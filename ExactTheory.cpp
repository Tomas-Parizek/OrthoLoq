#include "ExactTheory.hpp"

#include <algorithm>
#include <array>
#include <cstdlib>
#include <dlfcn.h>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace ql {
namespace {
struct ComplexExpr {
    std::string re;
    std::string im;
};

bool isZero(const std::string& x) {
    return x == "0";
}

bool isOne(const std::string& x) {
    return x == "1";
}

std::string neg(const std::string& x) {
    if (isZero(x)) return "0";
    if (!x.empty() && x.front() == '(' && x.rfind("(- ", 0) == 0 && x.back() == ')') {
        return x.substr(3, x.size() - 4);
    }
    return "(- " + x + ")";
}

std::string add(const std::string& a, const std::string& b) {
    if (isZero(a)) return b;
    if (isZero(b)) return a;
    return "(+ " + a + " " + b + ")";
}

std::string sub(const std::string& a, const std::string& b) {
    if (isZero(b)) return a;
    if (a == b) return "0";
    if (isZero(a)) return neg(b);
    return "(- " + a + " " + b + ")";
}

std::string mul(const std::string& a, const std::string& b) {
    if (isZero(a) || isZero(b)) return "0";
    if (isOne(a)) return b;
    if (isOne(b)) return a;
    if (a == "-1") return neg(b);
    if (b == "-1") return neg(a);
    return "(* " + a + " " + b + ")";
}

ComplexExpr cadd(const ComplexExpr& a, const ComplexExpr& b) {
    return {add(a.re, b.re), add(a.im, b.im)};
}

ComplexExpr csub(const ComplexExpr& a, const ComplexExpr& b) {
    return {sub(a.re, b.re), sub(a.im, b.im)};
}

ComplexExpr cmul(const ComplexExpr& a, const ComplexExpr& b) {
    return {
        sub(mul(a.re, b.re), mul(a.im, b.im)),
        add(mul(a.re, b.im), mul(a.im, b.re))
    };
}

ComplexExpr czero() {
    return {"0", "0"};
}

ComplexExpr cone() {
    return {"1", "0"};
}

std::string projectorReName(NodeId node, std::uint32_t i, std::uint32_t j) {
    if (i > j) std::swap(i, j);
    return "p_" + std::to_string(node) + "_" + std::to_string(i) + "_" +
           std::to_string(j) + "_re";
}

std::string projectorImName(NodeId node, std::uint32_t i, std::uint32_t j) {
    if (i == j) return "0";
    if (i < j) {
        return "p_" + std::to_string(node) + "_" + std::to_string(i) + "_" +
               std::to_string(j) + "_im";
    }
    return neg(projectorImName(node, j, i));
}

ComplexExpr projectorEntry(NodeId node, std::uint32_t i, std::uint32_t j) {
    return {projectorReName(node, i, j), projectorImName(node, i, j)};
}

std::string auxReName(NodeId gate, std::uint32_t i, std::uint32_t j) {
    return "x_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
           std::to_string(j) + "_re";
}

std::string auxImName(NodeId gate, std::uint32_t i, std::uint32_t j) {
    return "x_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
           std::to_string(j) + "_im";
}

ComplexExpr auxEntry(NodeId gate, std::uint32_t i, std::uint32_t j) {
    return {auxReName(gate, i, j), auxImName(gate, i, j)};
}

class Encoder {
public:
    Encoder(const Formula& formula, ExactTheoryStats& stats)
        : formula_(formula), stats_(stats), n_(formula.dimension()) {
        if (n_ == 0) {
            throw std::invalid_argument("exact theory requires positive Hilbert dimension");
        }
    }

    std::string encode() {
        stats_.realVariables = 0;
        stats_.polynomialEqualities = 0;
        stats_.polynomialInequalities = 0;
        stats_.smtBytes = 0;

        out_ << "; qlcir exact fixed-dimension BvN encoding\n"
             << "; orthogonal projectors + exact kernel encoding of meet\n"
             << "(set-logic QF_NRA)\n";

        declareProjectors();
        declareGateAuxiliaries();
        assertProjectors();
        assertGateSemantics();
        assertWeakOutput();
        out_ << "(check-sat)\n";

        std::string result = out_.str();
        stats_.smtBytes = result.size();
        return result;
    }

private:
    const Formula& formula_;
    ExactTheoryStats& stats_;
    std::uint32_t n_;
    std::ostringstream out_;
    std::vector<NodeId> projectorNodes_;

    void declareReal(const std::string& name) {
        out_ << "(declare-fun " << name << " () Real)\n";
        ++stats_.realVariables;
    }

    void assertZero(const std::string& expr) {
        if (isZero(expr)) return;
        out_ << "(assert (= " << expr << " 0))\n";
        ++stats_.polynomialEqualities;
    }

    void assertEqual(const ComplexExpr& lhs, const ComplexExpr& rhs) {
        assertZero(sub(lhs.re, rhs.re));
        assertZero(sub(lhs.im, rhs.im));
    }

    ComplexExpr literalEntry(Lit literal, std::uint32_t i, std::uint32_t j) const {
        const ComplexExpr identity = i == j ? cone() : czero();
        if (literal == TRUE_LIT) return identity;
        if (literal == FALSE_LIT) return czero();

        const NodeId node = literal < 0 ? -literal : literal;
        const ComplexExpr p = projectorEntry(node, i, j);
        return literal < 0 ? csub(identity, p) : p;
    }

    ComplexExpr sEntry(
        Lit lhs,
        Lit rhs,
        std::uint32_t i,
        std::uint32_t j
    ) const {
        const ComplexExpr twiceIdentity = i == j
            ? ComplexExpr{"2", "0"}
            : czero();
        return csub(csub(twiceIdentity, literalEntry(lhs, i, j)),
                    literalEntry(rhs, i, j));
    }

    ComplexExpr matrixProductProjectors(
        NodeId lhs,
        NodeId rhs,
        std::uint32_t i,
        std::uint32_t j
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t k = 0; k < n_; ++k) {
            sum = cadd(sum, cmul(
                projectorEntry(lhs, i, k),
                projectorEntry(rhs, k, j)
            ));
        }
        return sum;
    }

    ComplexExpr sTimesProjector(
        const AndGate& gate,
        std::uint32_t i,
        std::uint32_t j
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t k = 0; k < n_; ++k) {
            sum = cadd(sum, cmul(
                sEntry(gate.lhs, gate.rhs, i, k),
                projectorEntry(gate.out, k, j)
            ));
        }
        return sum;
    }

    ComplexExpr sTimesAux(
        const AndGate& gate,
        std::uint32_t i,
        std::uint32_t j
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t k = 0; k < n_; ++k) {
            sum = cadd(sum, cmul(
                sEntry(gate.lhs, gate.rhs, i, k),
                auxEntry(gate.out, k, j)
            ));
        }
        return sum;
    }

    void collectProjectorNodes() {
        std::unordered_set<NodeId> seen;
        for (const auto& [name, node] : formula_.variables()) {
            (void)name;
            if (seen.insert(node).second) projectorNodes_.push_back(node);
        }
        for (const AndGate& gate : formula_.gates()) {
            if (seen.insert(gate.out).second) projectorNodes_.push_back(gate.out);
        }
        std::sort(projectorNodes_.begin(), projectorNodes_.end());
    }

    void declareProjectors() {
        collectProjectorNodes();
        for (const NodeId node : projectorNodes_) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                declareReal(projectorReName(node, i, i));
                for (std::uint32_t j = i + 1; j < n_; ++j) {
                    declareReal(projectorReName(node, i, j));
                    declareReal(projectorImName(node, i, j));
                }
            }
        }
    }

    void declareGateAuxiliaries() {
        for (const AndGate& gate : formula_.gates()) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                for (std::uint32_t j = 0; j < n_; ++j) {
                    declareReal(auxReName(gate.out, i, j));
                    declareReal(auxImName(gate.out, i, j));
                }
            }
        }
    }

    void assertProjectors() {
        for (const NodeId node : projectorNodes_) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                for (std::uint32_t j = i; j < n_; ++j) {
                    const ComplexExpr square = matrixProductProjectors(
                        node, node, i, j
                    );
                    const ComplexExpr p = projectorEntry(node, i, j);
                    assertZero(sub(square.re, p.re));
                    if (i != j) {
                        assertZero(sub(square.im, p.im));
                    }
                }
            }
        }
    }

    void assertGateSemantics() {
        for (const AndGate& gate : formula_.gates()) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                for (std::uint32_t j = 0; j < n_; ++j) {
                    assertEqual(sTimesProjector(gate, i, j), czero());
                }
            }

            for (std::uint32_t i = 0; i < n_; ++i) {
                for (std::uint32_t j = 0; j < n_; ++j) {
                    const ComplexExpr rhs = csub(
                        i == j ? cone() : czero(),
                        projectorEntry(gate.out, i, j)
                    );
                    assertEqual(sTimesAux(gate, i, j), rhs);
                }
            }
        }
    }

    void assertWeakOutput() {
        const Lit output = formula_.output();
        if (output == FALSE_LIT) {
            out_ << "(assert false)\n";
            ++stats_.polynomialInequalities;
            return;
        }
        if (output == TRUE_LIT) {
            return;
        }

        const NodeId node = output < 0 ? -output : output;
        std::string trace = "0";
        for (std::uint32_t i = 0; i < n_; ++i) {
            trace = add(trace, projectorReName(node, i, i));
        }
        if (output < 0) {
            trace = sub(std::to_string(n_), trace);
        }

        out_ << "(assert (> " << trace << " 0))\n";
        ++stats_.polynomialInequalities;
    }
};

class WitnessEncoder {
public:
    WitnessEncoder(
        const Formula& formula,
        const AbstractWitness& witness,
        ExactTheoryStats& stats
    )
        : formula_(formula), witness_(witness), stats_(stats), n_(formula.dimension()) {
        validateWitness();
        buildPairs();
    }

    std::string encode() {
        stats_.realVariables = 0;
        stats_.polynomialEqualities = 0;
        stats_.polynomialInequalities = 0;
        stats_.smtBytes = 0;

        out_ << "; qlcir exact abstract-witness realizability encoding\n"
             << "; fixed-dimensional bases + exact complements + exact meets\n"
             << "(set-logic QF_NRA)\n";

        declareBases();
        declareRankWitnesses();
        declareGateCoefficients();
        assertFullRanks();
        assertComplements();
        assertGateSemantics();
        assertOutputNonzero();
        out_ << "(check-sat)\n";

        std::string result = out_.str();
        stats_.smtBytes = result.size();
        return result;
    }

private:
    struct PairInfo {
        ValueId root = UNASSIGNED_VALUE;
        ValueId complement = UNASSIGNED_VALUE;
        std::uint32_t rootDimension = 0;
        bool gaugeFixed = false;
    };

    struct RankMethod {
        bool charts = false;
        std::vector<std::vector<std::uint32_t>> pivotSets;
    };

    const Formula& formula_;
    const AbstractWitness& witness_;
    ExactTheoryStats& stats_;
    std::uint32_t n_;
    std::ostringstream out_;
    std::vector<PairInfo> pairs_;
    std::vector<std::int32_t> pairIndexByValue_;

    void validateWitness() const {
        if (n_ == 0 || witness_.hilbertDimension != n_) {
            throw std::invalid_argument("exact witness theory: dimension mismatch");
        }
        if (witness_.dimensions.size() != witness_.complements.size()) {
            throw std::invalid_argument("exact witness theory: malformed witness arrays");
        }
        if (witness_.dimensions.size() < 2 ||
            witness_.dimensions[static_cast<std::size_t>(BOTTOM_VALUE)] != 0 ||
            witness_.dimensions[static_cast<std::size_t>(TOP_VALUE)] !=
                static_cast<std::int32_t>(n_)) {
            throw std::invalid_argument("exact witness theory: missing 0/H values");
        }
        for (ValueId v = 0; v < static_cast<ValueId>(witness_.valueCount()); ++v) {
            const ValueId c = witness_.complements[static_cast<std::size_t>(v)];
            if (c < 0 || static_cast<std::size_t>(c) >= witness_.valueCount()) {
                throw std::invalid_argument("exact witness theory: invalid complement");
            }
            if (witness_.complements[static_cast<std::size_t>(c)] != v) {
                throw std::invalid_argument("exact witness theory: complement not involutive");
            }
            const std::int32_t dv = witness_.dimensions[static_cast<std::size_t>(v)];
            const std::int32_t dc = witness_.dimensions[static_cast<std::size_t>(c)];
            if (dv < 0 || dc < 0 || dv + dc != static_cast<std::int32_t>(n_)) {
                throw std::invalid_argument("exact witness theory: invalid complement dimensions");
            }
        }
    }

    void buildPairs() {
        pairIndexByValue_.assign(witness_.valueCount(), -1);
        bool gaugeChosen = false;
        for (ValueId v = 0; v < static_cast<ValueId>(witness_.valueCount()); ++v) {
            const std::int32_t dim = witness_.dimensions[static_cast<std::size_t>(v)];
            if (dim == 0 || dim == static_cast<std::int32_t>(n_)) continue;
            const ValueId c = witness_.complements[static_cast<std::size_t>(v)];
            if (v > c) continue;

            PairInfo info;
            info.root = v;
            info.complement = c;
            info.rootDimension = static_cast<std::uint32_t>(dim);
            info.gaugeFixed = !gaugeChosen;
            gaugeChosen = true;

            const std::int32_t index = static_cast<std::int32_t>(pairs_.size());
            pairs_.push_back(info);
            pairIndexByValue_[static_cast<std::size_t>(v)] = index;
            pairIndexByValue_[static_cast<std::size_t>(c)] = index;
        }
    }

    std::uint32_t dimension(ValueId value) const {
        return static_cast<std::uint32_t>(
            witness_.dimensions.at(static_cast<std::size_t>(value))
        );
    }

    ValueId complement(ValueId value) const {
        return witness_.complements.at(static_cast<std::size_t>(value));
    }

    const PairInfo& pairFor(ValueId value) const {
        const std::int32_t index = pairIndexByValue_.at(static_cast<std::size_t>(value));
        if (index < 0) {
            throw std::logic_error("exact witness theory: trivial value has no basis pair");
        }
        return pairs_.at(static_cast<std::size_t>(index));
    }

    std::string basisReName(ValueId value, std::uint32_t row, std::uint32_t col) const {
        return "b_" + std::to_string(value) + "_" + std::to_string(row) + "_" +
               std::to_string(col) + "_re";
    }

    std::string basisImName(ValueId value, std::uint32_t row, std::uint32_t col) const {
        return "b_" + std::to_string(value) + "_" + std::to_string(row) + "_" +
               std::to_string(col) + "_im";
    }

    std::string leftReName(ValueId value, std::uint32_t row, std::uint32_t col) const {
        return "l_" + std::to_string(value) + "_" + std::to_string(row) + "_" +
               std::to_string(col) + "_re";
    }

    std::string leftImName(ValueId value, std::uint32_t row, std::uint32_t col) const {
        return "l_" + std::to_string(value) + "_" + std::to_string(row) + "_" +
               std::to_string(col) + "_im";
    }

    std::string selectorName(ValueId value, std::size_t chart) const {
        return "sel_" + std::to_string(value) + "_" + std::to_string(chart);
    }

    std::string coeffReName(NodeId gate, std::uint32_t i, std::uint32_t j) const {
        return "c_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
               std::to_string(j) + "_re";
    }

    std::string coeffImName(NodeId gate, std::uint32_t i, std::uint32_t j) const {
        return "c_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
               std::to_string(j) + "_im";
    }

    void declareReal(const std::string& name) {
        out_ << "(declare-fun " << name << " () Real)\n";
        ++stats_.realVariables;
    }

    void declareBool(const std::string& name) {
        out_ << "(declare-fun " << name << " () Bool)\n";
    }

    void assertZero(const std::string& expr) {
        if (isZero(expr)) return;
        out_ << "(assert (= " << expr << " 0))\n";
        ++stats_.polynomialEqualities;
    }

    void assertZeroGuarded(const std::string& guard, const std::string& expr) {
        if (isZero(expr)) return;
        out_ << "(assert (=> " << guard << " (= " << expr << " 0)))\n";
        ++stats_.polynomialEqualities;
    }

    void assertEqual(const ComplexExpr& lhs, const ComplexExpr& rhs) {
        assertZero(sub(lhs.re, rhs.re));
        assertZero(sub(lhs.im, rhs.im));
    }

    ComplexExpr basisEntry(
        ValueId value,
        std::uint32_t row,
        std::uint32_t localColumn
    ) const {
        const std::uint32_t dim = dimension(value);
        if (localColumn >= dim) {
            throw std::out_of_range("exact witness theory: basis column out of range");
        }
        if (value == TOP_VALUE || dim == n_) {
            return row == localColumn ? cone() : czero();
        }
        if (value == BOTTOM_VALUE || dim == 0) {
            throw std::logic_error("exact witness theory: requested basis of zero space");
        }

        const PairInfo& pair = pairFor(value);
        if (pair.gaugeFixed) {
            std::uint32_t globalColumn = localColumn;
            if (value != pair.root) {
                globalColumn = pair.rootDimension + localColumn;
            }
            return row == globalColumn ? cone() : czero();
        }
        return {
            basisReName(value, row, localColumn),
            basisImName(value, row, localColumn)
        };
    }

    ComplexExpr leftEntry(
        ValueId value,
        std::uint32_t row,
        std::uint32_t column
    ) const {
        return {
            leftReName(value, row, column),
            leftImName(value, row, column)
        };
    }

    ComplexExpr coeffEntry(
        NodeId gate,
        std::uint32_t row,
        std::uint32_t column
    ) const {
        return {
            coeffReName(gate, row, column),
            coeffImName(gate, row, column)
        };
    }

    ComplexExpr conjugate(const ComplexExpr& x) const {
        return {x.re, neg(x.im)};
    }

    ComplexExpr innerProduct(
        ValueId lhs,
        std::uint32_t lhsColumn,
        ValueId rhs,
        std::uint32_t rhsColumn
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t row = 0; row < n_; ++row) {
            sum = cadd(sum, cmul(
                conjugate(basisEntry(lhs, row, lhsColumn)),
                basisEntry(rhs, row, rhsColumn)
            ));
        }
        return sum;
    }

    ValueId literalValue(Lit literal) const {
        if (literal == TRUE_LIT) return TOP_VALUE;
        if (literal == FALSE_LIT) return BOTTOM_VALUE;
        const NodeId node = literal < 0 ? -literal : literal;
        if (node < 0 || static_cast<std::size_t>(node) >= witness_.nodeValues.size()) {
            throw std::invalid_argument("exact witness theory: node value missing");
        }
        ValueId value = witness_.nodeValues[static_cast<std::size_t>(node)];
        if (value == UNASSIGNED_VALUE) {
            throw std::invalid_argument("exact witness theory: unassigned AIG node");
        }
        if (literal < 0) value = complement(value);
        return value;
    }

    static std::uint64_t binomialCapped(
        std::uint32_t n,
        std::uint32_t k,
        std::uint64_t cap
    ) {
        if (k > n) return 0;
        k = std::min(k, n - k);
        std::uint64_t result = 1;
        for (std::uint32_t i = 1; i <= k; ++i) {
            if (result > cap) return cap + 1;
            result = result * (n - k + i) / i;
            if (result > cap) return cap + 1;
        }
        return result;
    }

    static void generatePivotSetsRec(
        std::uint32_t n,
        std::uint32_t k,
        std::uint32_t next,
        std::vector<std::uint32_t>& current,
        std::vector<std::vector<std::uint32_t>>& out
    ) {
        if (current.size() == k) {
            out.push_back(current);
            return;
        }
        const std::uint32_t need = k - static_cast<std::uint32_t>(current.size());
        for (std::uint32_t i = next; i + need <= n; ++i) {
            current.push_back(i);
            generatePivotSetsRec(n, k, i + 1, current, out);
            current.pop_back();
        }
    }

    RankMethod rankMethod(ValueId value) const {
        RankMethod method;
        const std::uint32_t k = dimension(value);

        constexpr std::uint64_t MAX_CHARTS = 64;
        if (k > 0 && k < n_ && binomialCapped(n_, k, MAX_CHARTS) <= MAX_CHARTS) {
            method.charts = true;
            std::vector<std::uint32_t> current;
            generatePivotSetsRec(n_, k, 0, current, method.pivotSets);
        }
        return method;
    }

    void declareBases() {
        for (const PairInfo& pair : pairs_) {
            if (pair.gaugeFixed) continue;
            for (const ValueId value : {pair.root, pair.complement}) {
                const std::uint32_t k = dimension(value);
                for (std::uint32_t row = 0; row < n_; ++row) {
                    for (std::uint32_t col = 0; col < k; ++col) {
                        declareReal(basisReName(value, row, col));
                        declareReal(basisImName(value, row, col));
                    }
                }
            }
        }
    }

    void declareRankWitnesses() {
        for (const PairInfo& pair : pairs_) {
            if (pair.gaugeFixed) continue;
            for (const ValueId value : {pair.root, pair.complement}) {
                const std::uint32_t k = dimension(value);
                const RankMethod method = rankMethod(value);
                if (method.charts) {
                    for (std::size_t c = 0; c < method.pivotSets.size(); ++c) {
                        declareBool(selectorName(value, c));
                    }
                } else {
                    for (std::uint32_t row = 0; row < k; ++row) {
                        for (std::uint32_t col = 0; col < n_; ++col) {
                            declareReal(leftReName(value, row, col));
                            declareReal(leftImName(value, row, col));
                        }
                    }
                }
            }
        }
    }

    void declareGateCoefficients() {
        for (const AndGate& gate : formula_.gates()) {
            const ValueId a = literalValue(gate.lhs);
            const ValueId b = literalValue(gate.rhs);
            const ValueId g = literalValue(gate.out);
            const std::uint32_t sourceColumns =
                dimension(complement(a)) + dimension(complement(b));
            const std::uint32_t targetColumns = dimension(complement(g));
            for (std::uint32_t i = 0; i < sourceColumns; ++i) {
                for (std::uint32_t j = 0; j < targetColumns; ++j) {
                    declareReal(coeffReName(gate.out, i, j));
                    declareReal(coeffImName(gate.out, i, j));
                }
            }
        }
    }

    void assertFullRankCharts(ValueId value, const RankMethod& method) {
        out_ << "(assert (or";
        for (std::size_t c = 0; c < method.pivotSets.size(); ++c) {
            out_ << " " << selectorName(value, c);
        }
        out_ << "))\n";

        const std::uint32_t k = dimension(value);
        for (std::size_t c = 0; c < method.pivotSets.size(); ++c) {
            const std::string selector = selectorName(value, c);
            const auto& pivots = method.pivotSets[c];
            for (std::uint32_t i = 0; i < k; ++i) {
                for (std::uint32_t j = 0; j < k; ++j) {
                    const ComplexExpr entry = basisEntry(value, pivots[i], j);
                    const ComplexExpr rhs = i == j ? cone() : czero();
                    assertZeroGuarded(selector, sub(entry.re, rhs.re));
                    assertZeroGuarded(selector, sub(entry.im, rhs.im));
                }
            }
        }
    }

    void assertFullRankLeftInverse(ValueId value) {
        const std::uint32_t k = dimension(value);
        for (std::uint32_t i = 0; i < k; ++i) {
            for (std::uint32_t j = 0; j < k; ++j) {
                ComplexExpr product = czero();
                for (std::uint32_t row = 0; row < n_; ++row) {
                    product = cadd(product, cmul(
                        leftEntry(value, i, row),
                        basisEntry(value, row, j)
                    ));
                }
                assertEqual(product, i == j ? cone() : czero());
            }
        }
    }

    void assertFullRanks() {
        for (const PairInfo& pair : pairs_) {
            if (pair.gaugeFixed) continue;
            for (const ValueId value : {pair.root, pair.complement}) {
                const RankMethod method = rankMethod(value);
                if (method.charts) {
                    assertFullRankCharts(value, method);
                } else {
                    assertFullRankLeftInverse(value);
                }
            }
        }
    }

    void assertOrthogonal(ValueId lhs, ValueId rhs) {
        const std::uint32_t dl = dimension(lhs);
        const std::uint32_t dr = dimension(rhs);
        for (std::uint32_t i = 0; i < dl; ++i) {
            for (std::uint32_t j = 0; j < dr; ++j) {
                assertEqual(innerProduct(lhs, i, rhs, j), czero());
            }
        }
    }

    void assertComplements() {
        for (const PairInfo& pair : pairs_) {
            if (pair.gaugeFixed) continue;

            assertOrthogonal(pair.root, pair.complement);
        }
    }

    ComplexExpr sourceBasisEntry(
        ValueId aComplement,
        ValueId bComplement,
        std::uint32_t row,
        std::uint32_t sourceColumn
    ) const {
        const std::uint32_t da = dimension(aComplement);
        if (sourceColumn < da) {
            return basisEntry(aComplement, row, sourceColumn);
        }
        return basisEntry(bComplement, row, sourceColumn - da);
    }

    void assertContainedInSourceSpan(
        NodeId gate,
        ValueId target,
        ValueId aComplement,
        ValueId bComplement
    ) {
        const std::uint32_t sourceColumns =
            dimension(aComplement) + dimension(bComplement);
        const std::uint32_t targetColumns = dimension(target);

        for (std::uint32_t row = 0; row < n_; ++row) {
            for (std::uint32_t targetColumn = 0;
                 targetColumn < targetColumns;
                 ++targetColumn) {
                ComplexExpr combination = czero();
                for (std::uint32_t sourceColumn = 0;
                     sourceColumn < sourceColumns;
                     ++sourceColumn) {
                    combination = cadd(combination, cmul(
                        sourceBasisEntry(
                            aComplement,
                            bComplement,
                            row,
                            sourceColumn
                        ),
                        coeffEntry(gate, sourceColumn, targetColumn)
                    ));
                }
                assertEqual(
                    combination,
                    basisEntry(target, row, targetColumn)
                );
            }
        }
    }

    void assertGateSemantics() {
        for (const AndGate& gate : formula_.gates()) {
            const ValueId a = literalValue(gate.lhs);
            const ValueId b = literalValue(gate.rhs);
            const ValueId g = literalValue(gate.out);
            const ValueId aComplement = complement(a);
            const ValueId bComplement = complement(b);
            const ValueId gComplement = complement(g);

            assertOrthogonal(aComplement, g);
            assertOrthogonal(bComplement, g);

            assertContainedInSourceSpan(
                gate.out,
                gComplement,
                aComplement,
                bComplement
            );
        }
    }

    void assertOutputNonzero() {
        const ValueId output = literalValue(formula_.output());
        if (dimension(output) == 0) {
            out_ << "(assert false)\n";
            ++stats_.polynomialInequalities;
        }
    }
};

struct LitVectorKey {
    Lit literal = 0;
    std::size_t vector = 0;

    bool operator==(const LitVectorKey&) const = default;
};

struct LitVectorKeyHash {
    std::size_t operator()(const LitVectorKey& key) const noexcept {
        const std::size_t h1 = std::hash<Lit>{}(key.literal);
        const std::size_t h2 = std::hash<std::size_t>{}(key.vector);
        return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
    }
};

class MembershipEncoder {
public:
    MembershipEncoder(const Formula& formula, ExactTheoryStats& stats)
        : formula_(formula), stats_(stats), n_(formula.dimension()),
          gateByNode_(static_cast<std::size_t>(formula.maxNodeId()) + 1, nullptr) {
        if (n_ == 0) {
            throw std::invalid_argument(
                "exact membership theory requires positive Hilbert dimension"
            );
        }
        for (const auto& [name, node] : formula_.variables()) {
            (void)name;
            variableNodes_.insert(node);
        }
        for (const AndGate& gate : formula_.gates()) {
            gateByNode_.at(static_cast<std::size_t>(gate.out)) = &gate;
        }
    }

    std::string encode() {
        stats_.realVariables = 0;
        stats_.polynomialEqualities = 0;
        stats_.polynomialInequalities = 0;
        stats_.smtBytes = 0;
        nextVector_ = 0;
        expanded_.clear();

        out_.str({});
        out_.clear();
        out_ << "; qlcir compact exact weak-membership encoding\n"
             << "; input projectors + recursively constrained witness vectors\n"
             << "(set-logic QF_NRA)\n";

        declareVariableProjectors();
        assertVariableProjectors();

        const std::size_t root = newVector();
        assertMembership(formula_.output(), root);
        assertNonzero(root);
        out_ << "(check-sat)\n";

        std::string result = out_.str();
        stats_.smtBytes = result.size();
        return result;
    }

private:
    const Formula& formula_;
    ExactTheoryStats& stats_;
    std::uint32_t n_;
    std::ostringstream out_;
    std::unordered_set<NodeId> variableNodes_;
    std::vector<const AndGate*> gateByNode_;
    std::size_t nextVector_ = 0;
    std::unordered_set<LitVectorKey, LitVectorKeyHash> expanded_;

    bool isVariable(NodeId node) const {
        return variableNodes_.contains(node);
    }

    std::string vectorReName(std::size_t vector, std::uint32_t row) const {
        return "mv_" + std::to_string(vector) + "_" +
               std::to_string(row) + "_re";
    }

    std::string vectorImName(std::size_t vector, std::uint32_t row) const {
        return "mv_" + std::to_string(vector) + "_" +
               std::to_string(row) + "_im";
    }

    ComplexExpr vectorEntry(std::size_t vector, std::uint32_t row) const {
        return {vectorReName(vector, row), vectorImName(vector, row)};
    }

    void declareReal(const std::string& name) {
        out_ << "(declare-fun " << name << " () Real)\n";
        ++stats_.realVariables;
    }

    void assertZero(const std::string& expr) {
        if (isZero(expr)) return;
        out_ << "(assert (= " << expr << " 0))\n";
        ++stats_.polynomialEqualities;
    }

    void assertEqual(const ComplexExpr& lhs, const ComplexExpr& rhs) {
        assertZero(sub(lhs.re, rhs.re));
        assertZero(sub(lhs.im, rhs.im));
    }

    std::size_t newVector() {
        const std::size_t vector = nextVector_++;
        for (std::uint32_t i = 0; i < n_; ++i) {
            declareReal(vectorReName(vector, i));
            declareReal(vectorImName(vector, i));
        }
        return vector;
    }

    ComplexExpr projectorTimesVector(
        NodeId projector,
        std::size_t vector,
        std::uint32_t row
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t k = 0; k < n_; ++k) {
            sum = cadd(sum, cmul(
                projectorEntry(projector, row, k),
                vectorEntry(vector, k)
            ));
        }
        return sum;
    }

    ComplexExpr projectorSquaredEntry(
        NodeId projector,
        std::uint32_t i,
        std::uint32_t j
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t k = 0; k < n_; ++k) {
            sum = cadd(sum, cmul(
                projectorEntry(projector, i, k),
                projectorEntry(projector, k, j)
            ));
        }
        return sum;
    }

    void declareVariableProjectors() {
        std::vector<NodeId> nodes(variableNodes_.begin(), variableNodes_.end());
        std::sort(nodes.begin(), nodes.end());
        for (const NodeId node : nodes) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                declareReal(projectorReName(node, i, i));
                for (std::uint32_t j = i + 1; j < n_; ++j) {
                    declareReal(projectorReName(node, i, j));
                    declareReal(projectorImName(node, i, j));
                }
            }
        }
    }

    void assertVariableProjectors() {
        for (const NodeId node : variableNodes_) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                for (std::uint32_t j = i; j < n_; ++j) {
                    const ComplexExpr square = projectorSquaredEntry(node, i, j);
                    const ComplexExpr p = projectorEntry(node, i, j);
                    assertZero(sub(square.re, p.re));
                    if (i != j) assertZero(sub(square.im, p.im));
                }
            }
        }
    }

    void assertMembership(Lit literal, std::size_t vector) {
        if (!expanded_.insert({literal, vector}).second) return;

        if (literal == TRUE_LIT) return;
        if (literal == FALSE_LIT) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                assertEqual(vectorEntry(vector, i), czero());
            }
            return;
        }

        const NodeId node = static_cast<NodeId>(std::abs(literal));
        if (isVariable(node)) {
            for (std::uint32_t i = 0; i < n_; ++i) {
                const ComplexExpr pv = projectorTimesVector(node, vector, i);
                assertEqual(
                    pv,
                    literal > 0 ? vectorEntry(vector, i) : czero()
                );
            }
            return;
        }

        if (node < 0 || static_cast<std::size_t>(node) >= gateByNode_.size() ||
            gateByNode_[static_cast<std::size_t>(node)] == nullptr) {
            throw std::logic_error(
                "exact membership theory: AIG references unknown node"
            );
        }
        const AndGate& gate = *gateByNode_[static_cast<std::size_t>(node)];

        if (literal > 0) {
            assertMembership(gate.lhs, vector);
            assertMembership(gate.rhs, vector);
            return;
        }

        const std::size_t x = newVector();
        const std::size_t y = newVector();
        for (std::uint32_t i = 0; i < n_; ++i) {
            assertEqual(
                vectorEntry(vector, i),
                cadd(vectorEntry(x, i), vectorEntry(y, i))
            );
        }
        assertMembership(-gate.lhs, x);
        assertMembership(-gate.rhs, y);
    }

    void assertNonzero(std::size_t vector) {
        std::string norm = "0";
        for (std::uint32_t i = 0; i < n_; ++i) {
            const ComplexExpr v = vectorEntry(vector, i);
            norm = add(norm, add(mul(v.re, v.re), mul(v.im, v.im)));
        }
        out_ << "(assert (> " << norm << " 0))\n";
        ++stats_.polynomialInequalities;
    }
};

struct ChartPairLayout {
    ValueId root = UNASSIGNED_VALUE;
    ValueId complement = UNASSIGNED_VALUE;
    std::uint32_t rootDimension = 0;
    bool gaugeFixed = false;
};

void generatePivotSets(
    std::uint32_t n,
    std::uint32_t k,
    std::uint32_t next,
    std::vector<std::uint32_t>& current,
    std::vector<std::vector<std::uint32_t>>& out
) {
    if (current.size() == k) {
        out.push_back(current);
        return;
    }
    const std::uint32_t need = k - static_cast<std::uint32_t>(current.size());
    for (std::uint32_t i = next; i + need <= n; ++i) {
        current.push_back(i);
        generatePivotSets(n, k, i + 1, current, out);
        current.pop_back();
    }
}

std::vector<std::vector<std::uint32_t>> allPivotSets(
    std::uint32_t n,
    std::uint32_t k
) {
    std::vector<std::vector<std::uint32_t>> result;
    std::vector<std::uint32_t> current;
    generatePivotSets(n, k, 0, current, result);
    return result;
}

std::vector<ChartPairLayout> buildChartPairs(
    const AbstractWitness& witness,
    std::uint32_t n
) {
    std::vector<ChartPairLayout> result;
    bool gaugeChosen = false;
    for (ValueId v = 0; v < static_cast<ValueId>(witness.valueCount()); ++v) {
        const std::int32_t d = witness.dimensions.at(static_cast<std::size_t>(v));
        if (d == 0 || d == static_cast<std::int32_t>(n)) continue;
        const ValueId c = witness.complements.at(static_cast<std::size_t>(v));
        if (v > c) continue;
        result.push_back({
            v,
            c,
            static_cast<std::uint32_t>(d),
            !gaugeChosen
        });
        gaugeChosen = true;
    }
    return result;
}

class ChartWitnessEncoder {
public:
    ChartWitnessEncoder(
        const Formula& formula,
        const AbstractWitness& witness,
        std::vector<ChartPairLayout> pairs,
        std::vector<std::vector<std::uint32_t>> selectedPivots,
        ExactTheoryStats& stats
    )
        : formula_(formula),
          witness_(witness),
          pairs_(std::move(pairs)),
          selectedPivots_(std::move(selectedPivots)),
          stats_(stats),
          n_(formula.dimension()) {
        pairIndexByValue_.assign(witness_.valueCount(), -1);
        for (std::size_t i = 0; i < pairs_.size(); ++i) {
            pairIndexByValue_[static_cast<std::size_t>(pairs_[i].root)] =
                static_cast<std::int32_t>(i);
            pairIndexByValue_[static_cast<std::size_t>(pairs_[i].complement)] =
                static_cast<std::int32_t>(i);
        }
        if (selectedPivots_.size() != pairs_.size()) {
            throw std::invalid_argument("chart witness: pivot plan size mismatch");
        }
        for (std::size_t i = 0; i < pairs_.size(); ++i) {
            if (pairs_[i].gaugeFixed) continue;
            if (selectedPivots_[i].size() != pairs_[i].rootDimension) {
                throw std::invalid_argument("chart witness: invalid pivot count");
            }
        }
    }

    std::string encode() {
        stats_.realVariables = 0;
        stats_.polynomialEqualities = 0;
        stats_.polynomialInequalities = 0;
        stats_.smtBytes = 0;

        out_ << "; qlcir exact witness chart encoding\n"
             << "; one Grassmann chart per complementary pair\n"
             << "(set-logic QF_NRA)\n";
        declareChartCoordinates();
        declareGateCoefficients();
        assertGateSemantics();
        assertOutputNonzero();
        out_ << "(check-sat)\n";
        std::string text = out_.str();
        stats_.smtBytes = text.size();
        return text;
    }

private:
    const Formula& formula_;
    const AbstractWitness& witness_;
    std::vector<ChartPairLayout> pairs_;
    std::vector<std::vector<std::uint32_t>> selectedPivots_;
    ExactTheoryStats& stats_;
    std::uint32_t n_;
    std::vector<std::int32_t> pairIndexByValue_;
    std::ostringstream out_;

    std::uint32_t dimension(ValueId v) const {
        return static_cast<std::uint32_t>(
            witness_.dimensions.at(static_cast<std::size_t>(v))
        );
    }

    ValueId complement(ValueId v) const {
        return witness_.complements.at(static_cast<std::size_t>(v));
    }

    const ChartPairLayout& pairFor(ValueId value) const {
        const auto index = pairIndexByValue_.at(static_cast<std::size_t>(value));
        if (index < 0) throw std::logic_error("chart witness: trivial value has no pair");
        return pairs_.at(static_cast<std::size_t>(index));
    }

    std::size_t pairIndex(ValueId value) const {
        const auto index = pairIndexByValue_.at(static_cast<std::size_t>(value));
        if (index < 0) throw std::logic_error("chart witness: trivial value has no pair");
        return static_cast<std::size_t>(index);
    }

    std::string xReName(
        ValueId root,
        std::uint32_t nonPivotRow,
        std::uint32_t column
    ) const {
        return "gx_" + std::to_string(root) + "_" +
               std::to_string(nonPivotRow) + "_" + std::to_string(column) + "_re";
    }

    std::string xImName(
        ValueId root,
        std::uint32_t nonPivotRow,
        std::uint32_t column
    ) const {
        return "gx_" + std::to_string(root) + "_" +
               std::to_string(nonPivotRow) + "_" + std::to_string(column) + "_im";
    }

    std::string coeffReName(NodeId gate, std::uint32_t i, std::uint32_t j) const {
        return "gc_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
               std::to_string(j) + "_re";
    }

    std::string coeffImName(NodeId gate, std::uint32_t i, std::uint32_t j) const {
        return "gc_" + std::to_string(gate) + "_" + std::to_string(i) + "_" +
               std::to_string(j) + "_im";
    }

    void declareReal(const std::string& name) {
        out_ << "(declare-fun " << name << " () Real)\n";
        ++stats_.realVariables;
    }

    void assertZero(const std::string& expr) {
        if (isZero(expr)) return;
        out_ << "(assert (= " << expr << " 0))\n";
        ++stats_.polynomialEqualities;
    }

    void assertEqual(const ComplexExpr& lhs, const ComplexExpr& rhs) {
        assertZero(sub(lhs.re, rhs.re));
        assertZero(sub(lhs.im, rhs.im));
    }

    std::vector<std::uint32_t> nonPivotRows(std::size_t pairIdx) const {
        const ChartPairLayout& pair = pairs_.at(pairIdx);
        if (pair.gaugeFixed) {
            std::vector<std::uint32_t> result;
            for (std::uint32_t r = pair.rootDimension; r < n_; ++r) {
                result.push_back(r);
            }
            return result;
        }
        const auto& pivots = selectedPivots_.at(pairIdx);
        std::vector<bool> isPivot(n_, false);
        for (std::uint32_t p : pivots) isPivot[p] = true;
        std::vector<std::uint32_t> result;
        for (std::uint32_t r = 0; r < n_; ++r) {
            if (!isPivot[r]) result.push_back(r);
        }
        return result;
    }

    std::vector<std::uint32_t> pivotRows(std::size_t pairIdx) const {
        const ChartPairLayout& pair = pairs_.at(pairIdx);
        if (pair.gaugeFixed) {
            std::vector<std::uint32_t> result;
            for (std::uint32_t r = 0; r < pair.rootDimension; ++r) {
                result.push_back(r);
            }
            return result;
        }
        return selectedPivots_.at(pairIdx);
    }

    int positionOf(
        const std::vector<std::uint32_t>& rows,
        std::uint32_t row
    ) const {
        const auto it = std::find(rows.begin(), rows.end(), row);
        if (it == rows.end()) return -1;
        return static_cast<int>(std::distance(rows.begin(), it));
    }

    ComplexExpr chartX(
        const ChartPairLayout& pair,
        std::uint32_t nonPivotIndex,
        std::uint32_t rootColumn
    ) const {
        if (pair.gaugeFixed) return czero();
        return {
            xReName(pair.root, nonPivotIndex, rootColumn),
            xImName(pair.root, nonPivotIndex, rootColumn)
        };
    }

    ComplexExpr basisEntry(
        ValueId value,
        std::uint32_t row,
        std::uint32_t localColumn
    ) const {
        const std::uint32_t d = dimension(value);
        if (localColumn >= d) throw std::out_of_range("chart witness basis column");
        if (value == TOP_VALUE || d == n_) {
            return row == localColumn ? cone() : czero();
        }
        if (value == BOTTOM_VALUE || d == 0) {
            throw std::logic_error("chart witness requested zero-space basis");
        }

        const std::size_t pi = pairIndex(value);
        const ChartPairLayout& pair = pairs_[pi];
        const auto pivots = pivotRows(pi);
        const auto nonPivots = nonPivotRows(pi);

        if (value == pair.root) {
            const int p = positionOf(pivots, row);
            if (p >= 0) {
                return static_cast<std::uint32_t>(p) == localColumn ? cone() : czero();
            }
            const int np = positionOf(nonPivots, row);
            if (np < 0) throw std::logic_error("chart witness row partition failure");
            return chartX(pair, static_cast<std::uint32_t>(np), localColumn);
        }

        const int p = positionOf(pivots, row);
        if (p >= 0) {
            ComplexExpr x = chartX(
                pair,
                localColumn,
                static_cast<std::uint32_t>(p)
            );
            return {neg(x.re), x.im};
        }
        const int np = positionOf(nonPivots, row);
        if (np < 0) throw std::logic_error("chart witness row partition failure");
        return static_cast<std::uint32_t>(np) == localColumn ? cone() : czero();
    }

    ComplexExpr coeffEntry(
        NodeId gate,
        std::uint32_t row,
        std::uint32_t column
    ) const {
        return {
            coeffReName(gate, row, column),
            coeffImName(gate, row, column)
        };
    }

    ComplexExpr conjugate(const ComplexExpr& x) const {
        return {x.re, neg(x.im)};
    }

    ComplexExpr innerProduct(
        ValueId lhs,
        std::uint32_t lhsColumn,
        ValueId rhs,
        std::uint32_t rhsColumn
    ) const {
        ComplexExpr sum = czero();
        for (std::uint32_t row = 0; row < n_; ++row) {
            sum = cadd(sum, cmul(
                conjugate(basisEntry(lhs, row, lhsColumn)),
                basisEntry(rhs, row, rhsColumn)
            ));
        }
        return sum;
    }

    ValueId literalValue(Lit literal) const {
        if (literal == TRUE_LIT) return TOP_VALUE;
        if (literal == FALSE_LIT) return BOTTOM_VALUE;
        const NodeId node = literal < 0 ? -literal : literal;
        ValueId value = witness_.nodeValues.at(static_cast<std::size_t>(node));
        if (value == UNASSIGNED_VALUE) {
            throw std::invalid_argument("chart witness: missing node value");
        }
        if (literal < 0) value = complement(value);
        return value;
    }

    void declareChartCoordinates() {
        for (std::size_t i = 0; i < pairs_.size(); ++i) {
            const auto& pair = pairs_[i];
            if (pair.gaugeFixed) continue;
            const std::uint32_t k = pair.rootDimension;
            const std::uint32_t nk = n_ - k;
            for (std::uint32_t r = 0; r < nk; ++r) {
                for (std::uint32_t c = 0; c < k; ++c) {
                    declareReal(xReName(pair.root, r, c));
                    declareReal(xImName(pair.root, r, c));
                }
            }
        }
    }

    void declareGateCoefficients() {
        for (const AndGate& gate : formula_.gates()) {
            const ValueId a = literalValue(gate.lhs);
            const ValueId b = literalValue(gate.rhs);
            const ValueId g = literalValue(gate.out);
            const std::uint32_t sourceColumns =
                dimension(complement(a)) + dimension(complement(b));
            const std::uint32_t targetColumns = dimension(complement(g));
            for (std::uint32_t i = 0; i < sourceColumns; ++i) {
                for (std::uint32_t j = 0; j < targetColumns; ++j) {
                    declareReal(coeffReName(gate.out, i, j));
                    declareReal(coeffImName(gate.out, i, j));
                }
            }
        }
    }

    void assertOrthogonal(ValueId lhs, ValueId rhs) {
        for (std::uint32_t i = 0; i < dimension(lhs); ++i) {
            for (std::uint32_t j = 0; j < dimension(rhs); ++j) {
                assertEqual(innerProduct(lhs, i, rhs, j), czero());
            }
        }
    }

    ComplexExpr sourceBasisEntry(
        ValueId aComplement,
        ValueId bComplement,
        std::uint32_t row,
        std::uint32_t sourceColumn
    ) const {
        const std::uint32_t da = dimension(aComplement);
        if (sourceColumn < da) {
            return basisEntry(aComplement, row, sourceColumn);
        }
        return basisEntry(bComplement, row, sourceColumn - da);
    }

    void assertContainedInSourceSpan(
        NodeId gate,
        ValueId target,
        ValueId aComplement,
        ValueId bComplement
    ) {
        const std::uint32_t sourceColumns =
            dimension(aComplement) + dimension(bComplement);
        const std::uint32_t targetColumns = dimension(target);
        for (std::uint32_t row = 0; row < n_; ++row) {
            for (std::uint32_t tc = 0; tc < targetColumns; ++tc) {
                ComplexExpr sum = czero();
                for (std::uint32_t sc = 0; sc < sourceColumns; ++sc) {
                    sum = cadd(sum, cmul(
                        sourceBasisEntry(aComplement, bComplement, row, sc),
                        coeffEntry(gate, sc, tc)
                    ));
                }
                assertEqual(sum, basisEntry(target, row, tc));
            }
        }
    }

    void assertGateSemantics() {
        for (const AndGate& gate : formula_.gates()) {
            const ValueId a = literalValue(gate.lhs);
            const ValueId b = literalValue(gate.rhs);
            const ValueId g = literalValue(gate.out);
            const ValueId ac = complement(a);
            const ValueId bc = complement(b);
            const ValueId gc = complement(g);
            assertOrthogonal(ac, g);
            assertOrthogonal(bc, g);
            assertContainedInSourceSpan(gate.out, gc, ac, bc);
        }
    }

    void assertOutputNonzero() {
        if (dimension(literalValue(formula_.output())) == 0) {
            out_ << "(assert false)\n";
            ++stats_.polynomialInequalities;
        }
    }
};

struct Z3Api {
    using Config = void*;
    using Context = void*;
    using MkConfig = Config (*)();
    using DelConfig = void (*)(Config);
    using MkContext = Context (*)(Config);
    using DelContext = void (*)(Context);
    using EvalSmt2 = const char* (*)(Context, const char*);

    void* handle = nullptr;
    MkConfig mkConfig = nullptr;
    DelConfig delConfig = nullptr;
    MkContext mkContext = nullptr;
    DelContext delContext = nullptr;
    EvalSmt2 evalSmt2 = nullptr;
    std::string loadedName;

    ~Z3Api() {
        if (handle != nullptr) dlclose(handle);
    }

    Z3Api(const Z3Api&) = delete;
    Z3Api& operator=(const Z3Api&) = delete;
    Z3Api() = default;
    Z3Api(Z3Api&& other) noexcept {
        *this = std::move(other);
    }
    Z3Api& operator=(Z3Api&& other) noexcept {
        if (this == &other) return *this;
        if (handle != nullptr) dlclose(handle);
        handle = other.handle;
        mkConfig = other.mkConfig;
        delConfig = other.delConfig;
        mkContext = other.mkContext;
        delContext = other.delContext;
        evalSmt2 = other.evalSmt2;
        loadedName = std::move(other.loadedName);
        other.handle = nullptr;
        return *this;
    }
};

template <typename T>
T loadSymbol(void* handle, const char* name) {
    dlerror();
    void* symbol = dlsym(handle, name);
    const char* error = dlerror();
    if (error != nullptr || symbol == nullptr) {
        throw std::runtime_error(
            std::string("missing Z3 symbol ") + name +
            (error != nullptr ? std::string(": ") + error : std::string{})
        );
    }
    return reinterpret_cast<T>(symbol);
}

Z3Api loadZ3Impl() {
    std::vector<std::string> candidates;
    if (const char* configured = std::getenv("QLCIR_Z3_LIBRARY")) {
        if (*configured != '\0') candidates.emplace_back(configured);
    }
    candidates.emplace_back("libz3.so");
    candidates.emplace_back("libz3.so.4");
    candidates.emplace_back("libz3.dylib");

    std::string errors;
    for (const std::string& candidate : candidates) {
        void* handle = dlopen(candidate.c_str(), RTLD_NOW | RTLD_LOCAL);
        if (handle == nullptr) {
            if (const char* e = dlerror()) {
                if (!errors.empty()) errors += "; ";
                errors += candidate + ": " + e;
            }
            continue;
        }

        try {
            Z3Api api;
            api.handle = handle;
            api.loadedName = candidate;
            api.mkConfig = loadSymbol<Z3Api::MkConfig>(handle, "Z3_mk_config");
            api.delConfig = loadSymbol<Z3Api::DelConfig>(handle, "Z3_del_config");
            api.mkContext = loadSymbol<Z3Api::MkContext>(handle, "Z3_mk_context");
            api.delContext = loadSymbol<Z3Api::DelContext>(handle, "Z3_del_context");
            api.evalSmt2 = loadSymbol<Z3Api::EvalSmt2>(
                handle, "Z3_eval_smtlib2_string"
            );
            return api;
        } catch (...) {
            dlclose(handle);
            throw;
        }
    }

    throw std::runtime_error(
        "exact theory fallback requires the Z3 runtime library (libz3). "
        "Install libz3 or set QLCIR_Z3_LIBRARY to its path. Loader errors: " +
        errors
    );
}

std::string trim(std::string value) {
    const auto first = value.find_first_not_of(" \t\r\n");
    if (first == std::string::npos) return {};
    const auto last = value.find_last_not_of(" \t\r\n");
    return value.substr(first, last - first + 1);
}

ExactTheoryResult runZ3(
    const std::string& smt,
    ExactTheoryStats& stats
) {
    static Z3Api api = loadZ3Impl();
    stats.backend = "Z3 via " + api.loadedName;
    ++stats.backendCalls;

    Z3Api::Config config = api.mkConfig();
    if (config == nullptr) {
        throw std::runtime_error("Z3_mk_config failed");
    }
    Z3Api::Context context = api.mkContext(config);
    if (context == nullptr) {
        api.delConfig(config);
        throw std::runtime_error("Z3_mk_context failed");
    }

    const char* raw = api.evalSmt2(context, smt.c_str());
    const std::string answer = raw == nullptr ? std::string{} : trim(raw);

    api.delContext(context);
    api.delConfig(config);

    if (answer == "sat") return ExactTheoryResult::Sat;
    if (answer == "unsat") return ExactTheoryResult::Unsat;
    if (answer == "unknown") {
        throw std::runtime_error(
            "Z3 returned UNKNOWN for the exact QF_NRA fallback; completeness "
            "cannot be claimed for this run"
        );
    }
    throw std::runtime_error(
        "unexpected response from exact Z3 backend: " +
        (answer.empty() ? std::string("<empty>") : answer)
    );
}
}

ExactTheorySolver::ExactTheorySolver(const Formula& formula)
    : formula_(formula) {}

std::string ExactTheorySolver::encodeSmt2() {
    Encoder encoder(formula_, stats_);
    return encoder.encode();
}

ExactTheoryResult ExactTheorySolver::solve() {
    const std::string smt = encodeSmt2();
    return runZ3(smt, stats_);
}

const ExactTheoryStats& ExactTheorySolver::stats() const noexcept {
    return stats_;
}

ExactMembershipTheorySolver::ExactMembershipTheorySolver(const Formula& formula)
    : formula_(formula) {}

std::string ExactMembershipTheorySolver::encodeSmt2() {
    MembershipEncoder encoder(formula_, stats_);
    return encoder.encode();
}

ExactTheoryResult ExactMembershipTheorySolver::solve() {
    const std::string smt = encodeSmt2();
    return runZ3(smt, stats_);
}

const ExactTheoryStats& ExactMembershipTheorySolver::stats() const noexcept {
    return stats_;
}

ExactWitnessTheorySolver::ExactWitnessTheorySolver(
    const Formula& formula,
    const AbstractWitness& witness
)
    : formula_(formula), witness_(witness) {}

std::string ExactWitnessTheorySolver::encodeSmt2() {
    WitnessEncoder encoder(formula_, witness_, stats_);
    return encoder.encode();
}

ExactTheoryResult ExactWitnessTheorySolver::solve() {
    const std::uint32_t n = formula_.dimension();
    const std::vector<ChartPairLayout> pairs = buildChartPairs(witness_, n);

    constexpr std::uint64_t MAX_CHART_PRODUCT = 4096;
    std::vector<std::vector<std::vector<std::uint32_t>>> options(pairs.size());
    std::uint64_t product = 1;
    bool chartEnumeration = true;
    for (std::size_t i = 0; i < pairs.size(); ++i) {
        if (pairs[i].gaugeFixed) {
            options[i].push_back({});
            continue;
        }
        options[i] = allPivotSets(n, pairs[i].rootDimension);
        if (options[i].empty() || product > MAX_CHART_PRODUCT / options[i].size()) {
            chartEnumeration = false;
            break;
        }
        product *= options[i].size();
    }

    if (chartEnumeration) {
        std::vector<std::vector<std::uint32_t>> plan(pairs.size());
        bool foundSat = false;
        std::function<void(std::size_t)> visit = [&](std::size_t index) {
            if (foundSat) return;
            if (index == pairs.size()) {
                ExactTheoryStats one;
                ChartWitnessEncoder encoder(
                    formula_, witness_, pairs, plan, one
                );
                const std::string smt = encoder.encode();
                const ExactTheoryResult result = runZ3(smt, one);
                stats_.backend = one.backend;
                stats_.backendCalls += one.backendCalls;
                stats_.realVariables += one.realVariables;
                stats_.polynomialEqualities += one.polynomialEqualities;
                stats_.polynomialInequalities += one.polynomialInequalities;
                stats_.smtBytes += one.smtBytes;
                if (result == ExactTheoryResult::Sat) foundSat = true;
                return;
            }
            for (const auto& pivots : options[index]) {
                plan[index] = pivots;
                visit(index + 1);
                if (foundSat) return;
            }
        };
        visit(0);
        return foundSat ? ExactTheoryResult::Sat : ExactTheoryResult::Unsat;
    }

    const std::string smt = encodeSmt2();
    return runZ3(smt, stats_);
}

const ExactTheoryStats& ExactWitnessTheorySolver::stats() const noexcept {
    return stats_;
}

const char* toString(ExactTheoryResult result) noexcept {
    switch (result) {
        case ExactTheoryResult::Sat:
            return "SAT";
        case ExactTheoryResult::Unsat:
            return "UNSAT";
    }
    return "UNSAT";
}
}
