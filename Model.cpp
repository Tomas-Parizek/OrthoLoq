#include "Model.hpp"
#include "LatticeCertificate.hpp"

#include <algorithm>
#include <iomanip>
#include <sstream>
#include <stdexcept>

namespace ql {
namespace {
bool isZero(const Rational& value) {
    return value.numerator() == 0;
}

std::string rationalToString(const Rational& value) {
    std::ostringstream out;
    out << value.numerator();
    if (value.denominator() != 1) {
        out << '/' << value.denominator();
    }
    return out.str();
}
}

Realizer::Realizer(
    const Formula& formula,
    const AbstractWitness& witness
)
    : formula_(formula), witness_(witness) {}

std::optional<ConcreteModel> Realizer::realize() const {
    if (witness_.hilbertDimension != formula_.dimension() ||
        witness_.valueCount() < 2 ||
        witness_.complements.size() != witness_.valueCount() ||
        witness_.relations.size() != witness_.valueCount() * witness_.valueCount()) {
        return std::nullopt;
    }

    const auto spaces = realizeWitnessValues();
    if (!spaces || !verifyWitness(*spaces)) {
        return std::nullopt;
    }

    return buildModel(*spaces);
}

std::optional<std::vector<Realizer::Subspace>>
Realizer::realizeWitnessValues() const {
    const std::size_t n = witness_.hilbertDimension;
    const std::size_t count = witness_.valueCount();

    std::vector<Subspace> spaces(count, zero(n));
    std::vector<bool> assigned(count, false);

    spaces[BOTTOM_VALUE] = zero(n);
    spaces[TOP_VALUE] = whole(n);
    assigned[BOTTOM_VALUE] = true;
    assigned[TOP_VALUE] = true;

    if (witness_.dimensions[BOTTOM_VALUE] != 0 ||
        witness_.dimensions[TOP_VALUE] != static_cast<std::int32_t>(n) ||
        witness_.complements[BOTTOM_VALUE] != TOP_VALUE ||
        witness_.complements[TOP_VALUE] != BOTTOM_VALUE) {
        return std::nullopt;
    }

    if (n >= 3 && n <= 6 && count > 4) {
        const auto certificate =
            LatticeCertificate::supportCertificate(formula_, witness_);
        if (!certificate) {
            return std::nullopt;
        }

        std::size_t ordinal = 1;
        for (std::size_t i = 0; i < certificate->lineValues.size(); ++i) {
            const ValueId line = certificate->lineValues[i];
            const ValueId plane =
                witness_.complements[static_cast<std::size_t>(line)];
            const std::uint64_t mask = certificate->supportMasks[i];

            std::vector<Rational> row(n, Rational(0));
            const BigInt t = static_cast<unsigned long long>(ordinal + 1);
            BigInt power = 1;
            for (std::size_t coordinate = 0; coordinate < n; ++coordinate) {
                if ((mask & (std::uint64_t{1} << coordinate)) != 0) {
                    row[coordinate] = Rational(power);
                }
                power *= t;
            }

            Subspace lineSpace = fromRows({std::move(row)}, n);
            Subspace planeSpace = orthogonalComplement(lineSpace, n);

            spaces[static_cast<std::size_t>(line)] = std::move(lineSpace);
            spaces[static_cast<std::size_t>(plane)] = std::move(planeSpace);
            assigned[static_cast<std::size_t>(line)] = true;
            assigned[static_cast<std::size_t>(plane)] = true;
            ++ordinal;
        }

        if (std::all_of(assigned.begin(), assigned.end(), [](bool x) { return x; })) {
            return spaces;
        }
        return std::nullopt;
    }

    if (n > 2 && count > 4) {
        return std::nullopt;
    }

    std::size_t pairOrdinal = 1;

    for (ValueId value = 2; value < static_cast<ValueId>(count); ++value) {
        if (assigned[static_cast<std::size_t>(value)]) {
            continue;
        }

        const ValueId complement = witness_.complements[static_cast<std::size_t>(value)];
        if (complement < 2 || static_cast<std::size_t>(complement) >= count ||
            witness_.complements[static_cast<std::size_t>(complement)] != value) {
            return std::nullopt;
        }

        const std::int32_t d = witness_.dimensions[static_cast<std::size_t>(value)];
        const std::int32_t cd = witness_.dimensions[static_cast<std::size_t>(complement)];
        if (d <= 0 || cd <= 0 || d + cd != static_cast<std::int32_t>(n)) {
            return std::nullopt;
        }

        if (n == 2) {
            if (d != 1 || cd != 1) {
                return std::nullopt;
            }

            const Rational t{BigInt(pairOrdinal)};
            Subspace first = fromRows({{Rational(1), t}}, n);
            Subspace second = fromRows({{-t, Rational(1)}}, n);

            spaces[static_cast<std::size_t>(value)] = std::move(first);
            spaces[static_cast<std::size_t>(complement)] = std::move(second);
            assigned[static_cast<std::size_t>(value)] = true;
            assigned[static_cast<std::size_t>(complement)] = true;
            ++pairOrdinal;
            continue;
        }

        ExactMatrix firstRows;
        ExactMatrix secondRows;
        firstRows.reserve(static_cast<std::size_t>(d));
        secondRows.reserve(static_cast<std::size_t>(cd));

        for (std::int32_t i = 0; i < d; ++i) {
            std::vector<Rational> row(n, Rational(0));
            row[static_cast<std::size_t>(i)] = Rational(1);
            firstRows.push_back(std::move(row));
        }
        for (std::int32_t i = d; i < static_cast<std::int32_t>(n); ++i) {
            std::vector<Rational> row(n, Rational(0));
            row[static_cast<std::size_t>(i)] = Rational(1);
            secondRows.push_back(std::move(row));
        }

        spaces[static_cast<std::size_t>(value)] = fromRows(std::move(firstRows), n);
        spaces[static_cast<std::size_t>(complement)] = fromRows(std::move(secondRows), n);
        assigned[static_cast<std::size_t>(value)] = true;
        assigned[static_cast<std::size_t>(complement)] = true;
        ++pairOrdinal;
    }

    return spaces;
}

bool Realizer::verifyWitness(const std::vector<Subspace>& spaces) const {
    const std::size_t n = witness_.hilbertDimension;
    const std::size_t count = witness_.valueCount();

    if (spaces.size() != count) {
        return false;
    }

    for (ValueId value = 0; value < static_cast<ValueId>(count); ++value) {
        if (static_cast<std::int32_t>(dimension(spaces[static_cast<std::size_t>(value)])) !=
            witness_.dimensions[static_cast<std::size_t>(value)]) {
            return false;
        }

        const ValueId complement = witness_.complements[static_cast<std::size_t>(value)];
        if (complement < 0 || static_cast<std::size_t>(complement) >= count) {
            return false;
        }

        if (!equal(
                orthogonalComplement(spaces[static_cast<std::size_t>(value)], n),
                spaces[static_cast<std::size_t>(complement)])) {
            return false;
        }
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            const bool lhsBelow = isSubspaceOf(
                spaces[static_cast<std::size_t>(lhs)],
                spaces[static_cast<std::size_t>(rhs)]
            );
            const bool rhsBelow = isSubspaceOf(
                spaces[static_cast<std::size_t>(rhs)],
                spaces[static_cast<std::size_t>(lhs)]
            );

            switch (witness_.relation(lhs, rhs)) {
                case Relation::Below:
                    if (!lhsBelow || rhsBelow) return false;
                    break;
                case Relation::Above:
                    if (!rhsBelow || lhsBelow) return false;
                    break;
                case Relation::Incomparable:
                    if (lhsBelow || rhsBelow) return false;
                    break;
                case Relation::Undefined:
                    return false;
            }
        }
    }

    std::vector<Subspace> concreteNodes(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1,
        zero(n)
    );
    std::vector<bool> nodeAssigned(concreteNodes.size(), false);

    for (const auto& [name, node] : formula_.variables()) {
        (void)name;
        const std::size_t index = static_cast<std::size_t>(node);
        if (index >= witness_.nodeValues.size()) {
            return false;
        }
        const ValueId value = witness_.nodeValues[index];
        if (value < 0 || static_cast<std::size_t>(value) >= count) {
            return false;
        }
        concreteNodes[index] = spaces[static_cast<std::size_t>(value)];
        nodeAssigned[index] = true;
    }

    const auto literalSpace = [&](Lit lit) -> std::optional<Subspace> {
        if (lit == TRUE_LIT) return whole(n);
        if (lit == FALSE_LIT) return zero(n);
        const NodeId node = lit < 0 ? -lit : lit;
        const std::size_t index = static_cast<std::size_t>(node);
        if (index >= concreteNodes.size() || !nodeAssigned[index]) {
            return std::nullopt;
        }
        if (lit < 0) {
            return orthogonalComplement(concreteNodes[index], n);
        }
        return concreteNodes[index];
    };

    for (const AndGate& gate : formula_.gates()) {
        const auto lhs = literalSpace(gate.lhs);
        const auto rhs = literalSpace(gate.rhs);
        if (!lhs || !rhs) {
            return false;
        }
        Subspace result = meet(*lhs, *rhs, n);
        const std::size_t out = static_cast<std::size_t>(gate.out);
        concreteNodes[out] = result;
        nodeAssigned[out] = true;

        if (out < witness_.nodeValues.size()) {
            const ValueId abstract = witness_.nodeValues[out];
            if (abstract != UNASSIGNED_VALUE) {
                if (abstract < 0 || static_cast<std::size_t>(abstract) >= count ||
                    !equal(result, spaces[static_cast<std::size_t>(abstract)])) {
                    return false;
                }
            }
        }
    }

    auto output = literalSpace(formula_.output());
    return output && dimension(*output) > 0;
}

std::optional<ConcreteModel> Realizer::buildModel(
    const std::vector<Subspace>& spaces
) const {
    const std::size_t n = witness_.hilbertDimension;

    ConcreteModel model;
    model.hilbertDimension = witness_.hilbertDimension;

    std::vector<std::pair<std::string, NodeId>> variables;
    variables.reserve(formula_.variables().size());
    for (const auto& [name, node] : formula_.variables()) {
        variables.push_back({name, node});
    }
    std::sort(
        variables.begin(),
        variables.end(),
        [](const auto& lhs, const auto& rhs) { return lhs.second < rhs.second; }
    );

    for (const auto& [name, node] : variables) {
        const std::size_t index = static_cast<std::size_t>(node);
        if (index >= witness_.nodeValues.size()) {
            return std::nullopt;
        }
        const ValueId value = witness_.nodeValues[index];
        if (value < 0 || static_cast<std::size_t>(value) >= spaces.size()) {
            return std::nullopt;
        }
        const Subspace& subspace = spaces[static_cast<std::size_t>(value)];
        model.variables.push_back({
            name,
            subspace.basis,
            projector(subspace, n)
        });
    }

    std::vector<Subspace> nodes(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1,
        zero(n)
    );
    std::vector<bool> assigned(nodes.size(), false);
    for (const auto& [name, node] : variables) {
        (void)name;
        const ValueId value = witness_.nodeValues[static_cast<std::size_t>(node)];
        nodes[static_cast<std::size_t>(node)] = spaces[static_cast<std::size_t>(value)];
        assigned[static_cast<std::size_t>(node)] = true;
    }

    const auto literalSpace = [&](Lit lit) -> std::optional<Subspace> {
        if (lit == TRUE_LIT) return whole(n);
        if (lit == FALSE_LIT) return zero(n);
        const NodeId node = lit < 0 ? -lit : lit;
        const std::size_t index = static_cast<std::size_t>(node);
        if (index >= nodes.size() || !assigned[index]) return std::nullopt;
        return lit < 0
            ? std::optional<Subspace>(orthogonalComplement(nodes[index], n))
            : std::optional<Subspace>(nodes[index]);
    };

    for (const AndGate& gate : formula_.gates()) {
        const auto lhs = literalSpace(gate.lhs);
        const auto rhs = literalSpace(gate.rhs);
        if (!lhs || !rhs) return std::nullopt;
        nodes[static_cast<std::size_t>(gate.out)] = meet(*lhs, *rhs, n);
        assigned[static_cast<std::size_t>(gate.out)] = true;
    }

    const auto output = literalSpace(formula_.output());
    if (!output || dimension(*output) == 0) {
        return std::nullopt;
    }
    model.outputBasis = output->basis;
    model.outputProjector = projector(*output, n);
    return model;
}

Realizer::Subspace Realizer::zero(std::size_t ambientDimension) {
    return fromRows({}, ambientDimension);
}

Realizer::Subspace Realizer::whole(std::size_t ambientDimension) {
    ExactMatrix rows;
    rows.reserve(ambientDimension);
    for (std::size_t i = 0; i < ambientDimension; ++i) {
        std::vector<Rational> row(ambientDimension, Rational(0));
        row[i] = Rational(1);
        rows.push_back(std::move(row));
    }
    return fromRows(std::move(rows), ambientDimension);
}

Realizer::Subspace Realizer::fromRows(
    ExactMatrix rows,
    std::size_t ambientDimension
) {
    for (const auto& row : rows) {
        if (row.size() != ambientDimension) {
            throw std::invalid_argument("subspace basis row has wrong ambient dimension");
        }
    }

    ExactMatrix reduced = rref(std::move(rows));
    reduced.erase(
        std::remove_if(
            reduced.begin(),
            reduced.end(),
            [](const auto& row) {
                return std::all_of(row.begin(), row.end(), isZero);
            }
        ),
        reduced.end()
    );
    return {std::move(reduced)};
}

Realizer::Subspace Realizer::span(
    const Subspace& lhs,
    const Subspace& rhs
) {
    ExactMatrix rows = lhs.basis;
    rows.insert(rows.end(), rhs.basis.begin(), rhs.basis.end());
    const std::size_t n = !lhs.basis.empty()
        ? lhs.basis.front().size()
        : (!rhs.basis.empty() ? rhs.basis.front().size() : 0);
    return fromRows(std::move(rows), n);
}

Realizer::Subspace Realizer::orthogonalComplement(
    const Subspace& value,
    std::size_t ambientDimension
) {
    return fromRows(
        nullspaceBasis(value.basis, ambientDimension),
        ambientDimension
    );
}

Realizer::Subspace Realizer::meet(
    const Subspace& lhs,
    const Subspace& rhs,
    std::size_t ambientDimension
) {
    const Subspace lhsPerp = orthogonalComplement(lhs, ambientDimension);
    const Subspace rhsPerp = orthogonalComplement(rhs, ambientDimension);
    return orthogonalComplement(span(lhsPerp, rhsPerp), ambientDimension);
}

bool Realizer::equal(const Subspace& lhs, const Subspace& rhs) {
    return lhs.basis == rhs.basis;
}

bool Realizer::isSubspaceOf(const Subspace& lhs, const Subspace& rhs) {
    if (lhs.basis.empty()) return true;
    if (rhs.basis.empty()) return lhs.basis.empty();

    ExactMatrix rows = rhs.basis;
    const std::size_t rhsRank = rhs.basis.size();
    rows.insert(rows.end(), lhs.basis.begin(), lhs.basis.end());
    return rref(std::move(rows)).size() == rhsRank;
}

std::size_t Realizer::dimension(const Subspace& value) noexcept {
    return value.basis.size();
}

ExactMatrix Realizer::rref(ExactMatrix matrix) {
    if (matrix.empty()) return matrix;
    const std::size_t rows = matrix.size();
    const std::size_t cols = matrix.front().size();

    for (const auto& row : matrix) {
        if (row.size() != cols) {
            throw std::invalid_argument("ragged matrix");
        }
    }

    std::size_t pivotRow = 0;
    for (std::size_t col = 0; col < cols && pivotRow < rows; ++col) {
        std::size_t selected = pivotRow;
        while (selected < rows && isZero(matrix[selected][col])) {
            ++selected;
        }
        if (selected == rows) continue;

        std::swap(matrix[pivotRow], matrix[selected]);
        const Rational pivot = matrix[pivotRow][col];
        for (std::size_t c = col; c < cols; ++c) {
            matrix[pivotRow][c] /= pivot;
        }

        for (std::size_t r = 0; r < rows; ++r) {
            if (r == pivotRow || isZero(matrix[r][col])) continue;
            const Rational factor = matrix[r][col];
            for (std::size_t c = col; c < cols; ++c) {
                matrix[r][c] -= factor * matrix[pivotRow][c];
            }
        }
        ++pivotRow;
    }

    matrix.erase(
        std::remove_if(
            matrix.begin(),
            matrix.end(),
            [](const auto& row) {
                return std::all_of(row.begin(), row.end(), isZero);
            }
        ),
        matrix.end()
    );
    return matrix;
}

ExactMatrix Realizer::nullspaceBasis(
    const ExactMatrix& matrix,
    std::size_t columnCount
) {
    if (matrix.empty()) {
        ExactMatrix result;
        result.reserve(columnCount);
        for (std::size_t i = 0; i < columnCount; ++i) {
            std::vector<Rational> row(columnCount, Rational(0));
            row[i] = Rational(1);
            result.push_back(std::move(row));
        }
        return result;
    }

    ExactMatrix reduced = rref(matrix);
    std::vector<std::size_t> pivotColumns;
    pivotColumns.reserve(reduced.size());

    for (const auto& row : reduced) {
        auto it = std::find_if(row.begin(), row.end(), [](const Rational& v) {
            return !isZero(v);
        });
        if (it != row.end()) {
            pivotColumns.push_back(static_cast<std::size_t>(it - row.begin()));
        }
    }

    std::vector<bool> isPivot(columnCount, false);
    for (const std::size_t col : pivotColumns) {
        if (col >= columnCount) throw std::logic_error("pivot out of range");
        isPivot[col] = true;
    }

    ExactMatrix basis;
    for (std::size_t freeCol = 0; freeCol < columnCount; ++freeCol) {
        if (isPivot[freeCol]) continue;
        std::vector<Rational> vector(columnCount, Rational(0));
        vector[freeCol] = Rational(1);

        for (std::size_t row = 0; row < pivotColumns.size(); ++row) {
            const std::size_t pivotCol = pivotColumns[row];
            vector[pivotCol] = -reduced[row][freeCol];
        }
        basis.push_back(std::move(vector));
    }
    return basis;
}

ExactMatrix Realizer::projector(
    const Subspace& value,
    std::size_t ambientDimension
) {
    if (value.basis.empty()) {
        return ExactMatrix(
            ambientDimension,
            std::vector<Rational>(ambientDimension, Rational(0))
        );
    }

    const ExactMatrix bt = transpose(value.basis);
    const ExactMatrix gram = multiply(value.basis, bt);
    const ExactMatrix gramInv = inverse(gram);
    return multiply(multiply(bt, gramInv), value.basis);
}

ExactMatrix Realizer::inverse(ExactMatrix matrix) {
    const std::size_t n = matrix.size();
    if (n == 0) return {};
    for (const auto& row : matrix) {
        if (row.size() != n) throw std::invalid_argument("matrix is not square");
    }

    ExactMatrix augmented(
        n,
        std::vector<Rational>(2 * n, Rational(0))
    );
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t c = 0; c < n; ++c) augmented[r][c] = matrix[r][c];
        augmented[r][n + r] = Rational(1);
    }

    for (std::size_t col = 0; col < n; ++col) {
        std::size_t pivot = col;
        while (pivot < n && isZero(augmented[pivot][col])) ++pivot;
        if (pivot == n) throw std::runtime_error("singular Gram matrix");
        std::swap(augmented[col], augmented[pivot]);

        const Rational scale = augmented[col][col];
        for (std::size_t c = 0; c < 2 * n; ++c) augmented[col][c] /= scale;

        for (std::size_t r = 0; r < n; ++r) {
            if (r == col || isZero(augmented[r][col])) continue;
            const Rational factor = augmented[r][col];
            for (std::size_t c = 0; c < 2 * n; ++c) {
                augmented[r][c] -= factor * augmented[col][c];
            }
        }
    }

    ExactMatrix result(n, std::vector<Rational>(n, Rational(0)));
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t c = 0; c < n; ++c) result[r][c] = augmented[r][n + c];
    }
    return result;
}

ExactMatrix Realizer::transpose(const ExactMatrix& matrix) {
    if (matrix.empty()) return {};
    const std::size_t rows = matrix.size();
    const std::size_t cols = matrix.front().size();
    ExactMatrix result(cols, std::vector<Rational>(rows, Rational(0)));
    for (std::size_t r = 0; r < rows; ++r) {
        if (matrix[r].size() != cols) throw std::invalid_argument("ragged matrix");
        for (std::size_t c = 0; c < cols; ++c) result[c][r] = matrix[r][c];
    }
    return result;
}

ExactMatrix Realizer::multiply(
    const ExactMatrix& lhs,
    const ExactMatrix& rhs
) {
    if (lhs.empty() || rhs.empty()) return {};
    const std::size_t lhsRows = lhs.size();
    const std::size_t inner = lhs.front().size();
    if (rhs.size() != inner) throw std::invalid_argument("matrix dimensions do not match");
    const std::size_t rhsCols = rhs.front().size();

    ExactMatrix result(
        lhsRows,
        std::vector<Rational>(rhsCols, Rational(0))
    );
    for (std::size_t r = 0; r < lhsRows; ++r) {
        if (lhs[r].size() != inner) throw std::invalid_argument("ragged matrix");
        for (std::size_t k = 0; k < inner; ++k) {
            for (std::size_t c = 0; c < rhsCols; ++c) {
                result[r][c] += lhs[r][k] * rhs[k][c];
            }
        }
    }
    return result;
}

ValueId Realizer::valueOfLiteral(
    Lit literal,
    const std::vector<ValueId>& nodeValues,
    const AbstractWitness& witness
) {
    if (literal == TRUE_LIT) return TOP_VALUE;
    if (literal == FALSE_LIT) return BOTTOM_VALUE;
    const NodeId node = literal < 0 ? -literal : literal;
    const std::size_t index = static_cast<std::size_t>(node);
    if (index >= nodeValues.size()) return UNASSIGNED_VALUE;
    const ValueId value = nodeValues[index];
    if (value == UNASSIGNED_VALUE) return value;
    return literal < 0
        ? witness.complements[static_cast<std::size_t>(value)]
        : value;
}

void printModel(std::ostream& out, const ConcreteModel& model) {
    out << "model dimension: " << model.hilbertDimension << '\n';

    auto printMatrix = [&](const ExactMatrix& matrix) {
        if (matrix.empty()) {
            out << "  []\n";
            return;
        }

        std::size_t width = 1;
        for (const auto& row : matrix) {
            for (const Rational& value : row) {
                width = std::max(width, rationalToString(value).size());
            }
        }

        for (const auto& row : matrix) {
            out << "  [";
            for (std::size_t i = 0; i < row.size(); ++i) {
                if (i != 0) out << ' ';
                out << std::setw(static_cast<int>(width)) << rationalToString(row[i]);
            }
            out << "]\n";
        }
    };

    for (const ModelEntry& variable : model.variables) {
        out << variable.name << " projector:\n";
        printMatrix(variable.projector);
    }

    out << "output projector:\n";
    printMatrix(model.outputProjector);
}
}
