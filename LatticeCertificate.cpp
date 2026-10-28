#include "LatticeCertificate.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <functional>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <utility>

namespace ql {
namespace {
Relation inverse(Relation relation) noexcept {
    switch (relation) {
        case Relation::Below: return Relation::Above;
        case Relation::Above: return Relation::Below;
        case Relation::Incomparable: return Relation::Incomparable;
        case Relation::Undefined: return Relation::Undefined;
    }
    return Relation::Undefined;
}

bool lessOrEqual(
    const AbstractWitness& witness,
    ValueId lhs,
    ValueId rhs
) {
    return lhs == rhs || witness.relation(lhs, rhs) == Relation::Below;
}

ValueId literalValue(
    const Formula& formula,
    const AbstractWitness& witness,
    Lit literal
) {
    (void)formula;
    if (literal == TRUE_LIT) return TOP_VALUE;
    if (literal == FALSE_LIT) return BOTTOM_VALUE;

    const NodeId node = literal < 0 ? -literal : literal;
    const std::size_t index = static_cast<std::size_t>(node);
    if (index >= witness.nodeValues.size()) return UNASSIGNED_VALUE;

    const ValueId value = witness.nodeValues[index];
    if (value == UNASSIGNED_VALUE) return UNASSIGNED_VALUE;
    if (value < 0 || static_cast<std::size_t>(value) >= witness.valueCount()) {
        return UNASSIGNED_VALUE;
    }
    return literal < 0
        ? witness.complements[static_cast<std::size_t>(value)]
        : value;
}

std::int32_t lineHyperplaneMeetDimension(
    const AbstractWitness& witness,
    ValueId lhs,
    ValueId rhs
) {
    const std::int32_t n = static_cast<std::int32_t>(witness.hilbertDimension);
    if (lhs == BOTTOM_VALUE || rhs == BOTTOM_VALUE) return 0;
    if (lhs == TOP_VALUE) return witness.dimensions[static_cast<std::size_t>(rhs)];
    if (rhs == TOP_VALUE) return witness.dimensions[static_cast<std::size_t>(lhs)];
    if (lhs == rhs) return witness.dimensions[static_cast<std::size_t>(lhs)];
    if (witness.complements[static_cast<std::size_t>(lhs)] == rhs) return 0;

    const Relation relation = witness.relation(lhs, rhs);
    if (relation == Relation::Below) {
        return witness.dimensions[static_cast<std::size_t>(lhs)];
    }
    if (relation == Relation::Above) {
        return witness.dimensions[static_cast<std::size_t>(rhs)];
    }
    if (relation != Relation::Incomparable) return -1;

    const auto a = witness.dimensions[static_cast<std::size_t>(lhs)];
    const auto b = witness.dimensions[static_cast<std::size_t>(rhs)];
    const bool aLine = a == 1;
    const bool bLine = b == 1;
    const bool aHyperplane = a == n - 1;
    const bool bHyperplane = b == n - 1;

    if (aLine && bLine) return 0;
    if ((aLine && bHyperplane) || (aHyperplane && bLine)) return 0;
    if (aHyperplane && bHyperplane) return n - 2;
    return -1;
}

bool gateResultCanBeExactMeet(
    const AbstractWitness& witness,
    ValueId lhs,
    ValueId rhs,
    ValueId result
) {
    if (result < 0 || static_cast<std::size_t>(result) >= witness.valueCount()) {
        return false;
    }

    const std::int32_t expectedDimension =
        lineHyperplaneMeetDimension(witness, lhs, rhs);
    if (expectedDimension < 0 ||
        witness.dimensions[static_cast<std::size_t>(result)] != expectedDimension) {
        return false;
    }

    if (!lessOrEqual(witness, result, lhs) ||
        !lessOrEqual(witness, result, rhs)) {
        return false;
    }

    if (expectedDimension == witness.dimensions[static_cast<std::size_t>(lhs)] &&
        !lessOrEqual(witness, lhs, result)) {
        return false;
    }
    if (expectedDimension == witness.dimensions[static_cast<std::size_t>(rhs)] &&
        !lessOrEqual(witness, rhs, result)) {
        return false;
    }

    if (expectedDimension == 1) {
        for (ValueId candidate = 0;
             candidate < static_cast<ValueId>(witness.valueCount());
             ++candidate) {
            if (candidate == result ||
                witness.dimensions[static_cast<std::size_t>(candidate)] != 1) {
                continue;
            }
            if (lessOrEqual(witness, candidate, lhs) &&
                lessOrEqual(witness, candidate, rhs)) {
                return false;
            }
        }
    }

    return true;
}

struct SupportProblem {
    std::size_t dimension = 0;
    std::vector<ValueId> lines;
    std::vector<std::vector<bool>> orthogonal;
};

std::optional<SupportProblem> makeSupportProblem(
    const AbstractWitness& witness
) {
    const std::size_t n = witness.hilbertDimension;

    if (n < 3 || n > 6) return std::nullopt;

    SupportProblem problem;
    problem.dimension = n;

    for (ValueId value = 2;
         value < static_cast<ValueId>(witness.valueCount());
         ++value) {
        const auto d = witness.dimensions[static_cast<std::size_t>(value)];
        if (d != 1 && d != static_cast<std::int32_t>(n - 1)) {
            return std::nullopt;
        }
        if (d == 1) problem.lines.push_back(value);
    }

    if (2 + 2 * problem.lines.size() != witness.valueCount()) {
        return std::nullopt;
    }

    const std::size_t m = problem.lines.size();
    problem.orthogonal.assign(m, std::vector<bool>(m, false));

    for (std::size_t i = 0; i < m; ++i) {
        const ValueId line = problem.lines[i];
        const ValueId hyperplane = witness.complements[static_cast<std::size_t>(line)];
        if (hyperplane < 0 ||
            static_cast<std::size_t>(hyperplane) >= witness.valueCount() ||
            witness.dimensions[static_cast<std::size_t>(hyperplane)] !=
                static_cast<std::int32_t>(n - 1) ||
            witness.complements[static_cast<std::size_t>(hyperplane)] != line) {
            return std::nullopt;
        }
        if (witness.relation(line, hyperplane) != Relation::Incomparable) {
            return std::nullopt;
        }
    }

    for (std::size_t i = 0; i < m; ++i) {
        for (std::size_t j = i + 1; j < m; ++j) {
            const ValueId li = problem.lines[i];
            const ValueId lj = problem.lines[j];
            const ValueId hi = witness.complements[static_cast<std::size_t>(li)];
            const ValueId hj = witness.complements[static_cast<std::size_t>(lj)];

            if (witness.relation(li, lj) != Relation::Incomparable ||
                witness.relation(hi, hj) != Relation::Incomparable) {
                return std::nullopt;
            }

            const Relation iToHyperplaneJ = witness.relation(li, hj);
            const Relation jToHyperplaneI = witness.relation(lj, hi);
            const bool iOrthogonalJ = iToHyperplaneJ == Relation::Below;
            const bool jOrthogonalI = jToHyperplaneI == Relation::Below;
            if (iOrthogonalJ != jOrthogonalI) return std::nullopt;
            if (iToHyperplaneJ != (iOrthogonalJ
                    ? Relation::Below : Relation::Incomparable) ||
                jToHyperplaneI != (jOrthogonalI
                    ? Relation::Below : Relation::Incomparable)) {
                return std::nullopt;
            }

            problem.orthogonal[i][j] = iOrthogonalJ;
            problem.orthogonal[j][i] = iOrthogonalJ;
        }
    }

    return problem;
}

std::optional<std::vector<std::uint64_t>> solveSupportMasks(
    const SupportProblem& problem
) {
    const std::size_t m = problem.lines.size();
    if (m == 0) return std::vector<std::uint64_t>{};
    const std::size_t n = problem.dimension;

    std::vector<std::size_t> order(m);
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](std::size_t lhs, std::size_t rhs) {
        const auto degree = [&](std::size_t v) {
            return static_cast<std::size_t>(std::count(
                problem.orthogonal[v].begin(), problem.orthogonal[v].end(), true
            ));
        };
        const auto dl = degree(lhs);
        const auto dr = degree(rhs);
        if (dl != dr) return dl > dr;
        return lhs < rhs;
    });

    std::vector<std::uint64_t> allMasks;
    const std::uint64_t limit = std::uint64_t{1} << n;
    allMasks.reserve(static_cast<std::size_t>(limit - 1));
    for (std::uint64_t mask = 1; mask < limit; ++mask) allMasks.push_back(mask);

    std::vector<std::uint64_t> masks(m, 0);
    const auto consistent = [&](std::size_t vertex, std::uint64_t mask) {
        for (std::size_t other = 0; other < m; ++other) {
            if (masks[other] == 0) continue;
            const bool disjoint = (mask & masks[other]) == 0;
            if (disjoint != problem.orthogonal[vertex][other]) return false;
            if (mask == masks[other] && (mask & (mask - 1)) == 0) return false;
        }
        return true;
    };

    std::function<bool(std::size_t)> dfs = [&](std::size_t depth) {
        if (depth == m) return true;
        const std::size_t vertex = order[depth];

        if (depth == 0) {
            for (std::size_t cardinality = 1; cardinality <= n; ++cardinality) {
                const std::uint64_t mask =
                    (std::uint64_t{1} << cardinality) - 1;
                if (!consistent(vertex, mask)) continue;
                masks[vertex] = mask;
                if (dfs(depth + 1)) return true;
                masks[vertex] = 0;
            }
            return false;
        }

        for (const std::uint64_t mask : allMasks) {
            if (!consistent(vertex, mask)) continue;
            masks[vertex] = mask;
            if (dfs(depth + 1)) return true;
            masks[vertex] = 0;
        }
        return false;
    };

    if (!dfs(0)) return std::nullopt;
    return masks;
}

bool supportGateSemantics(
    const Formula& formula,
    const AbstractWitness& witness
) {
    for (const AndGate& gate : formula.gates()) {
        const ValueId lhs = literalValue(formula, witness, gate.lhs);
        const ValueId rhs = literalValue(formula, witness, gate.rhs);
        const std::size_t outIndex = static_cast<std::size_t>(gate.out);
        if (lhs == UNASSIGNED_VALUE || rhs == UNASSIGNED_VALUE ||
            outIndex >= witness.nodeValues.size()) {
            return false;
        }
        const ValueId result = witness.nodeValues[outIndex];
        if (!gateResultCanBeExactMeet(witness, lhs, rhs, result)) return false;
    }

    const ValueId output = literalValue(formula, witness, formula.output());
    return output != UNASSIGNED_VALUE &&
           witness.dimensions[static_cast<std::size_t>(output)] > 0;
}
}

bool LatticeCertificate::relationsWellFormed(
    const AbstractWitness& witness
) {
    const std::size_t count = witness.valueCount();
    if (count < 2 ||
        witness.complements.size() != count ||
        witness.relations.size() != count * count ||
        witness.dimensions.size() != count) {
        return false;
    }

    const auto n = static_cast<std::int32_t>(witness.hilbertDimension);
    if (witness.dimensions[BOTTOM_VALUE] != 0 ||
        witness.dimensions[TOP_VALUE] != n ||
        witness.complements[BOTTOM_VALUE] != TOP_VALUE ||
        witness.complements[TOP_VALUE] != BOTTOM_VALUE) {
        return false;
    }

    if (witness.relation(BOTTOM_VALUE, TOP_VALUE) != Relation::Below) {
        return false;
    }

    for (ValueId value = 0; value < static_cast<ValueId>(count); ++value) {
        const auto dim = witness.dimensions[static_cast<std::size_t>(value)];
        if (dim < 0 || dim > n) return false;

        const ValueId complement =
            witness.complements[static_cast<std::size_t>(value)];
        if (complement < 0 || static_cast<std::size_t>(complement) >= count) {
            return false;
        }
        if (witness.complements[static_cast<std::size_t>(complement)] != value ||
            witness.dimensions[static_cast<std::size_t>(complement)] != n - dim) {
            return false;
        }

        if (value != BOTTOM_VALUE && value != TOP_VALUE) {
            if (witness.relation(BOTTOM_VALUE, value) != Relation::Below ||
                witness.relation(value, TOP_VALUE) != Relation::Below ||
                witness.relation(value, complement) != Relation::Incomparable) {
                return false;
            }
        }
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            const Relation rel = witness.relation(lhs, rhs);
            if (rel == Relation::Undefined ||
                witness.relation(rhs, lhs) != inverse(rel)) {
                return false;
            }

            const auto dl = witness.dimensions[static_cast<std::size_t>(lhs)];
            const auto dr = witness.dimensions[static_cast<std::size_t>(rhs)];
            if (rel == Relation::Below && dl >= dr) return false;
            if (rel == Relation::Above && dr >= dl) return false;
        }
    }

    return true;
}

bool LatticeCertificate::trivialGeometryCertified(
    const AbstractWitness& witness
) {
    return witness.hilbertDimension <= 2 ||
           (witness.valueCount() <= 4 &&
            witness.valueCount() == witness.baseValueCount);
}

bool LatticeCertificate::rankThreeGateSemantics(
    const Formula& formula,
    const AbstractWitness& witness
) {
    if (witness.hilbertDimension != 3) return false;

    for (const AndGate& gate : formula.gates()) {
        const ValueId lhs = literalValue(formula, witness, gate.lhs);
        const ValueId rhs = literalValue(formula, witness, gate.rhs);
        const std::size_t outIndex = static_cast<std::size_t>(gate.out);
        if (lhs == UNASSIGNED_VALUE || rhs == UNASSIGNED_VALUE ||
            outIndex >= witness.nodeValues.size()) {
            return false;
        }
        const ValueId result = witness.nodeValues[outIndex];
        if (!gateResultCanBeExactMeet(witness, lhs, rhs, result)) {
            return false;
        }
    }

    const ValueId output = literalValue(formula, witness, formula.output());
    return output != UNASSIGNED_VALUE &&
           witness.dimensions[static_cast<std::size_t>(output)] > 0;
}

std::optional<SupportCertificate> LatticeCertificate::supportCertificate(
    const Formula& formula,
    const AbstractWitness& witness
) {
    if (!relationsWellFormed(witness)) return std::nullopt;

    const auto problem = makeSupportProblem(witness);
    if (!problem) return std::nullopt;

    const auto masks = solveSupportMasks(*problem);
    if (!masks) return std::nullopt;

    if (!supportGateSemantics(formula, witness)) return std::nullopt;

    SupportCertificate certificate;
    certificate.hilbertDimension = witness.hilbertDimension;
    certificate.lineValues = problem->lines;
    certificate.supportMasks = *masks;
    return certificate;
}

bool LatticeCertificate::certify(
    const Formula& formula,
    const AbstractWitness& witness
) {
    if (!relationsWellFormed(witness)) return false;
    if (trivialGeometryCertified(witness)) return true;
    return supportCertificate(formula, witness).has_value();
}
}
