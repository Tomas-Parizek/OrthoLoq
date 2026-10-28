#include "Solver.hpp"
#include "Evaluator.hpp"
#include "ExactTheory.hpp"
#include "FormulaAnalysis.hpp"
#include "FormulaSymmetry.hpp"
#include "TheoremPatterns.hpp"

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <stdexcept>
#include <unordered_set>
#include <utility>

namespace ql {
namespace {
std::size_t maximumLatticeValues(const Formula& formula) {
    return 2 + 2 * formula.variables().size();
}

std::uint64_t adaptiveExactBranchBudget() {
    constexpr std::uint64_t DEFAULT_BUDGET = 1000;
    const char* configured = std::getenv("QLCIR_ADAPTIVE_EXACT_BRANCH_BUDGET");
    if (configured == nullptr || *configured == '\0') return DEFAULT_BUDGET;

    char* end = nullptr;
    const unsigned long long parsed = std::strtoull(configured, &end, 10);
    if (end == configured || *end != '\0') return DEFAULT_BUDGET;
    return static_cast<std::uint64_t>(parsed);
}
}

Solver::Solver(
    const Formula& formula,
    bool keepWitness,
    SolveMode mode
)
    : formula_(formula),
      lattice_(formula.dimension(), maximumLatticeValues(formula)),
      keepWitness_(keepWitness),
      mode_(mode) {
    variables_.reserve(formula.variables().size());

    for (const auto& [name, node] : formula.variables()) {
        variables_.push_back({name, node});
    }

    const auto occurrences = variableOccurrenceCounts(formula_);
    std::sort(
        variables_.begin(),
        variables_.end(),
        [&](const Variable& lhs, const Variable& rhs) {
            const auto lhsIt = occurrences.find(lhs.node);
            const auto rhsIt = occurrences.find(rhs.node);
            const std::size_t lhsCount =
                lhsIt == occurrences.end() ? 0 : lhsIt->second;
            const std::size_t rhsCount =
                rhsIt == occurrences.end() ? 0 : rhsIt->second;
            if (lhsCount != rhsCount) return lhsCount > rhsCount;
            return lhs.node < rhs.node;
        }
    );

    assignment_.assign(variables_.size(), UNASSIGNED_VALUE);

    occurrenceWeight_.assign(variables_.size(), 0);
    for (std::size_t i = 0; i < variables_.size(); ++i) {
        variableIndexByNode_.emplace(variables_[i].node, i);
        const auto it = occurrences.find(variables_[i].node);
        if (it != occurrences.end()) occurrenceWeight_[i] = it->second;
    }

    symmetryOrbit_.assign(variables_.size(), -1);
    symmetryPosition_.assign(variables_.size(), -1);
    const auto symmetryOrbits = variableSwapSymmetryOrbits(formula_);
    for (std::size_t orbit = 0; orbit < symmetryOrbits.size(); ++orbit) {
        for (std::size_t position = 0;
             position < symmetryOrbits[orbit].size();
             ++position) {
            const auto it = variableIndexByNode_.find(symmetryOrbits[orbit][position]);
            if (it == variableIndexByNode_.end()) continue;
            symmetryOrbit_[it->second] = static_cast<std::int32_t>(orbit);
            symmetryPosition_[it->second] = static_cast<std::int32_t>(position);
        }
    }

    gateByNode_.assign(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1,
        nullptr
    );
    for (const AndGate& gate : formula_.gates()) {
        gateByNode_[static_cast<std::size_t>(gate.out)] = &gate;
    }

    mustBeNonzero_.assign(gateByNode_.size(), false);
    mustNotBeTop_.assign(gateByNode_.size(), false);
    initializeGoalRequirements();

    interactionWeight_.assign(
        variables_.size(),
        std::vector<std::size_t>(variables_.size(), 0)
    );
    std::vector<std::unordered_set<NodeId>> support(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1
    );
    for (const auto& [name, node] : formula_.variables()) {
        (void)name;
        support[static_cast<std::size_t>(node)].insert(node);
    }
    const auto supportOfLiteral = [&](Lit literal) -> const std::unordered_set<NodeId>& {
        const NodeId node = static_cast<NodeId>(std::abs(literal));
        return support[static_cast<std::size_t>(node)];
    };
    for (const AndGate& gate : formula_.gates()) {
        auto merged = supportOfLiteral(gate.lhs);
        const auto& rhsSupport = supportOfLiteral(gate.rhs);
        merged.insert(rhsSupport.begin(), rhsSupport.end());
        support[static_cast<std::size_t>(gate.out)] = std::move(merged);

        std::vector<std::size_t> indices;
        for (const NodeId node : support[static_cast<std::size_t>(gate.out)]) {
            const auto it = variableIndexByNode_.find(node);
            if (it != variableIndexByNode_.end()) indices.push_back(it->second);
        }
        for (std::size_t a = 0; a < indices.size(); ++a) {
            for (std::size_t b = a + 1; b < indices.size(); ++b) {
                ++interactionWeight_[indices[a]][indices[b]];
                ++interactionWeight_[indices[b]][indices[a]];
            }
        }
    }

    stats_.maxActiveValues = lattice_.activeValueCount();
}

SolveResult Solver::solve() {
    stats_ = {};
    stats_.maxActiveValues = lattice_.activeValueCount();
    std::fill(assignment_.begin(), assignment_.end(), UNASSIGNED_VALUE);
    memo_.clear();
    relationMemo_.clear();
    witness_.reset();
    globalExactDecision_.reset();

    if (mode_ == SolveMode::ExactOnly) {
        return solveExact();
    }

    const SolveResult fast = solveFast();
    if (fast != SolveResult::Unknown || mode_ == SolveMode::FastOnly) {
        return fast;
    }

    return solveExact();
}

SolveResult Solver::solveFast() {
    bool structuralApplied = false;
    const SolveResult structural = solveStructurally(structuralApplied);

    if (structuralApplied) {
        if (!keepWitness_) return structural;
        if (structural == SolveResult::Unsat) return structural;

        if (structural == SolveResult::Sat) {
            if (formula_.dimension() <= 3) {
                const SolveResult core = solveCore();
                if (core == SolveResult::Sat) return core;
            }
            return SolveResult::Sat;
        }

        return solveCore();
    }

    return solveCore();
}

SolveResult Solver::solveExact() {
    ExactMembershipTheorySolver theory(formula_);
    const ExactTheoryResult result = theory.solve();
    const ExactTheoryStats& exact = theory.stats();

    stats_.exactTheoryCalls += exact.backendCalls;
    stats_.exactTheoryRealVariables += exact.realVariables;
    stats_.exactTheoryEqualities += exact.polynomialEqualities;
    stats_.exactTheoryInequalities += exact.polynomialInequalities;
    stats_.exactTheorySmtBytes += exact.smtBytes;

    if (result == ExactTheoryResult::Sat) {
        ++stats_.exactTheorySat;
        return SolveResult::Sat;
    }

    ++stats_.exactTheoryUnsat;
    return SolveResult::Unsat;
}

SolveResult Solver::solveCore() {
    if (formula_.output() == FALSE_LIT) return SolveResult::Unsat;
    if (formula_.output() == TRUE_LIT && !keepWitness_) return SolveResult::Sat;
    return search(0);
}

void Solver::accumulateStats(const SolveStats& other) {
    stats_.recursiveCalls += other.recursiveCalls;
    stats_.branches += other.branches;
    stats_.leaves += other.leaves;
    stats_.reusedValueBranches += other.reusedValueBranches;
    stats_.freshValueBranches += other.freshValueBranches;
    stats_.relationDecisions += other.relationDecisions;
    stats_.upperRelationDecisions += other.upperRelationDecisions;
    stats_.lowerRelationDecisions += other.lowerRelationDecisions;
    stats_.relationConfigurations += other.relationConfigurations;
    stats_.prunedRelationBranches += other.prunedRelationBranches;
    stats_.structuralSubproblems += other.structuralSubproblems;
    stats_.independentMeetSplits += other.independentMeetSplits;
    stats_.topLevelJoinSplits += other.topLevelJoinSplits;
    stats_.partialDimensionPrunes += other.partialDimensionPrunes;
    stats_.dimensionDomainPrunes += other.dimensionDomainPrunes;
    stats_.memoHits += other.memoHits;
    stats_.memoStores += other.memoStores;
    stats_.demandedRelationPairs += other.demandedRelationPairs;
    stats_.relationStateMemoHits += other.relationStateMemoHits;
    stats_.relationStateMemoStores += other.relationStateMemoStores;
    stats_.deferredRelationCompletions += other.deferredRelationCompletions;
    stats_.theoremPatternHits += other.theoremPatternHits;
    stats_.symmetryDimensionPrunes += other.symmetryDimensionPrunes;
    stats_.exactTheoryCalls += other.exactTheoryCalls;
    stats_.exactTheorySat += other.exactTheorySat;
    stats_.exactTheoryUnsat += other.exactTheoryUnsat;
    stats_.exactTheoryRealVariables += other.exactTheoryRealVariables;
    stats_.exactTheoryEqualities += other.exactTheoryEqualities;
    stats_.exactTheoryInequalities += other.exactTheoryInequalities;
    stats_.exactTheorySmtBytes += other.exactTheorySmtBytes;
    stats_.adaptiveExactHandoffs += other.adaptiveExactHandoffs;
    stats_.maxActiveValues = std::max(stats_.maxActiveValues, other.maxActiveValues);
}

SolveResult Solver::solveStructurally(bool& applied) {
    applied = false;
    if (formula_.output() == FALSE_LIT) {
        applied = true;
        return SolveResult::Unsat;
    }
    if (formula_.output() == TRUE_LIT) {
        applied = true;
        return SolveResult::Sat;
    }

    const TheoremPatternMatch theorem = matchStandardTheoremPattern(formula_);
    if (theorem.decision != TheoremDecision::None) {
        applied = true;
        ++stats_.theoremPatternHits;
        return theorem.decision == TheoremDecision::Sat
            ? SolveResult::Sat
            : SolveResult::Unsat;
    }

    std::vector<Formula> joinParts = splitTopLevelJoin(formula_);
    if (joinParts.size() > 1) {
        applied = true;
        ++stats_.topLevelJoinSplits;
        SolveResult aggregate = SolveResult::Unsat;
        for (Formula& rawPart : joinParts) {
            ++stats_.structuralSubproblems;
            Formula part = preprocessFormula(rawPart);
            Solver child(part, false, mode_);
            const SolveResult result = child.solve();
            accumulateStats(child.stats());
            if (result == SolveResult::Sat) return SolveResult::Sat;
            aggregate = combine(aggregate, result);
        }
        return aggregate;
    }

    std::vector<Formula> meetParts = splitIndependentTopLevelMeet(formula_);
    if (meetParts.size() > 1) {
        applied = true;
        ++stats_.independentMeetSplits;
        SolveResult aggregate = SolveResult::Sat;
        for (Formula& rawPart : meetParts) {
            ++stats_.structuralSubproblems;
            Formula part = preprocessFormula(rawPart);
            Solver child(part, false, mode_);
            const SolveResult result = child.solve();
            accumulateStats(child.stats());
            if (result == SolveResult::Unsat) return SolveResult::Unsat;
            if (result == SolveResult::Unknown) aggregate = SolveResult::Unknown;
        }
        return aggregate;
    }

    return SolveResult::Unknown;
}

const SolveStats& Solver::stats() const noexcept {
    return stats_;
}

const Lattice& Solver::lattice() const noexcept {
    return lattice_;
}

const AbstractWitness* Solver::witness() const noexcept {
    return witness_ ? &*witness_ : nullptr;
}

SolveResult Solver::search(std::size_t assignedCount) {
    ++stats_.recursiveCalls;

    if (globalExactDecision_) return *globalExactDecision_;

    const std::uint64_t adaptiveBudget = adaptiveExactBranchBudget();
    if (!keepWitness_ && mode_ == SolveMode::Complete && adaptiveBudget != 0 &&
        stats_.branches >= adaptiveBudget) {
        ++stats_.adaptiveExactHandoffs;
        globalExactDecision_ = solveExact();
        return *globalExactDecision_;
    }

    if (!outputMayBeNonzero()) {
        ++stats_.partialDimensionPrunes;
        return SolveResult::Unsat;
    }

    std::string memoKey;
    if (!keepWitness_) {
        memoKey = canonicalSearchKey();
        if (const auto it = memo_.find(memoKey); it != memo_.end()) {
            ++stats_.memoHits;
            return it->second;
        }
    }

    if (assignedCount == variables_.size()) {
        ++stats_.leaves;
        const SolveResult result = evaluateCompleteAssignment();
        if (!keepWitness_) {
            memo_.emplace(std::move(memoKey), result);
            ++stats_.memoStores;
        }
        return result;
    }

    VariableSelection selection = chooseNextVariable();
    const std::size_t variableIndex = selection.index;
    if (variableIndex >= variables_.size()) {
        throw std::logic_error("failed to select an unassigned variable");
    }

    const std::vector<bool>& dimensionAllowed = selection.allowedDimensions;
    bool anyDimension = false;
    for (bool allowed : dimensionAllowed) anyDimension |= allowed;
    if (!anyDimension) {
        ++stats_.partialDimensionPrunes;
        if (!keepWitness_) {
            memo_.emplace(std::move(memoKey), SolveResult::Unsat);
            ++stats_.memoStores;
        }
        return SolveResult::Unsat;
    }

    SolveResult result = SolveResult::Unsat;

    const std::size_t existingCount = lattice_.activeValueCount();
    for (ValueId value = 0; value < static_cast<ValueId>(existingCount); ++value) {
        const std::int32_t dim = lattice_.dimension(value);
        if (dim < 0 || static_cast<std::size_t>(dim) >= dimensionAllowed.size() ||
            !dimensionAllowed[static_cast<std::size_t>(dim)]) {
            ++stats_.dimensionDomainPrunes;
            continue;
        }

        ++stats_.branches;
        ++stats_.reusedValueBranches;
        const SolveResult branch = recurseWithAssignment(
            assignedCount,
            variableIndex,
            value
        );
        if (branch == SolveResult::Sat) {
            if (!keepWitness_) {
                memo_[memoKey] = SolveResult::Sat;
                ++stats_.memoStores;
            }
            return SolveResult::Sat;
        }
        result = combine(result, branch);
    }

    for (std::uint32_t dim = 1; dim < lattice_.hilbertDimension(); ++dim) {
        if (static_cast<std::size_t>(dim) >= dimensionAllowed.size() ||
            !dimensionAllowed[static_cast<std::size_t>(dim)]) {
            ++stats_.dimensionDomainPrunes;
            continue;
        }

        const ValuePair pair = lattice_.pushValuePair(dim);
        stats_.maxActiveValues = std::max(
            stats_.maxActiveValues,
            lattice_.activeValueCount()
        );

        ++stats_.branches;
        ++stats_.freshValueBranches;
        const SolveResult branch = recurseWithAssignment(
            assignedCount,
            variableIndex,
            pair.value
        );
        lattice_.popValuePair();

        if (branch == SolveResult::Sat) {
            if (!keepWitness_) {
                memo_[memoKey] = SolveResult::Sat;
                ++stats_.memoStores;
            }
            return SolveResult::Sat;
        }
        result = combine(result, branch);
    }

    if (!keepWitness_) {
        memo_[std::move(memoKey)] = result;
        ++stats_.memoStores;
    }
    return result;
}

SolveResult Solver::recurseWithAssignment(
    std::size_t assignedCount,
    std::size_t variableIndex,
    ValueId value
) {
    if (assignment_[variableIndex] != UNASSIGNED_VALUE) {
        throw std::logic_error("variable is already assigned");
    }

    assignment_[variableIndex] = value;
    const SolveResult result = search(assignedCount + 1);
    assignment_[variableIndex] = UNASSIGNED_VALUE;
    return result;
}

Solver::VariableSelection Solver::chooseNextVariable() {
    VariableSelection bestSelection;
    bestSelection.index = variables_.size();

    std::size_t bestDomain = std::numeric_limits<std::size_t>::max();
    std::size_t bestInteraction = 0;
    std::size_t bestOccurrence = 0;

    for (std::size_t candidate = 0; candidate < variables_.size(); ++candidate) {
        if (assignment_[candidate] != UNASSIGNED_VALUE) continue;

        const std::size_t dimensionCount =
            static_cast<std::size_t>(lattice_.hilbertDimension()) + 1;
        std::vector<bool> allowed(dimensionCount, false);
        std::size_t dimensionDomain = 0;
        for (std::size_t dim = 0; dim < dimensionCount; ++dim) {
            allowed[dim] = outputMayBeNonzero(
                std::pair{candidate, static_cast<std::int32_t>(dim)}
            );
            if (allowed[dim] &&
                !dimensionSymmetryAllowed(candidate, static_cast<std::int32_t>(dim))) {
                allowed[dim] = false;
                ++stats_.symmetryDimensionPrunes;
            }
            if (allowed[dim]) ++dimensionDomain;
        }

        std::size_t interaction = 0;
        for (std::size_t other = 0; other < variables_.size(); ++other) {
            if (assignment_[other] == UNASSIGNED_VALUE) continue;
            interaction += interactionWeight_[candidate][other];
        }

        const std::size_t occurrence = occurrenceWeight_[candidate];
        if (bestSelection.index == variables_.size() ||
            dimensionDomain < bestDomain ||
            (dimensionDomain == bestDomain && interaction > bestInteraction) ||
            (dimensionDomain == bestDomain && interaction == bestInteraction &&
             occurrence > bestOccurrence) ||
            (dimensionDomain == bestDomain && interaction == bestInteraction &&
             occurrence == bestOccurrence &&
             variables_[candidate].node < variables_[bestSelection.index].node)) {
            bestSelection.index = candidate;
            bestSelection.allowedDimensions = std::move(allowed);
            bestDomain = dimensionDomain;
            bestInteraction = interaction;
            bestOccurrence = occurrence;
        }
    }
    return bestSelection;
}

bool Solver::dimensionSymmetryAllowed(
    std::size_t variableIndex,
    std::int32_t dimension
) const {
    if (variableIndex >= symmetryOrbit_.size()) return true;
    const std::int32_t orbit = symmetryOrbit_[variableIndex];
    if (orbit < 0) return true;
    const std::int32_t position = symmetryPosition_[variableIndex];

    for (std::size_t other = 0; other < variables_.size(); ++other) {
        if (other == variableIndex || assignment_[other] == UNASSIGNED_VALUE) continue;
        if (symmetryOrbit_[other] != orbit) continue;
        const std::int32_t otherDim = lattice_.dimension(assignment_[other]);
        if (symmetryPosition_[other] < position && otherDim > dimension) return false;
        if (symmetryPosition_[other] > position && dimension > otherDim) return false;
    }
    return true;
}

bool Solver::outputMayBeNonzero(
    std::optional<std::pair<std::size_t, std::int32_t>> dimensionOverride
) const {
    std::vector<std::optional<PartialInfo>> memo(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1
    );
    const PartialInfo info = partialInfo(formula_.output(), dimensionOverride, memo);
    return info.possible && info.dimension.max > 0;
}

Solver::PartialInfo Solver::partialInfo(
    Lit literal,
    std::optional<std::pair<std::size_t, std::int32_t>> dimensionOverride,
    std::vector<std::optional<PartialInfo>>& memo
) const {
    const std::int32_t n =
        static_cast<std::int32_t>(lattice_.hilbertDimension());

    if (literal == TRUE_LIT) return {{n, n}, TOP_VALUE, true};
    if (literal == FALSE_LIT) return {{0, 0}, BOTTOM_VALUE, true};

    const bool negated = literal < 0;
    const NodeId node = static_cast<NodeId>(std::abs(literal));
    const std::size_t nodeIndex = static_cast<std::size_t>(node);

    PartialInfo positive;
    if (memo[nodeIndex].has_value()) {
        positive = *memo[nodeIndex];
    } else if (const auto it = variableIndexByNode_.find(node);
               it != variableIndexByNode_.end()) {
        const std::size_t variableIndex = it->second;
        const ValueId assigned = assignment_[variableIndex];
        if (assigned != UNASSIGNED_VALUE) {
            const std::int32_t dim = lattice_.dimension(assigned);
            positive = {{dim, dim}, assigned};
        } else if (dimensionOverride &&
                   dimensionOverride->first == variableIndex) {
            const std::int32_t dim = dimensionOverride->second;
            positive.dimension = {dim, dim};
            if (dim == 0) positive.knownValue = BOTTOM_VALUE;
            if (dim == n) positive.knownValue = TOP_VALUE;
        } else {
            positive.dimension = {0, n};
        }
        if (nodeIndex < mustBeNonzero_.size() && mustBeNonzero_[nodeIndex]) {
            positive.dimension.min = std::max<std::int32_t>(
                positive.dimension.min,
                1
            );
        }
        if (nodeIndex < mustNotBeTop_.size() && mustNotBeTop_[nodeIndex]) {
            positive.dimension.max = std::min<std::int32_t>(
                positive.dimension.max,
                n - 1
            );
        }
        positive.possible = positive.dimension.min <= positive.dimension.max;
        memo[nodeIndex] = positive;
    } else {
        const AndGate* gate = nodeIndex < gateByNode_.size()
            ? gateByNode_[nodeIndex]
            : nullptr;
        if (gate == nullptr) {
            throw std::logic_error("partial evaluator saw unknown AIG node");
        }

        const PartialInfo lhs = partialInfo(gate->lhs, dimensionOverride, memo);
        const PartialInfo rhs = partialInfo(gate->rhs, dimensionOverride, memo);

        if (!lhs.possible || !rhs.possible) {
            positive.possible = false;
            positive.dimension = {1, 0};
            memo[nodeIndex] = positive;
            return positive;
        }

        if (lhs.knownValue == BOTTOM_VALUE || rhs.knownValue == BOTTOM_VALUE) {
            positive = {{0, 0}, BOTTOM_VALUE};
        } else if (lhs.knownValue == TOP_VALUE) {
            positive = rhs;
        } else if (rhs.knownValue == TOP_VALUE) {
            positive = lhs;
        } else if (lhs.knownValue != UNASSIGNED_VALUE &&
                   rhs.knownValue != UNASSIGNED_VALUE) {
            const ValueId a = lhs.knownValue;
            const ValueId b = rhs.knownValue;
            if (a == b) {
                positive = lhs;
            } else if (areKnownOrthogonal(a, b)) {
                positive = {{0, 0}, BOTTOM_VALUE};
            } else {
                const Relation relation = lattice_.relation(a, b);
                if (relation == Relation::Below) {
                    positive = lhs;
                } else if (relation == Relation::Above) {
                    positive = rhs;
                } else {
                    positive.dimension = structuralMeet({a, b});
                }
            }
        } else {
            positive.dimension.min = std::max<std::int32_t>(
                0,
                lhs.dimension.min + rhs.dimension.min - n
            );
            positive.dimension.max = std::min(
                lhs.dimension.max,
                rhs.dimension.max
            );
        }
        if (nodeIndex < mustBeNonzero_.size() && mustBeNonzero_[nodeIndex]) {
            positive.dimension.min = std::max<std::int32_t>(
                positive.dimension.min,
                1
            );
        }
        if (nodeIndex < mustNotBeTop_.size() && mustNotBeTop_[nodeIndex]) {
            positive.dimension.max = std::min<std::int32_t>(
                positive.dimension.max,
                n - 1
            );
        }
        positive.possible = positive.dimension.min <= positive.dimension.max;
        memo[nodeIndex] = positive;
    }

    if (!negated) return positive;

    PartialInfo result;
    result.possible = positive.possible;
    if (!positive.possible) {
        result.dimension = {1, 0};
        return result;
    }
    result.dimension = {
        n - positive.dimension.max,
        n - positive.dimension.min
    };
    if (positive.knownValue != UNASSIGNED_VALUE) {
        result.knownValue = lattice_.complement(positive.knownValue);
    }
    return result;
}

std::string Solver::canonicalSearchKey() const {
    std::string key;
    key.reserve(16 * variables_.size());
    key.append("n=").append(std::to_string(lattice_.hilbertDimension())).push_back('|');

    std::unordered_map<ValueId, std::size_t> pairLabels;
    std::size_t nextLabel = 0;

    for (std::size_t i = 0; i < assignment_.size(); ++i) {
        const ValueId value = assignment_[i];
        if (value == UNASSIGNED_VALUE) {
            key.append("u;");
            continue;
        }
        if (value == BOTTOM_VALUE || value == TOP_VALUE) {
            key.push_back(value == BOTTOM_VALUE ? '0' : '1');
            key.push_back(';');
            continue;
        }

        const ValueId complement = lattice_.complement(value);
        const ValueId root = std::min(value, complement);
        auto [it, inserted] = pairLabels.emplace(root, nextLabel);
        if (inserted) ++nextLabel;
        const bool complementSide = value != root;

        key.push_back('p');
        key.append(std::to_string(it->second));
        key.push_back(complementSide ? 'c' : 'a');
        key.push_back(':');
        key.append(std::to_string(lattice_.dimension(value)));
        key.push_back(';');
    }
    return key;
}

std::string Solver::canonicalRelationStateKey() const {
    std::string key = canonicalSearchKey();
    key.append("R|");

    std::unordered_map<ValueId, std::size_t> pairLabels;
    std::size_t nextLabel = 0;
    for (const ValueId value : assignment_) {
        if (value < 2) continue;
        const ValueId c = lattice_.complement(value);
        const ValueId root = std::min(value, c);
        if (pairLabels.emplace(root, nextLabel).second) ++nextLabel;
    }

    struct CanonicalValue {
        ValueId raw = UNASSIGNED_VALUE;
        std::size_t order = 0;
    };
    std::vector<CanonicalValue> values;
    values.reserve(lattice_.activeValueCount());
    values.push_back({BOTTOM_VALUE, 0});
    values.push_back({TOP_VALUE, 1});
    for (ValueId raw = 2;
         raw < static_cast<ValueId>(lattice_.activeValueCount());
         ++raw) {
        const ValueId c = lattice_.complement(raw);
        const ValueId root = std::min(raw, c);
        const auto it = pairLabels.find(root);
        if (it == pairLabels.end()) continue;
        const std::size_t side = raw == root ? 0 : 1;
        values.push_back({raw, 2 + 2 * it->second + side});
    }
    std::sort(values.begin(), values.end(), [](const auto& a, const auto& b) {
        return a.order < b.order;
    });

    for (const auto& cv : values) {
        key.append(std::to_string(lattice_.dimension(cv.raw))).push_back(',');
    }
    key.push_back('|');
    for (std::size_t i = 0; i < values.size(); ++i) {
        for (std::size_t j = i + 1; j < values.size(); ++j) {
            const Relation rel = lattice_.relation(values[i].raw, values[j].raw);
            key.push_back(static_cast<char>('0' + static_cast<int>(rel)));
        }
    }
    return key;
}

bool Solver::initializeFreshRelationState(
    FreshRelationState& state,
    std::vector<ChoiceChange>& undoLog
) {
    if (!forceUpperChoice(
            state, TOP_VALUE, RelationChoice::Included, undoLog) ||
        !forceUpperChoice(
            state, BOTTOM_VALUE, RelationChoice::Excluded, undoLog) ||
        !forceLowerChoice(
            state, BOTTOM_VALUE, RelationChoice::Included, undoLog) ||
        !forceLowerChoice(
            state, TOP_VALUE, RelationChoice::Excluded, undoLog)) {
        return false;
    }

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        const std::int32_t dim = lattice_.dimension(value);
        const std::int32_t a = static_cast<std::int32_t>(state.valueDimension);

        if (dim <= a) {
            if (!forceUpperChoice(
                    state, value, RelationChoice::Excluded, undoLog)) {
                return false;
            }
        }

        if (dim >= a) {
            if (!forceLowerChoice(
                    state, value, RelationChoice::Excluded, undoLog)) {
                return false;
            }
        }
    }

    if (!propagateRequiredLineMeets(state, undoLog)) {
        return false;
    }

    return validateFreshRelationState(state);
}

void Solver::initializeGoalRequirements() {
    requireLiteralNonzero(formula_.output());
}

void Solver::requireLiteralNonzero(Lit literal) {
    if (literal == TRUE_LIT || literal == FALSE_LIT) return;
    if (literal < 0) {
        requireLiteralNotTop(static_cast<Lit>(-literal));
        return;
    }

    const NodeId node = static_cast<NodeId>(literal);
    const std::size_t index = static_cast<std::size_t>(node);
    if (index >= mustBeNonzero_.size()) return;
    if (mustBeNonzero_[index]) return;
    mustBeNonzero_[index] = true;

    const AndGate* gate = index < gateByNode_.size() ? gateByNode_[index] : nullptr;
    if (gate == nullptr) return;

    if (std::find(requiredNonzeroMeetGates_.begin(),
                  requiredNonzeroMeetGates_.end(),
                  node) != requiredNonzeroMeetGates_.end()) {
    } else {
        requiredNonzeroMeetGates_.push_back(node);
    }

    requireLiteralNonzero(gate->lhs);
    requireLiteralNonzero(gate->rhs);
}

void Solver::requireLiteralNotTop(Lit literal) {
    if (literal == TRUE_LIT || literal == FALSE_LIT) return;
    if (literal < 0) {
        requireLiteralNonzero(static_cast<Lit>(-literal));
        return;
    }

    const NodeId node = static_cast<NodeId>(literal);
    const std::size_t index = static_cast<std::size_t>(node);
    if (index >= mustNotBeTop_.size()) return;
    mustNotBeTop_[index] = true;
}

ValueId Solver::directAssignedValue(Lit literal) const {
    if (literal == TRUE_LIT) return TOP_VALUE;
    if (literal == FALSE_LIT) return BOTTOM_VALUE;

    const bool negated = literal < 0;
    const NodeId node = static_cast<NodeId>(std::abs(literal));
    const auto it = variableIndexByNode_.find(node);
    if (it == variableIndexByNode_.end()) return UNASSIGNED_VALUE;

    const ValueId value = assignment_[it->second];
    if (value == UNASSIGNED_VALUE) return UNASSIGNED_VALUE;
    return negated ? lattice_.complement(value) : value;
}

bool Solver::forceRequiredContainment(
    FreshRelationState& state,
    ValueId lower,
    ValueId upper,
    std::vector<ChoiceChange>& undoLog
) {
    if (lower == upper || lower == BOTTOM_VALUE || upper == TOP_VALUE) return true;
    if (lower == TOP_VALUE || upper == BOTTOM_VALUE) return false;

    const ValueId p = state.pair.value;
    const ValueId pPerp = state.pair.complement;
    const auto isOld = [&](ValueId value) {
        return value >= 0 && static_cast<std::size_t>(value) < state.oldValueCount;
    };

    if (isOld(lower) && isOld(upper)) {
        const Relation relation = lattice_.relation(lower, upper);

        return relation == Relation::Below || relation == Relation::Undefined;
    }
    if (lower == p && isOld(upper)) {
        return forceUpperChoice(state, upper, RelationChoice::Included, undoLog);
    }
    if (isOld(lower) && upper == p) {
        return forceLowerChoice(state, lower, RelationChoice::Included, undoLog);
    }
    if (lower == pPerp && isOld(upper)) {
        const ValueId upperPerp = lattice_.complement(upper);
        if (!isOld(upperPerp)) return false;
        return forceLowerChoice(state, upperPerp, RelationChoice::Included, undoLog);
    }
    if (isOld(lower) && upper == pPerp) {
        const ValueId lowerPerp = lattice_.complement(lower);
        if (!isOld(lowerPerp)) return false;
        return forceUpperChoice(state, lowerPerp, RelationChoice::Included, undoLog);
    }
    if ((lower == p && upper == pPerp) ||
        (lower == pPerp && upper == p)) {
        return false;
    }

    return true;
}

bool Solver::propagateRequiredLineMeets(
    FreshRelationState& state,
    std::vector<ChoiceChange>& undoLog
) {
    for (const NodeId out : requiredNonzeroMeetGates_) {
        const AndGate* gate = gateByNode_[static_cast<std::size_t>(out)];
        if (gate == nullptr) continue;

        const ValueId lhs = directAssignedValue(gate->lhs);
        const ValueId rhs = directAssignedValue(gate->rhs);
        if (lhs == UNASSIGNED_VALUE || rhs == UNASSIGNED_VALUE) continue;
        if (lhs == BOTTOM_VALUE || rhs == BOTTOM_VALUE) return false;
        if (lhs == rhs || lhs == TOP_VALUE || rhs == TOP_VALUE) continue;

        if (lattice_.dimension(lhs) == 1 &&
            !forceRequiredContainment(state, lhs, rhs, undoLog)) {
            return false;
        }
        if (lattice_.dimension(rhs) == 1 &&
            !forceRequiredContainment(state, rhs, lhs, undoLog)) {
            return false;
        }
    }
    return true;
}

bool Solver::forceUpperChoice(
    FreshRelationState& state,
    ValueId value,
    RelationChoice choice,
    std::vector<ChoiceChange>& undoLog
) {
    if (value < 0 || static_cast<std::size_t>(value) >= state.oldValueCount) {
        throw std::out_of_range("fresh upper choice refers to a non-old value");
    }

    RelationChoice& current = choiceRef(state, false, value);
    if (current == choice) {
        return true;
    }
    if (current != RelationChoice::Undecided) {
        return false;
    }

    if (choice == RelationChoice::Included &&
        lattice_.dimension(value) <=
            static_cast<std::int32_t>(state.valueDimension)) {
        return false;
    }

    undoLog.push_back({false, value, current});
    current = choice;

    if (choice == RelationChoice::Included) {
        if (!forceLowerChoice(
                state, value, RelationChoice::Excluded, undoLog)) {
            return false;
        }

        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (lattice_.relation(value, other) == Relation::Below) {
                if (!forceUpperChoice(
                        state, other, RelationChoice::Included, undoLog)) {
                    return false;
                }
            }
        }

        for (ValueId lowerCandidate = 0;
             lowerCandidate < static_cast<ValueId>(state.oldValueCount);
             ++lowerCandidate) {
            if (getChoice(state, true, lowerCandidate) ==
                RelationChoice::Excluded) {
                continue;
            }
            if (lowerCandidate == value ||
                lattice_.relation(lowerCandidate, value) != Relation::Below) {
                if (!forceLowerChoice(
                        state,
                        lowerCandidate,
                        RelationChoice::Excluded,
                        undoLog)) {
                    return false;
                }
            }
        }

        const ValueId negated = lattice_.complement(value);
        if (static_cast<std::size_t>(negated) < state.oldValueCount) {
            if (!forceUpperChoice(
                    state, negated, RelationChoice::Excluded, undoLog)) {
                return false;
            }
        }
    } else if (choice == RelationChoice::Excluded) {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (lattice_.relation(other, value) == Relation::Below) {
                if (!forceUpperChoice(
                        state, other, RelationChoice::Excluded, undoLog)) {
                    return false;
                }
            }
        }
    }

    return true;
}

bool Solver::forceLowerChoice(
    FreshRelationState& state,
    ValueId value,
    RelationChoice choice,
    std::vector<ChoiceChange>& undoLog
) {
    if (value < 0 || static_cast<std::size_t>(value) >= state.oldValueCount) {
        throw std::out_of_range("fresh lower choice refers to a non-old value");
    }

    RelationChoice& current = choiceRef(state, true, value);
    if (current == choice) {
        return true;
    }
    if (current != RelationChoice::Undecided) {
        return false;
    }

    if (choice == RelationChoice::Included &&
        lattice_.dimension(value) >=
            static_cast<std::int32_t>(state.valueDimension)) {
        return false;
    }

    undoLog.push_back({true, value, current});
    current = choice;

    if (choice == RelationChoice::Included) {
        if (!forceUpperChoice(
                state, value, RelationChoice::Excluded, undoLog)) {
            return false;
        }

        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (lattice_.relation(other, value) == Relation::Below) {
                if (!forceLowerChoice(
                        state, other, RelationChoice::Included, undoLog)) {
                    return false;
                }
            }
        }

        for (ValueId upperCandidate = 0;
             upperCandidate < static_cast<ValueId>(state.oldValueCount);
             ++upperCandidate) {
            if (getChoice(state, false, upperCandidate) ==
                RelationChoice::Excluded) {
                continue;
            }
            if (upperCandidate == value ||
                lattice_.relation(value, upperCandidate) != Relation::Below) {
                if (!forceUpperChoice(
                        state,
                        upperCandidate,
                        RelationChoice::Excluded,
                        undoLog)) {
                    return false;
                }
            }
        }

        const ValueId negated = lattice_.complement(value);
        if (static_cast<std::size_t>(negated) < state.oldValueCount) {
            if (!forceLowerChoice(
                    state, negated, RelationChoice::Excluded, undoLog)) {
                return false;
            }
        }
    } else if (choice == RelationChoice::Excluded) {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (lattice_.relation(value, other) == Relation::Below) {
                if (!forceLowerChoice(
                        state, other, RelationChoice::Excluded, undoLog)) {
                    return false;
                }
            }
        }
    }

    return true;
}

std::size_t Solver::relationDecisionImpact(
    const FreshRelationState& state,
    bool lowerSide,
    ValueId value
) const {
    std::size_t includedImpact = 1;
    std::size_t excludedImpact = 1;

    if (!lowerSide) {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) continue;

            if (getChoice(state, false, other) == RelationChoice::Undecided) {
                if (lattice_.relation(value, other) == Relation::Below) {
                    ++includedImpact;
                }
                if (lattice_.relation(other, value) == Relation::Below) {
                    ++excludedImpact;
                }
            }

            if (getChoice(state, true, other) == RelationChoice::Undecided &&
                lattice_.relation(other, value) != Relation::Below) {
                ++includedImpact;
            }
        }

        const ValueId negated = lattice_.complement(value);
        if (negated >= 0 &&
            static_cast<std::size_t>(negated) < state.oldValueCount &&
            getChoice(state, false, negated) == RelationChoice::Undecided) {
            ++includedImpact;
        }
    } else {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) continue;

            if (getChoice(state, true, other) == RelationChoice::Undecided) {
                if (lattice_.relation(other, value) == Relation::Below) {
                    ++includedImpact;
                }
                if (lattice_.relation(value, other) == Relation::Below) {
                    ++excludedImpact;
                }
            }

            if (getChoice(state, false, other) == RelationChoice::Undecided &&
                lattice_.relation(value, other) != Relation::Below) {
                ++includedImpact;
            }
        }

        const ValueId negated = lattice_.complement(value);
        if (negated >= 0 &&
            static_cast<std::size_t>(negated) < state.oldValueCount &&
            getChoice(state, true, negated) == RelationChoice::Undecided) {
            ++includedImpact;
        }
    }

    return std::min(includedImpact, excludedImpact) * 4 +
           includedImpact + excludedImpact;
}

ValueId Solver::nextUndecidedUpper(const FreshRelationState& state) const {
    ValueId best = UNASSIGNED_VALUE;
    std::size_t bestImpact = 0;
    std::int32_t bestDimension = std::numeric_limits<std::int32_t>::max();

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (state.aboveValue[static_cast<std::size_t>(value)] !=
            RelationChoice::Undecided) {
            continue;
        }

        const std::size_t impact = relationDecisionImpact(state, false, value);
        const std::int32_t dim = lattice_.dimension(value);
        if (best == UNASSIGNED_VALUE || impact > bestImpact ||
            (impact == bestImpact && dim < bestDimension)) {
            best = value;
            bestImpact = impact;
            bestDimension = dim;
        }
    }

    return best;
}

ValueId Solver::nextUndecidedLower(const FreshRelationState& state) const {
    ValueId best = UNASSIGNED_VALUE;
    std::size_t bestImpact = 0;
    std::int32_t bestDimension = -1;

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (state.belowValue[static_cast<std::size_t>(value)] !=
            RelationChoice::Undecided) {
            continue;
        }

        const std::size_t impact = relationDecisionImpact(state, true, value);
        const std::int32_t dim = lattice_.dimension(value);
        if (best == UNASSIGNED_VALUE || impact > bestImpact ||
            (impact == bestImpact && dim > bestDimension)) {
            best = value;
            bestImpact = impact;
            bestDimension = dim;
        }
    }

    return best;
}

bool Solver::validateFreshRelationState(const FreshRelationState& state) const {
    const std::vector<ValueId> upperA = includedValues(state, false);
    const std::vector<ValueId> lowerA = includedValues(state, true);

    const std::vector<ValueId> upperNotA = complementedValues(lattice_, lowerA);
    const std::vector<ValueId> lowerNotA = complementedValues(lattice_, upperA);

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        const RelationChoice upper = getChoice(state, false, value);
        const RelationChoice lower = getChoice(state, true, value);

        if (upper == RelationChoice::Included &&
            lower == RelationChoice::Included) {
            return false;
        }

        const ValueId negated = lattice_.complement(value);
        if (static_cast<std::size_t>(negated) >= state.oldValueCount) {
            continue;
        }

        if (upper == RelationChoice::Included &&
            getChoice(state, false, negated) == RelationChoice::Included) {
            return false;
        }
        if (lower == RelationChoice::Included &&
            getChoice(state, true, negated) == RelationChoice::Included) {
            return false;
        }
    }

    const auto boundsCompatible = [&](const std::vector<ValueId>& lowers,
                                      const std::vector<ValueId>& uppers) {
        for (const ValueId lower : lowers) {
            for (const ValueId upper : uppers) {
                if (lower == upper) {
                    return false;
                }

                const Relation relation = lattice_.relation(lower, upper);
                if (relation == Relation::Above ||
                    relation == Relation::Incomparable) {
                    return false;
                }
            }
        }
        return true;
    };

    if (!boundsCompatible(lowerA, upperA) ||
        !boundsCompatible(lowerNotA, upperNotA)) {
        return false;
    }

    const DimensionRange meetA = structuralMeet(upperA);
    const DimensionRange joinA = structuralJoin(lowerA);
    const DimensionRange meetNotA = structuralMeet(upperNotA);
    const DimensionRange joinNotA = structuralJoin(lowerNotA);

    const std::int32_t a = static_cast<std::int32_t>(state.valueDimension);
    const std::int32_t notA =
        static_cast<std::int32_t>(state.complementDimension);

    if (meetA.max < a || joinA.min > a) {
        return false;
    }
    if (meetNotA.max < notA || joinNotA.min > notA) {
        return false;
    }

    return true;
}

SolveResult Solver::completeDeferredRelations(ValueId pairValue) {
    if (pairValue >= static_cast<ValueId>(lattice_.activeValueCount())) {
        ++stats_.deferredRelationCompletions;
        return evaluateCompleteAssignment();
    }
    if (pairValue < 2 || (pairValue & 1) != 0 ||
        pairValue + 1 >= static_cast<ValueId>(lattice_.activeValueCount())) {
        throw std::logic_error("invalid deferred relation pair");
    }

    FreshRelationState state;
    state.pair = {pairValue, pairValue + 1};
    state.oldValueCount = static_cast<std::size_t>(pairValue);
    state.valueDimension = static_cast<std::uint32_t>(lattice_.dimension(pairValue));
    state.complementDimension =
        static_cast<std::uint32_t>(lattice_.dimension(pairValue + 1));
    state.aboveValue.assign(state.oldValueCount, RelationChoice::Undecided);
    state.belowValue.assign(state.oldValueCount, RelationChoice::Undecided);

    std::vector<ChoiceChange> undoLog;
    undoLog.reserve(4 * state.oldValueCount);
    if (!initializeFreshRelationState(state, undoLog)) {
        ++stats_.prunedRelationBranches;
        return SolveResult::Unsat;
    }
    return enumerateDeferredRelations(pairValue, state, undoLog);
}

SolveResult Solver::completeRequestedRelation(ValueId lhs, ValueId rhs) {
    if (lhs == rhs) return evaluateCompleteAssignment();
    if (lhs > rhs) std::swap(lhs, rhs);

    if (lhs < 0 || rhs < 0 ||
        static_cast<std::size_t>(rhs) >= lattice_.activeValueCount()) {
        return SolveResult::Unknown;
    }
    if (lattice_.relation(lhs, rhs) != Relation::Undefined) {
        return evaluateCompleteAssignment();
    }

    ++stats_.demandedRelationPairs;

    const ValueId rhsComplement = lattice_.complement(rhs);
    ValueId pairValue = std::min(rhs, rhsComplement);
    if (pairValue < 2 || (pairValue & 1) != 0) {
        const ValueId lhsComplement = lattice_.complement(lhs);
        pairValue = std::min(lhs, lhsComplement);
    }
    if (pairValue < 2 || (pairValue & 1) != 0 ||
        pairValue + 1 >= static_cast<ValueId>(lattice_.activeValueCount())) {
        return SolveResult::Unknown;
    }

    return completeDeferredRelations(pairValue);
}

SolveResult Solver::enumerateDeferredRelations(
    ValueId pairValue,
    FreshRelationState& state,
    std::vector<ChoiceChange>& undoLog
) {
    if (!validateFreshRelationState(state)) {
        ++stats_.prunedRelationBranches;
        return SolveResult::Unsat;
    }

    const ValueId upper = nextUndecidedUpper(state);
    const ValueId lower = nextUndecidedLower(state);
    if (upper == UNASSIGNED_VALUE && lower == UNASSIGNED_VALUE) {
        ++stats_.relationConfigurations;
        return commitDeferredRelationConfiguration(state);
    }

    bool lowerSide = false;
    ValueId decisionValue = upper;
    if (upper == UNASSIGNED_VALUE) {
        lowerSide = true;
        decisionValue = lower;
    } else if (lower != UNASSIGNED_VALUE) {
        const std::size_t upperImpact =
            relationDecisionImpact(state, false, upper);
        const std::size_t lowerImpact =
            relationDecisionImpact(state, true, lower);
        if (lowerImpact > upperImpact) {
            lowerSide = true;
            decisionValue = lower;
        } else if (lowerImpact == upperImpact) {
            const std::int32_t a =
                static_cast<std::int32_t>(state.valueDimension);
            const std::int32_t upperGap = lattice_.dimension(upper) - a;
            const std::int32_t lowerGap = a - lattice_.dimension(lower);
            if (lowerGap < upperGap) {
                lowerSide = true;
                decisionValue = lower;
            }
        }
    }

    SolveResult result = SolveResult::Unsat;
    for (RelationChoice decision : {
             RelationChoice::Included,
             RelationChoice::Excluded
         }) {
        ++stats_.relationDecisions;
        if (lowerSide) ++stats_.lowerRelationDecisions;
        else ++stats_.upperRelationDecisions;

        const std::size_t checkpoint = undoLog.size();
        const bool consistent = lowerSide
            ? forceLowerChoice(state, decisionValue, decision, undoLog)
            : forceUpperChoice(state, decisionValue, decision, undoLog);

        if (consistent && validateFreshRelationState(state)) {
            const SolveResult branch = enumerateDeferredRelations(
                pairValue,
                state,
                undoLog
            );
            rollbackChoices(state, undoLog, checkpoint);
            if (branch == SolveResult::Sat) return SolveResult::Sat;
            result = combine(result, branch);
        } else {
            ++stats_.prunedRelationBranches;
            rollbackChoices(state, undoLog, checkpoint);
        }
    }
    return result;
}

SolveResult Solver::commitDeferredRelationConfiguration(
    const FreshRelationState& state
) {
    struct RelationSnapshot {
        ValueId oldValue;
        Relation valueRelation;
        Relation complementRelation;
    };

    std::vector<RelationSnapshot> snapshots;
    snapshots.reserve(state.oldValueCount);
    for (ValueId oldValue = 0;
         oldValue < static_cast<ValueId>(state.oldValueCount);
         ++oldValue) {
        snapshots.push_back({
            oldValue,
            lattice_.relation(state.pair.value, oldValue),
            lattice_.relation(state.pair.complement, oldValue)
        });

        Relation valueRelation = Relation::Incomparable;
        if (getChoice(state, false, oldValue) == RelationChoice::Included) {
            valueRelation = Relation::Below;
        } else if (getChoice(state, true, oldValue) == RelationChoice::Included) {
            valueRelation = Relation::Above;
        }

        const ValueId oldComplement = lattice_.complement(oldValue);
        Relation complementRelation = Relation::Incomparable;
        if (getChoice(state, true, oldComplement) == RelationChoice::Included) {
            complementRelation = Relation::Below;
        } else if (getChoice(state, false, oldComplement) == RelationChoice::Included) {
            complementRelation = Relation::Above;
        }

        lattice_.setRelation(state.pair.value, oldValue, valueRelation);
        lattice_.setRelation(
            state.pair.complement,
            oldValue,
            complementRelation
        );
    }

    SolveResult result = SolveResult::Unsat;

    if (!outputMayBeNonzero()) {
        ++stats_.partialDimensionPrunes;
    } else {
        result = evaluateCompleteAssignment();
    }

    for (const RelationSnapshot& snapshot : snapshots) {
        if (snapshot.valueRelation == Relation::Undefined) {
            lattice_.clearRelation(state.pair.value, snapshot.oldValue);
        } else {
            lattice_.setRelation(
                state.pair.value,
                snapshot.oldValue,
                snapshot.valueRelation
            );
        }
        if (snapshot.complementRelation == Relation::Undefined) {
            lattice_.clearRelation(state.pair.complement, snapshot.oldValue);
        } else {
            lattice_.setRelation(
                state.pair.complement,
                snapshot.oldValue,
                snapshot.complementRelation
            );
        }
    }
    return result;
}

void Solver::rollbackChoices(
    FreshRelationState& state,
    std::vector<ChoiceChange>& undoLog,
    std::size_t checkpoint
) {
    while (undoLog.size() > checkpoint) {
        const ChoiceChange change = undoLog.back();
        undoLog.pop_back();
        choiceRef(state, change.lowerSide, change.value) = change.previous;
    }
}

Solver::RelationChoice Solver::getChoice(
    const FreshRelationState& state,
    bool lowerSide,
    ValueId value
) {
    const auto& choices = lowerSide
        ? state.belowValue
        : state.aboveValue;
    return choices.at(static_cast<std::size_t>(value));
}

Solver::RelationChoice& Solver::choiceRef(
    FreshRelationState& state,
    bool lowerSide,
    ValueId value
) {
    auto& choices = lowerSide
        ? state.belowValue
        : state.aboveValue;
    return choices.at(static_cast<std::size_t>(value));
}

bool Solver::isKnownLessOrEqual(ValueId lhs, ValueId rhs) const {
    if (lhs == rhs) {
        return true;
    }
    return lattice_.relation(lhs, rhs) == Relation::Below;
}

bool Solver::areKnownOrthogonal(ValueId lhs, ValueId rhs) const {
    if (lhs == BOTTOM_VALUE || rhs == BOTTOM_VALUE) return true;
    const ValueId lhsPerp = lattice_.complement(lhs);
    const ValueId rhsPerp = lattice_.complement(rhs);
    return isKnownLessOrEqual(lhs, rhsPerp) ||
           isKnownLessOrEqual(rhs, lhsPerp);
}

std::int32_t Solver::smallestKnownCommonUpperDimension(
    const std::vector<ValueId>& values
) const {
    if (values.empty()) {
        return static_cast<std::int32_t>(lattice_.hilbertDimension());
    }

    std::int32_t best = static_cast<std::int32_t>(lattice_.hilbertDimension());

    for (ValueId candidate = 0;
         candidate < static_cast<ValueId>(lattice_.activeValueCount());
         ++candidate) {
        bool commonUpper = true;
        for (const ValueId value : values) {
            if (!isKnownLessOrEqual(value, candidate)) {
                commonUpper = false;
                break;
            }
        }

        if (commonUpper) {
            best = std::min(best, lattice_.dimension(candidate));
        }
    }

    return best;
}

std::int32_t Solver::largestKnownCommonLowerDimension(
    const std::vector<ValueId>& values
) const {
    if (values.empty()) {
        return 0;
    }

    std::int32_t best = 0;

    for (ValueId candidate = 0;
         candidate < static_cast<ValueId>(lattice_.activeValueCount());
         ++candidate) {
        bool commonLower = true;
        for (const ValueId value : values) {
            if (!isKnownLessOrEqual(candidate, value)) {
                commonLower = false;
                break;
            }
        }

        if (commonLower) {
            best = std::max(best, lattice_.dimension(candidate));
        }
    }

    return best;
}

Solver::DimensionRange Solver::structuralMeet(
    const std::vector<ValueId>& values
) const {
    const std::int32_t n =
        static_cast<std::int32_t>(lattice_.hilbertDimension());

    if (values.empty()) {
        return {n, n};
    }

    std::int32_t upper = n;
    std::int64_t dimensionSum = 0;

    for (const ValueId value : values) {
        const std::int32_t dim = lattice_.dimension(value);
        upper = std::min(upper, dim);
        dimensionSum += dim;
    }

    const std::int32_t ambient = smallestKnownCommonUpperDimension(values);
    const std::int32_t knownLower = largestKnownCommonLowerDimension(values);

    const std::int64_t kMinusOne =
        static_cast<std::int64_t>(values.size() - 1);
    const std::int64_t grassmann =
        dimensionSum - kMinusOne * static_cast<std::int64_t>(ambient);

    std::int32_t lower = std::max<std::int32_t>(
        knownLower,
        static_cast<std::int32_t>(std::max<std::int64_t>(0, grassmann))
    );

    for (std::size_t i = 0; i < values.size(); ++i) {
        for (std::size_t j = i + 1; j < values.size(); ++j) {
            const ValueId lhs = values[i];
            const ValueId rhs = values[j];

            if (lhs == rhs) {
                continue;
            }

            if (areKnownOrthogonal(lhs, rhs)) {
                upper = 0;
                continue;
            }

            const std::int32_t lhsDim = lattice_.dimension(lhs);
            const std::int32_t rhsDim = lattice_.dimension(rhs);

            if (lhsDim == rhsDim) {
                upper = std::min(
                    upper,
                    std::max<std::int32_t>(0, lhsDim - 1)
                );
            }

            const Relation relation = lattice_.relation(lhs, rhs);
            switch (relation) {
                case Relation::Below:
                    upper = std::min(upper, lhsDim);
                    break;
                case Relation::Above:
                    upper = std::min(upper, rhsDim);
                    break;
                case Relation::Incomparable:
                    upper = std::min(
                        upper,
                        std::max<std::int32_t>(0, std::min(lhsDim, rhsDim) - 1)
                    );
                    break;
                case Relation::Undefined:
                    break;
            }
        }
    }

    lower = std::min(lower, n);
    upper = std::max<std::int32_t>(0, upper);

    return {lower, upper};
}

Solver::DimensionRange Solver::structuralJoin(
    const std::vector<ValueId>& values
) const {
    const std::int32_t n =
        static_cast<std::int32_t>(lattice_.hilbertDimension());

    if (values.empty()) {
        return {0, 0};
    }

    const std::vector<ValueId> complements =
        complementedValues(lattice_, values);
    const DimensionRange complementMeet = structuralMeet(complements);

    return {
        n - complementMeet.max,
        n - complementMeet.min
    };
}

std::vector<ValueId> Solver::includedValues(
    const FreshRelationState& state,
    bool lowerSide
) const {
    std::vector<ValueId> result;
    result.reserve(state.oldValueCount);

    const auto& choices = lowerSide
        ? state.belowValue
        : state.aboveValue;

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (choices[static_cast<std::size_t>(value)] == RelationChoice::Included) {
            result.push_back(value);
        }
    }

    return result;
}

std::vector<ValueId> Solver::complementedValues(
    const Lattice& lattice,
    const std::vector<ValueId>& values
) {
    std::vector<ValueId> result;
    result.reserve(values.size());

    for (const ValueId value : values) {
        result.push_back(lattice.complement(value));
    }

    return result;
}

SolveResult Solver::evaluateCompleteAssignment() {
    std::string relationKey;

    const bool useRelationMemo =
        !keepWitness_ && stats_.relationConfigurations >= 2000;
    if (useRelationMemo) {
        relationKey = canonicalRelationStateKey();
        if (const auto it = relationMemo_.find(relationKey);
            it != relationMemo_.end()) {
            ++stats_.memoHits;
            ++stats_.relationStateMemoHits;
            return it->second;
        }
    }

    std::vector<ValueId> nodeValues(
        static_cast<std::size_t>(formula_.maxNodeId()) + 1,
        UNASSIGNED_VALUE
    );

    for (std::size_t i = 0; i < variables_.size(); ++i) {
        nodeValues[static_cast<std::size_t>(variables_[i].node)] =
            assignment_[i];
    }

    AbstractWitness candidateWitness;
    Evaluator evaluator(
        formula_,
        lattice_,
        std::move(nodeValues),
        &candidateWitness
    );

    SolveResult result = SolveResult::Unknown;
    switch (evaluator.evaluate()) {
        case EvaluationResult::Sat:
            if (keepWitness_) {
                witness_ = std::move(candidateWitness);
            }
            result = SolveResult::Sat;
            break;
        case EvaluationResult::Unsat:
            result = SolveResult::Unsat;
            break;
        case EvaluationResult::Unknown:
            if (const auto requested = evaluator.neededBaseRelation()) {
                result = completeRequestedRelation(
                    requested->first,
                    requested->second
                );
            } else if (
                mode_ != SolveMode::FastOnly &&
                candidateWitness.hilbertDimension == formula_.dimension() &&
                !candidateWitness.dimensions.empty()
            ) {
                ExactWitnessTheorySolver theory(formula_, candidateWitness);
                const ExactTheoryResult exactResult = theory.solve();
                const ExactTheoryStats& exact = theory.stats();
                stats_.exactTheoryCalls += exact.backendCalls;
                stats_.exactTheoryRealVariables += exact.realVariables;
                stats_.exactTheoryEqualities += exact.polynomialEqualities;
                stats_.exactTheoryInequalities += exact.polynomialInequalities;
                stats_.exactTheorySmtBytes += exact.smtBytes;

                if (exactResult == ExactTheoryResult::Sat) {
                    ++stats_.exactTheorySat;

                    witness_.reset();
                    result = SolveResult::Sat;
                } else {
                    ++stats_.exactTheoryUnsat;
                    result = SolveResult::Unsat;
                }
            } else {
                result = SolveResult::Unknown;
            }
            break;
    }

    if (useRelationMemo) {
        relationMemo_[std::move(relationKey)] = result;
        ++stats_.memoStores;
        ++stats_.relationStateMemoStores;
    }
    return result;
}

SolveResult Solver::combine(
    SolveResult accumulated,
    SolveResult branch
) noexcept {
    if (accumulated == SolveResult::Sat || branch == SolveResult::Sat) {
        return SolveResult::Sat;
    }
    if (accumulated == SolveResult::Unknown || branch == SolveResult::Unknown) {
        return SolveResult::Unknown;
    }
    return SolveResult::Unsat;
}

const char* toString(SolveResult result) noexcept {
    switch (result) {
        case SolveResult::Sat:
            return "SAT";
        case SolveResult::Unsat:
            return "UNSAT";
        case SolveResult::Unknown:
            return "UNKNOWN";
    }

    return "UNKNOWN";
}
}
