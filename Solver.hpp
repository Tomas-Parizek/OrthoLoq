#pragma once

#include "Aig.hpp"
#include "Lattice.hpp"
#include "ExactTheory.hpp"
#include "Witness.hpp"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace ql {
enum class SolveResult : std::uint8_t {
    Sat,
    Unsat,
    Unknown
};

enum class SolveMode : std::uint8_t {
    Complete,
    FastOnly,
    ExactOnly
};

struct SolveStats {
    std::uint64_t recursiveCalls = 0;
    std::uint64_t branches = 0;
    std::uint64_t leaves = 0;
    std::uint64_t reusedValueBranches = 0;
    std::uint64_t freshValueBranches = 0;
    std::uint64_t relationDecisions = 0;
    std::uint64_t upperRelationDecisions = 0;
    std::uint64_t lowerRelationDecisions = 0;
    std::uint64_t relationConfigurations = 0;
    std::uint64_t prunedRelationBranches = 0;
    std::uint64_t structuralSubproblems = 0;
    std::uint64_t independentMeetSplits = 0;
    std::uint64_t topLevelJoinSplits = 0;
    std::uint64_t partialDimensionPrunes = 0;
    std::uint64_t dimensionDomainPrunes = 0;
    std::uint64_t memoHits = 0;
    std::uint64_t memoStores = 0;
    std::uint64_t demandedRelationPairs = 0;
    std::uint64_t relationStateMemoHits = 0;
    std::uint64_t relationStateMemoStores = 0;
    std::uint64_t deferredRelationCompletions = 0;
    std::uint64_t theoremPatternHits = 0;
    std::uint64_t symmetryDimensionPrunes = 0;
    std::uint64_t exactTheoryCalls = 0;
    std::uint64_t exactTheorySat = 0;
    std::uint64_t exactTheoryUnsat = 0;
    std::uint64_t exactTheoryRealVariables = 0;
    std::uint64_t exactTheoryEqualities = 0;
    std::uint64_t exactTheoryInequalities = 0;
    std::uint64_t exactTheorySmtBytes = 0;
    std::uint64_t adaptiveExactHandoffs = 0;
    std::size_t maxActiveValues = 0;
};

class Solver {
public:
    explicit Solver(
        const Formula& formula,
        bool keepWitness = false,
        SolveMode mode = SolveMode::Complete
    );

    SolveResult solve();

    const SolveStats& stats() const noexcept;
    const Lattice& lattice() const noexcept;
    const AbstractWitness* witness() const noexcept;

private:
    struct Variable {
        std::string name;
        NodeId node;
    };

    enum class RelationChoice : std::uint8_t {
        Undecided,
        Included,
        Excluded
    };

    struct FreshRelationState {
        ValuePair pair{};
        std::size_t oldValueCount = 0;
        std::uint32_t valueDimension = 0;
        std::uint32_t complementDimension = 0;

        std::vector<RelationChoice> aboveValue;
        std::vector<RelationChoice> belowValue;
    };

    struct ChoiceChange {
        bool lowerSide = false;
        ValueId value = UNASSIGNED_VALUE;
        RelationChoice previous = RelationChoice::Undecided;
    };

    struct DimensionRange {
        std::int32_t min = 0;
        std::int32_t max = 0;
    };

    struct PartialInfo {
        DimensionRange dimension{};
        ValueId knownValue = UNASSIGNED_VALUE;
        bool possible = true;
    };

    struct VariableSelection {
        std::size_t index = 0;
        std::vector<bool> allowedDimensions;
    };

    const Formula& formula_;
    std::vector<Variable> variables_;
    std::vector<ValueId> assignment_;
    std::unordered_map<NodeId, std::size_t> variableIndexByNode_;
    std::vector<const AndGate*> gateByNode_;
    std::vector<std::size_t> occurrenceWeight_;
    std::vector<std::vector<std::size_t>> interactionWeight_;
    std::vector<std::int32_t> symmetryOrbit_;
    std::vector<std::int32_t> symmetryPosition_;
    std::vector<NodeId> requiredNonzeroMeetGates_;
    std::vector<bool> mustBeNonzero_;
    std::vector<bool> mustNotBeTop_;
    std::unordered_map<std::string, SolveResult> memo_;
    std::unordered_map<std::string, SolveResult> relationMemo_;
    Lattice lattice_;
    SolveStats stats_;
    bool keepWitness_ = false;
    SolveMode mode_ = SolveMode::Complete;
    std::optional<AbstractWitness> witness_;
    std::optional<SolveResult> globalExactDecision_;

    SolveResult solveStructurally(bool& applied);
    SolveResult solveFast();
    SolveResult solveCore();
    SolveResult solveExact();
    void accumulateStats(const SolveStats& other);

    SolveResult search(std::size_t assignedCount);
    SolveResult recurseWithAssignment(
        std::size_t assignedCount,
        std::size_t variableIndex,
        ValueId value
    );

    VariableSelection chooseNextVariable();
    bool dimensionSymmetryAllowed(std::size_t variableIndex, std::int32_t dimension) const;
    bool outputMayBeNonzero(
        std::optional<std::pair<std::size_t, std::int32_t>> dimensionOverride = std::nullopt
    ) const;
    PartialInfo partialInfo(
        Lit literal,
        std::optional<std::pair<std::size_t, std::int32_t>> dimensionOverride,
        std::vector<std::optional<PartialInfo>>& memo
    ) const;
    std::string canonicalSearchKey() const;
    std::string canonicalRelationStateKey() const;

    SolveResult completeRequestedRelation(ValueId lhs, ValueId rhs);

    SolveResult completeDeferredRelations(ValueId pairValue);
    SolveResult enumerateDeferredRelations(
        ValueId pairValue,
        FreshRelationState& state,
        std::vector<ChoiceChange>& undoLog
    );
    SolveResult commitDeferredRelationConfiguration(
        const FreshRelationState& state
    );

    bool initializeFreshRelationState(
        FreshRelationState& state,
        std::vector<ChoiceChange>& undoLog
    );

    void initializeGoalRequirements();
    void requireLiteralNonzero(Lit literal);
    void requireLiteralNotTop(Lit literal);
    ValueId directAssignedValue(Lit literal) const;
    bool forceRequiredContainment(
        FreshRelationState& state,
        ValueId lower,
        ValueId upper,
        std::vector<ChoiceChange>& undoLog
    );
    bool propagateRequiredLineMeets(
        FreshRelationState& state,
        std::vector<ChoiceChange>& undoLog
    );

    bool forceUpperChoice(
        FreshRelationState& state,
        ValueId value,
        RelationChoice choice,
        std::vector<ChoiceChange>& undoLog
    );

    bool forceLowerChoice(
        FreshRelationState& state,
        ValueId value,
        RelationChoice choice,
        std::vector<ChoiceChange>& undoLog
    );

    bool validateFreshRelationState(const FreshRelationState& state) const;

    static void rollbackChoices(
        FreshRelationState& state,
        std::vector<ChoiceChange>& undoLog,
        std::size_t checkpoint
    );

    static RelationChoice getChoice(
        const FreshRelationState& state,
        bool lowerSide,
        ValueId value
    );

    static RelationChoice& choiceRef(
        FreshRelationState& state,
        bool lowerSide,
        ValueId value
    );

    ValueId nextUndecidedUpper(const FreshRelationState& state) const;
    ValueId nextUndecidedLower(const FreshRelationState& state) const;
    std::size_t relationDecisionImpact(
        const FreshRelationState& state,
        bool lowerSide,
        ValueId value
    ) const;

    bool isKnownLessOrEqual(ValueId lhs, ValueId rhs) const;
    bool areKnownOrthogonal(ValueId lhs, ValueId rhs) const;
    std::int32_t smallestKnownCommonUpperDimension(
        const std::vector<ValueId>& values
    ) const;
    std::int32_t largestKnownCommonLowerDimension(
        const std::vector<ValueId>& values
    ) const;

    DimensionRange structuralMeet(
        const std::vector<ValueId>& values
    ) const;
    DimensionRange structuralJoin(
        const std::vector<ValueId>& values
    ) const;

    std::vector<ValueId> includedValues(
        const FreshRelationState& state,
        bool lowerSide
    ) const;

    static std::vector<ValueId> complementedValues(
        const Lattice& lattice,
        const std::vector<ValueId>& values
    );

    SolveResult evaluateCompleteAssignment();

    static SolveResult combine(SolveResult accumulated, SolveResult branch) noexcept;
};

const char* toString(SolveResult result) noexcept;
}
