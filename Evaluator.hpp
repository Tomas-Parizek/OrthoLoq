#pragma once

#include "Aig.hpp"
#include "GeneratedLattice.hpp"
#include "Lattice.hpp"
#include "Witness.hpp"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

namespace ql {
enum class EvaluationResult : std::uint8_t {
    Sat,
    Unsat,
    Unknown
};

class Evaluator {
public:
    Evaluator(
        const Formula& formula,
        const Lattice& baseLattice,
        std::vector<ValueId> nodeValues,
        AbstractWitness* witnessOut = nullptr
    );

    EvaluationResult evaluate();

    std::optional<std::pair<ValueId, ValueId>> neededBaseRelation() const noexcept;

private:
    enum class Choice : std::uint8_t {
        Undecided,
        Included,
        Excluded
    };

    struct DimensionRange {
        std::int32_t min = 0;
        std::int32_t max = 0;
    };

    struct MeetState {
        ValueId lhs = UNASSIGNED_VALUE;
        ValueId rhs = UNASSIGNED_VALUE;
        std::int32_t dimension = UNDEFINED_DIMENSION;
        std::size_t oldValueCount = 0;

        std::vector<bool> commonLower;

        std::vector<Choice> above;
    };

    struct ChoiceChange {
        ValueId value = UNASSIGNED_VALUE;
        Choice previous = Choice::Undecided;
    };

    const Formula& formula_;
    GeneratedLattice structure_;
    std::vector<ValueId> nodeValues_;
    std::vector<const AndGate*> gateByNode_;
    std::vector<bool> mustBeNonzero_;
    std::vector<bool> mustNotBeTop_;
    std::optional<std::pair<ValueId, ValueId>> neededBaseRelation_;
    AbstractWitness* witnessOut_ = nullptr;

    void initializeGoalRequirements();
    void requireLiteralNonzero(Lit literal);
    void requireLiteralNotTop(Lit literal);
    bool gateResultAllowed(NodeId out, ValueId value) const;

    EvaluationResult evaluateGate(std::size_t gateIndex);
    EvaluationResult recurseWithGateMeet(
        std::size_t gateIndex,
        ValueId lhs,
        ValueId rhs,
        ValueId value
    );

    EvaluationResult enumerateMeet(
        std::size_t gateIndex,
        ValueId lhs,
        ValueId rhs
    );

    EvaluationResult enumerateFreshMeetUpper(
        std::size_t gateIndex,
        MeetState& state,
        std::vector<ChoiceChange>& undoLog
    );

    EvaluationResult commitFreshMeet(
        std::size_t gateIndex,
        const MeetState& state
    );

    bool initializeMeetState(
        MeetState& state,
        std::vector<ChoiceChange>& undoLog
    );

    bool forceAboveChoice(
        MeetState& state,
        ValueId value,
        Choice choice,
        std::vector<ChoiceChange>& undoLog
    );

    bool validateMeetState(const MeetState& state) const;
    ValueId nextUndecidedAbove(const MeetState& state) const;

    static void rollbackChoices(
        MeetState& state,
        std::vector<ChoiceChange>& undoLog,
        std::size_t checkpoint
    );

    ValueId valueOfLiteral(Lit literal) const;

    bool isLessOrEqual(ValueId lhs, ValueId rhs) const;
    std::vector<ValueId> commonLowerValues(ValueId lhs, ValueId rhs) const;
    std::vector<ValueId> includedUpperValues(const MeetState& state) const;

    ValueId existingMeetCandidate(
        const std::vector<ValueId>& commonLower,
        std::int32_t dimension
    ) const;

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

    std::vector<ValueId> complementedValues(
        const std::vector<ValueId>& values
    ) const;

    bool newValueRelationsConsistent(
        ValueId value,
        std::size_t oldValueCount
    ) const;

    bool requestBaseRelation(ValueId lhs, ValueId rhs);
    bool requestAnyUndefinedBaseRelation();
    bool requestMissingMeetDownsetRelation(ValueId lhs, ValueId rhs);
    EvaluationResult finish();
    AbstractWitness snapshotWitness() const;

    static EvaluationResult combine(
        EvaluationResult accumulated,
        EvaluationResult branch
    ) noexcept;
};

const char* toString(EvaluationResult result) noexcept;
}
