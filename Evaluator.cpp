#include "Evaluator.hpp"
#include "LatticeCertificate.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>

namespace ql {
Evaluator::Evaluator(
    const Formula& formula,
    const Lattice& baseLattice,
    std::vector<ValueId> nodeValues,
    AbstractWitness* witnessOut
)
    : formula_(formula),
      structure_(baseLattice, formula.gates().size()),
      nodeValues_(std::move(nodeValues)),
      witnessOut_(witnessOut) {
    const std::size_t required =
        static_cast<std::size_t>(formula_.maxNodeId()) + 1;
    if (nodeValues_.size() < required) {
        nodeValues_.resize(required, UNASSIGNED_VALUE);
    }

    gateByNode_.assign(required, nullptr);
    for (const AndGate& gate : formula_.gates()) {
        gateByNode_[static_cast<std::size_t>(gate.out)] = &gate;
    }
    mustBeNonzero_.assign(required, false);
    mustNotBeTop_.assign(required, false);
    initializeGoalRequirements();
}

void Evaluator::initializeGoalRequirements() {
    requireLiteralNonzero(formula_.output());
}

void Evaluator::requireLiteralNonzero(Lit literal) {
    if (literal == TRUE_LIT || literal == FALSE_LIT) return;

    if (literal < 0) {
        requireLiteralNotTop(static_cast<Lit>(-literal));
        return;
    }

    const NodeId node = static_cast<NodeId>(literal);
    const std::size_t index = static_cast<std::size_t>(node);

    if (mustBeNonzero_[index]) return;
    mustBeNonzero_[index] = true;

    const AndGate* gate = index < gateByNode_.size() ? gateByNode_[index] : nullptr;
    if (gate == nullptr) return;

    requireLiteralNonzero(gate->lhs);
    requireLiteralNonzero(gate->rhs);
}

void Evaluator::requireLiteralNotTop(Lit literal) {
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

bool Evaluator::gateResultAllowed(NodeId out, ValueId value) const {
    const std::size_t index = static_cast<std::size_t>(out);
    const std::int32_t dim = structure_.dimension(value);
    if (index < mustBeNonzero_.size() && mustBeNonzero_[index] && dim == 0) {
        return false;
    }
    if (index < mustNotBeTop_.size() && mustNotBeTop_[index] &&
        dim == static_cast<std::int32_t>(structure_.hilbertDimension())) {
        return false;
    }
    return true;
}

EvaluationResult Evaluator::evaluate() {
    neededBaseRelation_.reset();
    return evaluateGate(0);
}

std::optional<std::pair<ValueId, ValueId>>
Evaluator::neededBaseRelation() const noexcept {
    return neededBaseRelation_;
}

EvaluationResult Evaluator::evaluateGate(std::size_t gateIndex) {
    if (gateIndex == formula_.gates().size()) {
        return finish();
    }

    const AndGate& gate = formula_.gates()[gateIndex];
    const ValueId lhs = valueOfLiteral(gate.lhs);
    const ValueId rhs = valueOfLiteral(gate.rhs);

    if (lhs == UNASSIGNED_VALUE || rhs == UNASSIGNED_VALUE) {
        return EvaluationResult::Unknown;
    }

    return enumerateMeet(gateIndex, lhs, rhs);
}

EvaluationResult Evaluator::recurseWithGateMeet(
    std::size_t gateIndex,
    ValueId lhs,
    ValueId rhs,
    ValueId value
) {
    const NodeId out = formula_.gates()[gateIndex].out;
    const std::size_t index = static_cast<std::size_t>(out);

    if (!gateResultAllowed(out, value)) {
        return EvaluationResult::Unsat;
    }

    if (nodeValues_[index] != UNASSIGNED_VALUE) {
        throw std::logic_error("AIG gate output is already evaluated");
    }

    const GeneratedLattice::Checkpoint checkpoint = structure_.checkpoint();
    if (!structure_.assertMeet(lhs, rhs, value)) {
        structure_.rollback(checkpoint);
        return EvaluationResult::Unsat;
    }

    const ValueId canonicalValue = structure_.canonical(value);
    nodeValues_[index] = canonicalValue;
    const EvaluationResult result = evaluateGate(gateIndex + 1);
    nodeValues_[index] = UNASSIGNED_VALUE;
    structure_.rollback(checkpoint);
    return result;
}

EvaluationResult Evaluator::enumerateMeet(
    std::size_t gateIndex,
    ValueId lhs,
    ValueId rhs
) {
    if (!structure_.consistent()) {
        return EvaluationResult::Unsat;
    }

    lhs = structure_.canonical(lhs);
    rhs = structure_.canonical(rhs);

    if (const auto known = structure_.knownMeet(lhs, rhs)) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, *known);
    }

    if (lhs == BOTTOM_VALUE || rhs == BOTTOM_VALUE) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, BOTTOM_VALUE);
    }
    if (lhs == TOP_VALUE) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, rhs);
    }
    if (rhs == TOP_VALUE) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, lhs);
    }
    if (lhs == rhs) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, lhs);
    }
    if (structure_.complement(lhs) == rhs ||
        structure_.lessOrEqual(lhs, structure_.complement(rhs)) ||
        structure_.lessOrEqual(rhs, structure_.complement(lhs))) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, BOTTOM_VALUE);
    }

    const Relation relation = structure_.relation(lhs, rhs);
    if (relation == Relation::Below) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, lhs);
    }
    if (relation == Relation::Above) {
        return recurseWithGateMeet(gateIndex, lhs, rhs, rhs);
    }
    if (relation == Relation::Undefined) {
        requestBaseRelation(lhs, rhs);
        return EvaluationResult::Unknown;
    }

    if (requestMissingMeetDownsetRelation(lhs, rhs)) {
        return EvaluationResult::Unknown;
    }

    const std::vector<ValueId> commonLower = commonLowerValues(lhs, rhs);
    DimensionRange range = structuralMeet({lhs, rhs});

    const NodeId out = formula_.gates()[gateIndex].out;
    const std::size_t outIndex = static_cast<std::size_t>(out);
    if (outIndex < mustBeNonzero_.size() && mustBeNonzero_[outIndex]) {
        range.min = std::max<std::int32_t>(range.min, 1);
    }
    if (outIndex < mustNotBeTop_.size() && mustNotBeTop_[outIndex]) {
        range.max = std::min<std::int32_t>(
            range.max,
            static_cast<std::int32_t>(structure_.hilbertDimension()) - 1
        );
    }

    if (range.min > range.max) {
        return EvaluationResult::Unsat;
    }

    EvaluationResult result = EvaluationResult::Unsat;

    for (std::int32_t dimensionValue = range.min;
         dimensionValue <= range.max;
         ++dimensionValue) {
        const ValueId existing = existingMeetCandidate(
            commonLower,
            dimensionValue
        );

        if (existing != UNASSIGNED_VALUE) {
            const EvaluationResult branch =
                recurseWithGateMeet(gateIndex, lhs, rhs, existing);
            if (branch == EvaluationResult::Sat) {
                return branch;
            }
            result = combine(result, branch);

            continue;
        }

        if (dimensionValue <= 0 ||
            dimensionValue >=
                static_cast<std::int32_t>(structure_.hilbertDimension())) {
            continue;
        }

        bool freshPossible = true;
        for (const ValueId lower : commonLower) {
            if (structure_.dimension(lower) >= dimensionValue) {
                freshPossible = false;
                break;
            }
        }
        if (!freshPossible) {
            continue;
        }

        MeetState state;
        state.lhs = lhs;
        state.rhs = rhs;
        state.dimension = dimensionValue;
        state.oldValueCount = structure_.activeValueCount();
        state.commonLower.assign(state.oldValueCount, false);
        state.above.assign(state.oldValueCount, Choice::Undecided);

        for (const ValueId lower : commonLower) {
            state.commonLower[static_cast<std::size_t>(lower)] = true;
        }

        std::vector<ChoiceChange> undoLog;
        undoLog.reserve(2 * state.oldValueCount);

        EvaluationResult branch = EvaluationResult::Unsat;
        if (initializeMeetState(state, undoLog)) {
            branch = enumerateFreshMeetUpper(gateIndex, state, undoLog);
        }

        if (branch == EvaluationResult::Sat) {
            return branch;
        }
        result = combine(result, branch);
    }

    return result;
}

bool Evaluator::initializeMeetState(
    MeetState& state,
    std::vector<ChoiceChange>& undoLog
) {
    if (!forceAboveChoice(state, TOP_VALUE, Choice::Included, undoLog) ||
        !forceAboveChoice(state, BOTTOM_VALUE, Choice::Excluded, undoLog)) {
        return false;
    }

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (structure_.dimension(value) <= state.dimension) {
            if (!forceAboveChoice(
                    state, value, Choice::Excluded, undoLog)) {
                return false;
            }
        }

        if (state.commonLower[static_cast<std::size_t>(value)]) {
            if (!forceAboveChoice(
                    state, value, Choice::Excluded, undoLog)) {
                return false;
            }
        }
    }

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (isLessOrEqual(state.lhs, value) ||
            isLessOrEqual(state.rhs, value)) {
            if (!forceAboveChoice(
                    state, value, Choice::Included, undoLog)) {
                return false;
            }
        }
    }

    return validateMeetState(state);
}

bool Evaluator::forceAboveChoice(
    MeetState& state,
    ValueId value,
    Choice choice,
    std::vector<ChoiceChange>& undoLog
) {
    if (value < 0 || static_cast<std::size_t>(value) >= state.oldValueCount) {
        throw std::out_of_range("meet upper choice refers to a non-old value");
    }

    Choice& current = state.above[static_cast<std::size_t>(value)];
    if (current == choice) {
        return true;
    }
    if (current != Choice::Undecided) {
        return false;
    }

    if (choice == Choice::Included) {
        if (structure_.dimension(value) <= state.dimension) {
            return false;
        }
        if (state.commonLower[static_cast<std::size_t>(value)]) {
            return false;
        }
    }

    undoLog.push_back({value, current});
    current = choice;

    if (choice == Choice::Included) {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (structure_.relation(value, other) == Relation::Below) {
                if (!forceAboveChoice(
                        state, other, Choice::Included, undoLog)) {
                    return false;
                }
            }
        }

        const ValueId negated = structure_.complement(value);
        if (static_cast<std::size_t>(negated) < state.oldValueCount) {
            if (!forceAboveChoice(
                    state, negated, Choice::Excluded, undoLog)) {
                return false;
            }
        }
    } else {
        for (ValueId other = 0;
             other < static_cast<ValueId>(state.oldValueCount);
             ++other) {
            if (other == value) {
                continue;
            }
            if (structure_.relation(other, value) == Relation::Below) {
                if (!forceAboveChoice(
                        state, other, Choice::Excluded, undoLog)) {
                    return false;
                }
            }
        }
    }

    return true;
}

bool Evaluator::validateMeetState(const MeetState& state) const {
    const std::vector<ValueId> uppers = includedUpperValues(state);
    std::vector<ValueId> lowers;
    lowers.reserve(state.oldValueCount);

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (state.commonLower[static_cast<std::size_t>(value)]) {
            lowers.push_back(value);
        }
    }

    for (const ValueId lower : lowers) {
        for (const ValueId upper : uppers) {
            if (!isLessOrEqual(lower, upper)) {
                const Relation raw = structure_.relation(lower, upper);
                if (raw == Relation::Undefined) {
                    continue;
                }
                return false;
            }
        }
    }

    const DimensionRange upperMeet = structuralMeet(uppers);
    const DimensionRange lowerJoin = structuralJoin(lowers);

    if (upperMeet.max < state.dimension) {
        return false;
    }
    if (lowerJoin.min > state.dimension) {
        return false;
    }

    return true;
}

ValueId Evaluator::nextUndecidedAbove(const MeetState& state) const {
    ValueId best = UNASSIGNED_VALUE;
    std::int32_t bestDimension = std::numeric_limits<std::int32_t>::max();

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (state.above[static_cast<std::size_t>(value)] != Choice::Undecided) {
            continue;
        }

        const std::int32_t dim = structure_.dimension(value);
        if (dim < bestDimension) {
            best = value;
            bestDimension = dim;
        }
    }

    return best;
}

EvaluationResult Evaluator::enumerateFreshMeetUpper(
    std::size_t gateIndex,
    MeetState& state,
    std::vector<ChoiceChange>& undoLog
) {
    if (!validateMeetState(state)) {
        return EvaluationResult::Unsat;
    }

    const ValueId decisionValue = nextUndecidedAbove(state);
    if (decisionValue == UNASSIGNED_VALUE) {
        return commitFreshMeet(gateIndex, state);
    }

    EvaluationResult result = EvaluationResult::Unsat;

    for (const Choice decision : {Choice::Included, Choice::Excluded}) {
        const std::size_t checkpoint = undoLog.size();

        if (forceAboveChoice(state, decisionValue, decision, undoLog) &&
            validateMeetState(state)) {
            const EvaluationResult branch =
                enumerateFreshMeetUpper(gateIndex, state, undoLog);
            if (branch == EvaluationResult::Sat) {
                rollbackChoices(state, undoLog, checkpoint);
                return branch;
            }
            result = combine(result, branch);
        }

        rollbackChoices(state, undoLog, checkpoint);
    }

    return result;
}

EvaluationResult Evaluator::commitFreshMeet(
    std::size_t gateIndex,
    const MeetState& state
) {
    const ValuePair pair = structure_.pushValuePair(
        static_cast<std::uint32_t>(state.dimension)
    );

    for (ValueId oldValue = 0;
         oldValue < static_cast<ValueId>(state.oldValueCount);
         ++oldValue) {
        Relation relation = Relation::Incomparable;

        if (state.commonLower[static_cast<std::size_t>(oldValue)]) {
            relation = Relation::Above;
        } else if (
            state.above[static_cast<std::size_t>(oldValue)] == Choice::Included
        ) {
            relation = Relation::Below;
        }

        structure_.setRelation(pair.value, oldValue, relation);
    }

    for (ValueId oldValue = 0;
         oldValue < static_cast<ValueId>(state.oldValueCount);
         ++oldValue) {
        const ValueId oldComplement = structure_.complement(oldValue);
        const Relation mToComplement =
            structure_.relation(pair.value, oldComplement);

        Relation complementRelation = Relation::Incomparable;
        switch (mToComplement) {
            case Relation::Below:
                complementRelation = Relation::Above;
                break;
            case Relation::Above:
                complementRelation = Relation::Below;
                break;
            case Relation::Incomparable:
                complementRelation = Relation::Incomparable;
                break;
            case Relation::Undefined:
                structure_.popValuePair();
                return EvaluationResult::Unknown;
        }

        structure_.setRelation(
            pair.complement,
            oldValue,
            complementRelation
        );
    }

    EvaluationResult result = EvaluationResult::Unsat;

    if (newValueRelationsConsistent(pair.value, state.oldValueCount) &&
        newValueRelationsConsistent(pair.complement, state.oldValueCount)) {
        result = recurseWithGateMeet(
            gateIndex, state.lhs, state.rhs, pair.value
        );
    }

    structure_.popValuePair();
    return result;
}

void Evaluator::rollbackChoices(
    MeetState& state,
    std::vector<ChoiceChange>& undoLog,
    std::size_t checkpoint
) {
    while (undoLog.size() > checkpoint) {
        const ChoiceChange change = undoLog.back();
        undoLog.pop_back();
        state.above[static_cast<std::size_t>(change.value)] = change.previous;
    }
}

ValueId Evaluator::valueOfLiteral(Lit literal) const {
    if (literal == TRUE_LIT) {
        return TOP_VALUE;
    }
    if (literal == FALSE_LIT) {
        return BOTTOM_VALUE;
    }

    const NodeId node = literal < 0 ? -literal : literal;
    const std::size_t index = static_cast<std::size_t>(node);
    if (index >= nodeValues_.size()) {
        return UNASSIGNED_VALUE;
    }

    const ValueId value = nodeValues_[index];
    if (value == UNASSIGNED_VALUE) {
        return UNASSIGNED_VALUE;
    }

    const ValueId interpreted =
        literal < 0 ? structure_.complement(value) : value;
    return structure_.canonical(interpreted);
}

bool Evaluator::isLessOrEqual(ValueId lhs, ValueId rhs) const {
    return structure_.lessOrEqual(lhs, rhs);
}

std::vector<ValueId> Evaluator::commonLowerValues(
    ValueId lhs,
    ValueId rhs
) const {
    std::vector<ValueId> result;
    result.reserve(structure_.activeValueCount());

    for (ValueId candidate = 0;
         candidate < static_cast<ValueId>(structure_.activeValueCount());
         ++candidate) {
        if (isLessOrEqual(candidate, lhs) &&
            isLessOrEqual(candidate, rhs)) {
            result.push_back(candidate);
        }
    }

    return result;
}

std::vector<ValueId> Evaluator::includedUpperValues(
    const MeetState& state
) const {
    std::vector<ValueId> result;
    result.reserve(state.oldValueCount);

    for (ValueId value = 0;
         value < static_cast<ValueId>(state.oldValueCount);
         ++value) {
        if (state.above[static_cast<std::size_t>(value)] == Choice::Included) {
            result.push_back(value);
        }
    }

    return result;
}

ValueId Evaluator::existingMeetCandidate(
    const std::vector<ValueId>& commonLower,
    std::int32_t dimensionValue
) const {
    ValueId result = UNASSIGNED_VALUE;

    for (const ValueId candidate : commonLower) {
        if (structure_.dimension(candidate) != dimensionValue) {
            continue;
        }

        bool dominatesAllKnownLowers = true;
        for (const ValueId lower : commonLower) {
            if (!isLessOrEqual(lower, candidate)) {
                dominatesAllKnownLowers = false;
                break;
            }
        }

        if (!dominatesAllKnownLowers) {
            continue;
        }

        if (result != UNASSIGNED_VALUE && result != candidate) {
            return UNASSIGNED_VALUE;
        }
        result = candidate;
    }

    return result;
}

std::int32_t Evaluator::smallestKnownCommonUpperDimension(
    const std::vector<ValueId>& values
) const {
    if (values.empty()) {
        return static_cast<std::int32_t>(structure_.hilbertDimension());
    }

    std::int32_t best =
        static_cast<std::int32_t>(structure_.hilbertDimension());

    for (ValueId candidate = 0;
         candidate < static_cast<ValueId>(structure_.activeValueCount());
         ++candidate) {
        bool commonUpper = true;
        for (const ValueId value : values) {
            if (!isLessOrEqual(value, candidate)) {
                commonUpper = false;
                break;
            }
        }

        if (commonUpper) {
            best = std::min(best, structure_.dimension(candidate));
        }
    }

    return best;
}

std::int32_t Evaluator::largestKnownCommonLowerDimension(
    const std::vector<ValueId>& values
) const {
    if (values.empty()) {
        return 0;
    }

    std::int32_t best = 0;

    for (ValueId candidate = 0;
         candidate < static_cast<ValueId>(structure_.activeValueCount());
         ++candidate) {
        bool commonLower = true;
        for (const ValueId value : values) {
            if (!isLessOrEqual(candidate, value)) {
                commonLower = false;
                break;
            }
        }

        if (commonLower) {
            best = std::max(best, structure_.dimension(candidate));
        }
    }

    return best;
}

Evaluator::DimensionRange Evaluator::structuralMeet(
    const std::vector<ValueId>& values
) const {
    const std::int32_t n =
        static_cast<std::int32_t>(structure_.hilbertDimension());

    if (values.empty()) {
        return {n, n};
    }

    std::int32_t upper = n;
    std::int64_t dimensionSum = 0;

    for (const ValueId value : values) {
        const std::int32_t dim = structure_.dimension(value);
        upper = std::min(upper, dim);
        dimensionSum += dim;
    }

    const std::int32_t ambient = smallestKnownCommonUpperDimension(values);
    const std::int32_t knownLower = largestKnownCommonLowerDimension(values);

    const std::int64_t grassmann =
        dimensionSum -
        static_cast<std::int64_t>(values.size() - 1) *
            static_cast<std::int64_t>(ambient);

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
            if (structure_.complement(lhs) == rhs ||
                structure_.lessOrEqual(lhs, structure_.complement(rhs)) ||
                structure_.lessOrEqual(rhs, structure_.complement(lhs))) {
                upper = 0;
                continue;
            }

            const std::int32_t lhsDim = structure_.dimension(lhs);
            const std::int32_t rhsDim = structure_.dimension(rhs);

            switch (structure_.relation(lhs, rhs)) {
                case Relation::Below:
                    upper = std::min(upper, lhsDim);
                    break;
                case Relation::Above:
                    upper = std::min(upper, rhsDim);
                    break;
                case Relation::Incomparable:
                    upper = std::min(
                        upper,
                        std::max<std::int32_t>(
                            0,
                            std::min(lhsDim, rhsDim) - 1
                        )
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

Evaluator::DimensionRange Evaluator::structuralJoin(
    const std::vector<ValueId>& values
) const {
    const std::int32_t n =
        static_cast<std::int32_t>(structure_.hilbertDimension());

    if (values.empty()) {
        return {0, 0};
    }

    const DimensionRange complementMeet =
        structuralMeet(complementedValues(values));

    return {
        n - complementMeet.max,
        n - complementMeet.min
    };
}

std::vector<ValueId> Evaluator::complementedValues(
    const std::vector<ValueId>& values
) const {
    std::vector<ValueId> result;
    result.reserve(values.size());

    for (const ValueId value : values) {
        result.push_back(structure_.complement(value));
    }

    return result;
}

bool Evaluator::newValueRelationsConsistent(
    ValueId value,
    std::size_t oldValueCount
) const {
    std::vector<ValueId> lowers;
    std::vector<ValueId> uppers;

    for (ValueId oldValue = 0;
         oldValue < static_cast<ValueId>(oldValueCount);
         ++oldValue) {
        const Relation rel = structure_.relation(value, oldValue);
        if (rel == Relation::Below) {
            uppers.push_back(oldValue);
        } else if (rel == Relation::Above) {
            lowers.push_back(oldValue);
        } else if (rel == Relation::Undefined) {
            return false;
        }
    }

    for (const ValueId lower : lowers) {
        for (const ValueId upper : uppers) {
            if (!isLessOrEqual(lower, upper)) {
                const Relation raw = structure_.relation(lower, upper);
                if (raw == Relation::Undefined) continue;
                return false;
            }
        }
    }

    for (const ValueId upper : uppers) {
        for (ValueId candidate = 0;
             candidate < static_cast<ValueId>(oldValueCount);
             ++candidate) {
            if (structure_.relation(upper, candidate) == Relation::Below &&
                structure_.relation(value, candidate) != Relation::Below) {
                return false;
            }
        }
    }

    for (const ValueId lower : lowers) {
        for (ValueId candidate = 0;
             candidate < static_cast<ValueId>(oldValueCount);
             ++candidate) {
            if (structure_.relation(candidate, lower) == Relation::Below &&
                structure_.relation(value, candidate) != Relation::Above) {
                return false;
            }
        }
    }

    const std::int32_t dim = structure_.dimension(value);
    if (structuralMeet(uppers).max < dim) {
        return false;
    }
    if (structuralJoin(lowers).min > dim) {
        return false;
    }

    return true;
}

bool Evaluator::requestBaseRelation(ValueId lhs, ValueId rhs) {
    lhs = structure_.canonical(lhs);
    rhs = structure_.canonical(rhs);
    if (lhs == rhs) return false;

    const auto baseRepresentative = [&](ValueId value) -> ValueId {
        for (ValueId base = 0;
             base < static_cast<ValueId>(structure_.baseValueCount());
             ++base) {
            if (structure_.equivalent(base, value)) return base;
        }
        return UNASSIGNED_VALUE;
    };

    lhs = baseRepresentative(lhs);
    rhs = baseRepresentative(rhs);
    if (lhs == UNASSIGNED_VALUE || rhs == UNASSIGNED_VALUE || lhs == rhs) {
        return false;
    }
    if (lhs > rhs) std::swap(lhs, rhs);
    neededBaseRelation_ = std::pair{lhs, rhs};
    return true;
}

bool Evaluator::requestMissingMeetDownsetRelation(ValueId lhs, ValueId rhs) {
    const ValueId count = static_cast<ValueId>(structure_.activeValueCount());
    for (ValueId candidate = 0; candidate < count; ++candidate) {
        for (const ValueId operand : {lhs, rhs}) {
            if (candidate == operand) continue;

            if (structure_.lessOrEqual(candidate, operand) ||
                structure_.lessOrEqual(operand, candidate)) {
                continue;
            }

            if (structure_.relation(candidate, operand) != Relation::Undefined) {
                continue;
            }

            if (requestBaseRelation(candidate, operand)) return true;

            neededBaseRelation_.reset();
            return true;
        }
    }
    return false;
}

bool Evaluator::requestAnyUndefinedBaseRelation() {
    const ValueId count = static_cast<ValueId>(structure_.baseValueCount());
    for (ValueId lhs = 0; lhs < count; ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < count; ++rhs) {
            if (structure_.relation(lhs, rhs) != Relation::Undefined) continue;

            if (structure_.lessOrEqual(lhs, rhs) ||
                structure_.lessOrEqual(rhs, lhs)) {
                continue;
            }
            neededBaseRelation_ = std::pair{lhs, rhs};
            return true;
        }
    }
    return false;
}

EvaluationResult Evaluator::finish() {
    if (!structure_.consistent()) {
        return EvaluationResult::Unsat;
    }

    const ValueId output = valueOfLiteral(formula_.output());
    if (output == UNASSIGNED_VALUE) {
        return EvaluationResult::Unknown;
    }

    if (output == BOTTOM_VALUE) {
        return EvaluationResult::Unsat;
    }

    if (requestAnyUndefinedBaseRelation()) {
        return EvaluationResult::Unknown;
    }

    const AbstractWitness candidate = snapshotWitness();
    if (!LatticeCertificate::certify(formula_, candidate)) {
        if (witnessOut_ != nullptr) {
            *witnessOut_ = candidate;
        }
        return EvaluationResult::Unknown;
    }

    if (witnessOut_ != nullptr) {
        *witnessOut_ = candidate;
    }

    return EvaluationResult::Sat;
}

AbstractWitness Evaluator::snapshotWitness() const {
    AbstractWitness witness;
    const GeneratedLattice::Quotient quotient = structure_.quotient();
    if (!quotient.consistent) {
        return witness;
    }

    witness.hilbertDimension = structure_.hilbertDimension();
    witness.baseValueCount = quotient.baseValueCount;
    witness.dimensions = quotient.dimensions;
    witness.complements = quotient.complements;
    witness.relations = quotient.relations;
    witness.nodeValues.assign(nodeValues_.size(), UNASSIGNED_VALUE);

    for (std::size_t i = 0; i < nodeValues_.size(); ++i) {
        const ValueId old = nodeValues_[i];
        if (old == UNASSIGNED_VALUE) continue;
        if (old < 0 || static_cast<std::size_t>(old) >= quotient.oldToNew.size()) {
            continue;
        }
        witness.nodeValues[i] = quotient.oldToNew[static_cast<std::size_t>(old)];
    }
    return witness;
}

EvaluationResult Evaluator::combine(
    EvaluationResult accumulated,
    EvaluationResult branch
) noexcept {
    if (accumulated == EvaluationResult::Sat ||
        branch == EvaluationResult::Sat) {
        return EvaluationResult::Sat;
    }
    if (accumulated == EvaluationResult::Unknown ||
        branch == EvaluationResult::Unknown) {
        return EvaluationResult::Unknown;
    }
    return EvaluationResult::Unsat;
}

const char* toString(EvaluationResult result) noexcept {
    switch (result) {
        case EvaluationResult::Sat:
            return "SAT";
        case EvaluationResult::Unsat:
            return "UNSAT";
        case EvaluationResult::Unknown:
            return "UNKNOWN";
    }
    return "UNKNOWN";
}
}
