#pragma once

#include "Lattice.hpp"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

namespace ql {
class GeneratedLattice {
public:
    struct Checkpoint {
        std::size_t operationFactCount = 0;
    };

    GeneratedLattice(const Lattice& base, std::size_t additionalPairs);

    std::uint32_t hilbertDimension() const noexcept;
    std::size_t baseValueCount() const noexcept;
    std::size_t activeValueCount() const noexcept;

    std::int32_t dimension(ValueId value) const;
    ValueId complement(ValueId value) const;
    Relation relation(ValueId lhs, ValueId rhs) const;

    ValuePair pushValuePair(std::uint32_t dimension);
    void popValuePair();
    void setRelation(ValueId lhs, ValueId rhs, Relation relation);

    Checkpoint checkpoint() const noexcept;
    void rollback(Checkpoint checkpoint);

    bool assertMeet(ValueId lhs, ValueId rhs, ValueId result);
    bool assertJoin(ValueId lhs, ValueId rhs, ValueId result);

    bool consistent() const;
    bool equivalent(ValueId lhs, ValueId rhs) const;
    ValueId canonical(ValueId value) const;
    bool lessOrEqual(ValueId lhs, ValueId rhs) const;

    std::optional<ValueId> knownMeet(ValueId lhs, ValueId rhs) const;
    std::optional<ValueId> knownJoin(ValueId lhs, ValueId rhs) const;

    struct Quotient {
        bool consistent = false;
        std::size_t baseValueCount = 0;
        std::vector<std::int32_t> dimensions;
        std::vector<ValueId> complements;
        std::vector<Relation> relations;
        std::vector<ValueId> oldToNew;
    };

    Quotient quotient() const;

private:
    enum class Operation : std::uint8_t { Meet, Join };

    struct OperationFact {
        Operation operation = Operation::Meet;
        ValueId lhs = UNASSIGNED_VALUE;
        ValueId rhs = UNASSIGNED_VALUE;
        ValueId result = UNASSIGNED_VALUE;
    };

    struct Closure {
        bool consistent = true;
        std::vector<ValueId> parent;
        std::vector<std::uint8_t> rank;
        std::vector<std::vector<bool>> leq;
        std::vector<OperationFact> facts;
    };

    std::uint32_t hilbertDimension_ = 0;
    std::size_t baseValueCount_ = 0;
    std::size_t maxValues_ = 0;
    std::size_t activeValues_ = 0;

    std::vector<std::int32_t> dimensions_;
    std::vector<ValueId> complements_;
    std::vector<Relation> relations_;
    std::vector<OperationFact> operationFacts_;

    mutable std::optional<Closure> cachedClosure_;

    void invalidateClosure() noexcept;
    Closure& closure() const;

    std::size_t index(ValueId lhs, ValueId rhs) const;
    void requireActive(ValueId value) const;
    static Relation inverse(Relation relation) noexcept;
    void clearValue(ValueId value);

    Closure computeClosure() const;
    void refineClosure(Closure& closure) const;
    OperationFact dualFact(const OperationFact& fact) const;
    static ValueId find(Closure& closure, ValueId value);
    static ValueId findConst(const Closure& closure, ValueId value);
    bool unite(Closure& closure, ValueId lhs, ValueId rhs) const;

    void rebuildOrder(Closure& closure) const;
    bool applyOperationCongruence(Closure& closure) const;
    bool applyComplementCongruence(Closure& closure) const;
    bool applyDimensionOrderEqualities(Closure& closure) const;
    bool applyAssociativity(Closure& closure) const;
    bool applyModularity(Closure& closure) const;
    bool applyOrthomodularity(Closure& closure) const;
    bool applyDimensionDistributivity(Closure& closure) const;
    bool validateClosure(Closure& closure) const;

    std::optional<ValueId> lookupOperation(
        Closure& closure,
        Operation operation,
        ValueId lhs,
        ValueId rhs
    ) const;
};
}
