#pragma once

#include "Lattice.hpp"

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace ql {
struct AbstractWitness {
    std::uint32_t hilbertDimension = 0;
    std::size_t baseValueCount = 0;

    std::vector<std::int32_t> dimensions;
    std::vector<ValueId> complements;
    std::vector<Relation> relations;
    std::vector<ValueId> nodeValues;

    std::size_t valueCount() const noexcept {
        return dimensions.size();
    }

    Relation relation(ValueId lhs, ValueId rhs) const {
        if (lhs == rhs) {
            return Relation::Undefined;
        }
        if (lhs < 0 || rhs < 0 ||
            static_cast<std::size_t>(lhs) >= valueCount() ||
            static_cast<std::size_t>(rhs) >= valueCount()) {
            throw std::out_of_range("witness ValueId out of range");
        }
        return relations[
            static_cast<std::size_t>(lhs) * valueCount() +
            static_cast<std::size_t>(rhs)
        ];
    }
};
}
