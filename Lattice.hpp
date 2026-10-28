#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

namespace ql {
using ValueId = std::int32_t;

inline constexpr ValueId BOTTOM_VALUE = 0;
inline constexpr ValueId TOP_VALUE = 1;
inline constexpr ValueId UNASSIGNED_VALUE = -1;
inline constexpr std::int32_t UNDEFINED_DIMENSION = -1;

enum class Relation : std::uint8_t {
    Undefined,
    Below,
    Above,
    Incomparable
};

struct ValuePair {
    ValueId value;
    ValueId complement;
};

class Lattice {
public:
    Lattice(std::uint32_t hilbertDimension, std::size_t maxValues);

    std::uint32_t hilbertDimension() const noexcept;
    std::size_t activeValueCount() const noexcept;
    std::size_t capacity() const noexcept;

    bool isActive(ValueId value) const noexcept;

    std::int32_t dimension(ValueId value) const;
    ValueId complement(ValueId value) const;
    Relation relation(ValueId lhs, ValueId rhs) const;

    ValuePair pushValuePair(std::uint32_t dimension);

    void popValuePair();

    void setRelation(ValueId lhs, ValueId rhs, Relation relation);
    void clearRelation(ValueId lhs, ValueId rhs);

private:
    std::uint32_t hilbertDimension_;
    std::size_t maxValues_;
    std::size_t activeValues_ = 2;

    std::vector<std::int32_t> dimensions_;
    std::vector<ValueId> complements_;
    std::vector<Relation> relations_;

    std::size_t index(ValueId lhs, ValueId rhs) const;
    void requireActive(ValueId value) const;
    static Relation inverse(Relation relation) noexcept;

    void initializeValue(ValueId value, std::uint32_t dimension, ValueId complement);
    void clearValue(ValueId value);
    void installBoundsFor(ValueId value);
};

const char* toString(Relation relation) noexcept;
}
