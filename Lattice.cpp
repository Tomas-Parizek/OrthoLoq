#include "Lattice.hpp"

#include <stdexcept>
#include <string>

namespace ql {
Lattice::Lattice(std::uint32_t hilbertDimension, std::size_t maxValues)
    : hilbertDimension_(hilbertDimension),
      maxValues_(maxValues),
      dimensions_(maxValues, UNDEFINED_DIMENSION),
      complements_(maxValues, UNASSIGNED_VALUE),
      relations_(maxValues * maxValues, Relation::Undefined) {
    if (hilbertDimension == 0) {
        throw std::invalid_argument("Hilbert dimension must be positive");
    }
    if (maxValues < 2) {
        throw std::invalid_argument("lattice capacity must be at least 2");
    }

    dimensions_[BOTTOM_VALUE] = 0;
    dimensions_[TOP_VALUE] = static_cast<std::int32_t>(hilbertDimension_);
    complements_[BOTTOM_VALUE] = TOP_VALUE;
    complements_[TOP_VALUE] = BOTTOM_VALUE;

    setRelation(BOTTOM_VALUE, TOP_VALUE, Relation::Below);
}

std::uint32_t Lattice::hilbertDimension() const noexcept {
    return hilbertDimension_;
}

std::size_t Lattice::activeValueCount() const noexcept {
    return activeValues_;
}

std::size_t Lattice::capacity() const noexcept {
    return maxValues_;
}

bool Lattice::isActive(ValueId value) const noexcept {
    return value >= 0 && static_cast<std::size_t>(value) < activeValues_;
}

std::int32_t Lattice::dimension(ValueId value) const {
    requireActive(value);
    return dimensions_[static_cast<std::size_t>(value)];
}

ValueId Lattice::complement(ValueId value) const {
    requireActive(value);
    return complements_[static_cast<std::size_t>(value)];
}

Relation Lattice::relation(ValueId lhs, ValueId rhs) const {
    requireActive(lhs);
    requireActive(rhs);

    if (lhs == rhs) {
        return Relation::Undefined;
    }

    return relations_[index(lhs, rhs)];
}

ValuePair Lattice::pushValuePair(std::uint32_t dimension) {
    if (dimension == 0 || dimension >= hilbertDimension_) {
        throw std::invalid_argument(
            "a fresh lattice value must have dimension in 1..dim(H)-1"
        );
    }
    if (activeValues_ + 2 > maxValues_) {
        throw std::runtime_error("lattice capacity exhausted");
    }

    const ValueId value = static_cast<ValueId>(activeValues_);
    const ValueId negated = value + 1;

    initializeValue(value, dimension, negated);
    initializeValue(negated, hilbertDimension_ - dimension, value);
    activeValues_ += 2;

    installBoundsFor(value);
    installBoundsFor(negated);
    setRelation(value, negated, Relation::Incomparable);

    return {value, negated};
}

void Lattice::popValuePair() {
    if (activeValues_ <= 2) {
        throw std::logic_error("cannot remove 0/1 from lattice");
    }

    const ValueId negated = static_cast<ValueId>(activeValues_ - 1);
    const ValueId value = negated - 1;

    if (complement(value) != negated || complement(negated) != value) {
        throw std::logic_error("last lattice values are not a complement pair");
    }

    clearValue(negated);
    clearValue(value);
    activeValues_ -= 2;
}

void Lattice::setRelation(ValueId lhs, ValueId rhs, Relation relationValue) {
    requireActive(lhs);
    requireActive(rhs);

    if (lhs == rhs) {
        throw std::invalid_argument("equality is not stored as a lattice relation");
    }
    if (relationValue == Relation::Undefined) {
        clearRelation(lhs, rhs);
        return;
    }

    relations_[index(lhs, rhs)] = relationValue;
    relations_[index(rhs, lhs)] = inverse(relationValue);
}

void Lattice::clearRelation(ValueId lhs, ValueId rhs) {
    requireActive(lhs);
    requireActive(rhs);

    if (lhs == rhs) {
        return;
    }

    relations_[index(lhs, rhs)] = Relation::Undefined;
    relations_[index(rhs, lhs)] = Relation::Undefined;
}

std::size_t Lattice::index(ValueId lhs, ValueId rhs) const {
    return static_cast<std::size_t>(lhs) * maxValues_ +
           static_cast<std::size_t>(rhs);
}

void Lattice::requireActive(ValueId value) const {
    if (!isActive(value)) {
        throw std::out_of_range("inactive lattice ValueId " + std::to_string(value));
    }
}

Relation Lattice::inverse(Relation relationValue) noexcept {
    switch (relationValue) {
        case Relation::Below:
            return Relation::Above;
        case Relation::Above:
            return Relation::Below;
        case Relation::Incomparable:
            return Relation::Incomparable;
        case Relation::Undefined:
            return Relation::Undefined;
    }

    return Relation::Undefined;
}

void Lattice::initializeValue(
    ValueId value,
    std::uint32_t dimensionValue,
    ValueId complementValue
) {
    dimensions_[static_cast<std::size_t>(value)] =
        static_cast<std::int32_t>(dimensionValue);
    complements_[static_cast<std::size_t>(value)] = complementValue;
}

void Lattice::clearValue(ValueId value) {
    const std::size_t v = static_cast<std::size_t>(value);

    for (std::size_t other = 0; other < maxValues_; ++other) {
        relations_[v * maxValues_ + other] = Relation::Undefined;
        relations_[other * maxValues_ + v] = Relation::Undefined;
    }

    dimensions_[v] = UNDEFINED_DIMENSION;
    complements_[v] = UNASSIGNED_VALUE;
}

void Lattice::installBoundsFor(ValueId value) {
    if (value != BOTTOM_VALUE) {
        setRelation(BOTTOM_VALUE, value, Relation::Below);
    }
    if (value != TOP_VALUE) {
        setRelation(value, TOP_VALUE, Relation::Below);
    }
}

const char* toString(Relation relationValue) noexcept {
    switch (relationValue) {
        case Relation::Undefined:
            return "undefined";
        case Relation::Below:
            return "below";
        case Relation::Above:
            return "above";
        case Relation::Incomparable:
            return "incomparable";
    }

    return "undefined";
}
}
