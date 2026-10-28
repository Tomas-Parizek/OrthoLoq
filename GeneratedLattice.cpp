#include "GeneratedLattice.hpp"

#include <algorithm>
#include <functional>
#include <map>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

namespace ql {
namespace {
using OpKey = std::tuple<std::uint8_t, ValueId, ValueId>;

OpKey keyFor(
    std::uint8_t operation,
    ValueId lhs,
    ValueId rhs
) {
    if (lhs > rhs) std::swap(lhs, rhs);
    return {operation, lhs, rhs};
}
}

GeneratedLattice::GeneratedLattice(
    const Lattice& base,
    std::size_t additionalPairs
)
    : hilbertDimension_(base.hilbertDimension()),
      baseValueCount_(base.activeValueCount()),
      maxValues_(base.activeValueCount() + 2 * additionalPairs),
      activeValues_(base.activeValueCount()),
      dimensions_(maxValues_, UNDEFINED_DIMENSION),
      complements_(maxValues_, UNASSIGNED_VALUE),
      relations_(maxValues_ * maxValues_, Relation::Undefined) {
    if (maxValues_ < 2) {
        throw std::logic_error("generated lattice capacity is invalid");
    }

    for (ValueId value = 0;
         value < static_cast<ValueId>(baseValueCount_);
         ++value) {
        dimensions_[static_cast<std::size_t>(value)] = base.dimension(value);
        complements_[static_cast<std::size_t>(value)] = base.complement(value);
    }

    for (ValueId lhs = 0;
         lhs < static_cast<ValueId>(baseValueCount_);
         ++lhs) {
        for (ValueId rhs = lhs + 1;
             rhs < static_cast<ValueId>(baseValueCount_);
             ++rhs) {
            const Relation rel = base.relation(lhs, rhs);
            relations_[index(lhs, rhs)] = rel;
            relations_[index(rhs, lhs)] = inverse(rel);
        }
    }
}

std::uint32_t GeneratedLattice::hilbertDimension() const noexcept {
    return hilbertDimension_;
}

std::size_t GeneratedLattice::baseValueCount() const noexcept {
    return baseValueCount_;
}

std::size_t GeneratedLattice::activeValueCount() const noexcept {
    return activeValues_;
}

std::int32_t GeneratedLattice::dimension(ValueId value) const {
    requireActive(value);
    return dimensions_[static_cast<std::size_t>(value)];
}

ValueId GeneratedLattice::complement(ValueId value) const {
    requireActive(value);
    return complements_[static_cast<std::size_t>(value)];
}

Relation GeneratedLattice::relation(ValueId lhs, ValueId rhs) const {
    requireActive(lhs);
    requireActive(rhs);
    if (lhs == rhs) return Relation::Undefined;
    return relations_[index(lhs, rhs)];
}

ValuePair GeneratedLattice::pushValuePair(std::uint32_t dimensionValue) {
    invalidateClosure();
    if (dimensionValue == 0 || dimensionValue >= hilbertDimension_) {
        throw std::invalid_argument(
            "a generated fresh value must be a proper non-zero subspace"
        );
    }
    if (activeValues_ + 2 > maxValues_) {
        throw std::runtime_error("generated lattice capacity exhausted");
    }

    const ValueId value = static_cast<ValueId>(activeValues_);
    const ValueId negated = value + 1;

    dimensions_[static_cast<std::size_t>(value)] =
        static_cast<std::int32_t>(dimensionValue);
    dimensions_[static_cast<std::size_t>(negated)] =
        static_cast<std::int32_t>(hilbertDimension_ - dimensionValue);
    complements_[static_cast<std::size_t>(value)] = negated;
    complements_[static_cast<std::size_t>(negated)] = value;

    activeValues_ += 2;

    setRelation(BOTTOM_VALUE, value, Relation::Below);
    setRelation(value, TOP_VALUE, Relation::Below);
    setRelation(BOTTOM_VALUE, negated, Relation::Below);
    setRelation(negated, TOP_VALUE, Relation::Below);
    setRelation(value, negated, Relation::Incomparable);

    return {value, negated};
}

void GeneratedLattice::popValuePair() {
    invalidateClosure();
    if (activeValues_ <= baseValueCount_) {
        throw std::logic_error("cannot pop a base generated-lattice value");
    }

    const ValueId negated = static_cast<ValueId>(activeValues_ - 1);
    const ValueId value = negated - 1;
    if (complement(value) != negated || complement(negated) != value) {
        throw std::logic_error("last generated values are not a complement pair");
    }

    for (const OperationFact& fact : operationFacts_) {
        if (fact.lhs >= value || fact.rhs >= value || fact.result >= value) {
            throw std::logic_error(
                "popValuePair with live operation fact; rollback first"
            );
        }
    }

    clearValue(negated);
    clearValue(value);
    activeValues_ -= 2;
}

void GeneratedLattice::setRelation(
    ValueId lhs,
    ValueId rhs,
    Relation relationValue
) {
    invalidateClosure();
    requireActive(lhs);
    requireActive(rhs);
    if (lhs == rhs) {
        throw std::invalid_argument("equality is not stored as a relation");
    }
    relations_[index(lhs, rhs)] = relationValue;
    relations_[index(rhs, lhs)] = inverse(relationValue);
}

GeneratedLattice::Checkpoint GeneratedLattice::checkpoint() const noexcept {
    return {operationFacts_.size()};
}

void GeneratedLattice::rollback(Checkpoint checkpointValue) {
    invalidateClosure();
    if (checkpointValue.operationFactCount > operationFacts_.size()) {
        throw std::logic_error("invalid generated-lattice checkpoint");
    }
    operationFacts_.resize(checkpointValue.operationFactCount);
}

bool GeneratedLattice::assertMeet(ValueId lhs, ValueId rhs, ValueId result) {
    requireActive(lhs);
    requireActive(rhs);
    requireActive(result);

    if (consistent()) {
        if (const auto known = knownMeet(lhs, rhs)) {
            if (canonical(*known) == canonical(result)) return true;
        }
    } else {
        return false;
    }

    const OperationFact fact{Operation::Meet, lhs, rhs, result};
    operationFacts_.push_back(fact);

    if (cachedClosure_) {
        cachedClosure_->facts.push_back(fact);
        cachedClosure_->facts.push_back(dualFact(fact));
        refineClosure(*cachedClosure_);
        return cachedClosure_->consistent;
    }
    return consistent();
}

bool GeneratedLattice::assertJoin(ValueId lhs, ValueId rhs, ValueId result) {
    requireActive(lhs);
    requireActive(rhs);
    requireActive(result);

    if (consistent()) {
        if (const auto known = knownJoin(lhs, rhs)) {
            if (canonical(*known) == canonical(result)) return true;
        }
    } else {
        return false;
    }

    const OperationFact fact{Operation::Join, lhs, rhs, result};
    operationFacts_.push_back(fact);
    if (cachedClosure_) {
        cachedClosure_->facts.push_back(fact);
        cachedClosure_->facts.push_back(dualFact(fact));
        refineClosure(*cachedClosure_);
        return cachedClosure_->consistent;
    }
    return consistent();
}

GeneratedLattice::OperationFact GeneratedLattice::dualFact(
    const OperationFact& fact
) const {
    return {
        fact.operation == Operation::Meet ? Operation::Join : Operation::Meet,
        complements_[static_cast<std::size_t>(fact.lhs)],
        complements_[static_cast<std::size_t>(fact.rhs)],
        complements_[static_cast<std::size_t>(fact.result)]
    };
}

std::size_t GeneratedLattice::index(ValueId lhs, ValueId rhs) const {
    return static_cast<std::size_t>(lhs) * maxValues_ +
           static_cast<std::size_t>(rhs);
}

void GeneratedLattice::requireActive(ValueId value) const {
    if (value < 0 || static_cast<std::size_t>(value) >= activeValues_) {
        throw std::out_of_range(
            "inactive generated ValueId " + std::to_string(value)
        );
    }
}

Relation GeneratedLattice::inverse(Relation relationValue) noexcept {
    switch (relationValue) {
        case Relation::Below: return Relation::Above;
        case Relation::Above: return Relation::Below;
        case Relation::Incomparable: return Relation::Incomparable;
        case Relation::Undefined: return Relation::Undefined;
    }
    return Relation::Undefined;
}

void GeneratedLattice::clearValue(ValueId value) {
    const std::size_t v = static_cast<std::size_t>(value);
    for (std::size_t other = 0; other < maxValues_; ++other) {
        relations_[v * maxValues_ + other] = Relation::Undefined;
        relations_[other * maxValues_ + v] = Relation::Undefined;
    }
    dimensions_[v] = UNDEFINED_DIMENSION;
    complements_[v] = UNASSIGNED_VALUE;
}

ValueId GeneratedLattice::find(Closure& closure, ValueId value) {
    ValueId& parent = closure.parent[static_cast<std::size_t>(value)];
    if (parent != value) parent = find(closure, parent);
    return parent;
}

ValueId GeneratedLattice::findConst(
    const Closure& closure,
    ValueId value
) {
    while (closure.parent[static_cast<std::size_t>(value)] != value) {
        value = closure.parent[static_cast<std::size_t>(value)];
    }
    return value;
}

bool GeneratedLattice::unite(
    Closure& closure,
    ValueId lhs,
    ValueId rhs
) const {
    lhs = find(closure, lhs);
    rhs = find(closure, rhs);
    if (lhs == rhs) return false;

    if (dimensions_[static_cast<std::size_t>(lhs)] !=
        dimensions_[static_cast<std::size_t>(rhs)]) {
        closure.consistent = false;
        return false;
    }

    auto& lhsRank = closure.rank[static_cast<std::size_t>(lhs)];
    auto& rhsRank = closure.rank[static_cast<std::size_t>(rhs)];
    if (lhsRank < rhsRank) std::swap(lhs, rhs);
    closure.parent[static_cast<std::size_t>(rhs)] = lhs;
    if (lhsRank == rhsRank) {
        ++closure.rank[static_cast<std::size_t>(lhs)];
    }
    return true;
}

void GeneratedLattice::rebuildOrder(Closure& closure) const {
    const std::size_t count = activeValues_;
    closure.leq.assign(count, std::vector<bool>(count, false));

    for (ValueId i = 0; i < static_cast<ValueId>(count); ++i) {
        closure.leq[static_cast<std::size_t>(i)][static_cast<std::size_t>(i)] = true;
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            const Relation rel = relations_[index(lhs, rhs)];
            if (rel == Relation::Below) {
                closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)] = true;
            } else if (rel == Relation::Above) {
                closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(lhs)] = true;
            }
        }
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (find(closure, lhs) == find(closure, rhs)) {
                closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)] = true;
                closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(lhs)] = true;
            }
        }
    }

    const auto transitiveClosure = [&]() {
        for (std::size_t k = 0; k < count; ++k) {
            for (std::size_t i = 0; i < count; ++i) {
                if (!closure.leq[i][k]) continue;
                for (std::size_t j = 0; j < count; ++j) {
                    if (closure.leq[k][j]) closure.leq[i][j] = true;
                }
            }
        }
    };

    for (const OperationFact& fact : closure.facts) {
        const ValueId lhs = find(closure, fact.lhs);
        const ValueId rhs = find(closure, fact.rhs);
        const ValueId result = find(closure, fact.result);
        if (fact.operation == Operation::Meet) {
            closure.leq[static_cast<std::size_t>(result)][static_cast<std::size_t>(lhs)] = true;
            closure.leq[static_cast<std::size_t>(result)][static_cast<std::size_t>(rhs)] = true;
        } else {
            closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(result)] = true;
            closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(result)] = true;
        }
    }
    transitiveClosure();

    bool changed = true;
    while (changed) {
        changed = false;
        for (const OperationFact& fact : closure.facts) {
            const ValueId lhs = find(closure, fact.lhs);
            const ValueId rhs = find(closure, fact.rhs);
            const ValueId result = find(closure, fact.result);

            if (fact.operation == Operation::Meet) {
                for (ValueId x = 0; x < static_cast<ValueId>(count); ++x) {
                    if (closure.leq[static_cast<std::size_t>(x)][static_cast<std::size_t>(lhs)] &&
                        closure.leq[static_cast<std::size_t>(x)][static_cast<std::size_t>(rhs)] &&
                        !closure.leq[static_cast<std::size_t>(x)][static_cast<std::size_t>(result)]) {
                        closure.leq[static_cast<std::size_t>(x)][static_cast<std::size_t>(result)] = true;
                        changed = true;
                    }
                }
            } else {
                for (ValueId x = 0; x < static_cast<ValueId>(count); ++x) {
                    if (closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(x)] &&
                        closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(x)] &&
                        !closure.leq[static_cast<std::size_t>(result)][static_cast<std::size_t>(x)]) {
                        closure.leq[static_cast<std::size_t>(result)][static_cast<std::size_t>(x)] = true;
                        changed = true;
                    }
                }
            }
        }
        if (changed) transitiveClosure();
    }
}

bool GeneratedLattice::applyComplementCongruence(Closure& closure) const {
    bool changed = false;
    const std::size_t count = activeValues_;
    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (find(closure, lhs) != find(closure, rhs)) continue;
            changed |= unite(
                closure,
                complements_[static_cast<std::size_t>(lhs)],
                complements_[static_cast<std::size_t>(rhs)]
            );
            if (!closure.consistent) return changed;
        }
    }
    return changed;
}

std::optional<ValueId> GeneratedLattice::lookupOperation(
    Closure& closure,
    Operation operation,
    ValueId lhs,
    ValueId rhs
) const {
    lhs = find(closure, lhs);
    rhs = find(closure, rhs);
    if (lhs > rhs) std::swap(lhs, rhs);

    const auto leq = [&](ValueId a, ValueId b) {
        return closure.leq[static_cast<std::size_t>(a)][static_cast<std::size_t>(b)];
    };

    if (lhs == rhs) return lhs;
    if (operation == Operation::Meet) {
        if (lhs == BOTTOM_VALUE || rhs == BOTTOM_VALUE) return BOTTOM_VALUE;
        if (lhs == TOP_VALUE) return rhs;
        if (rhs == TOP_VALUE) return lhs;
        const ValueId lhsPerp = find(
            closure, complements_[static_cast<std::size_t>(lhs)]
        );
        const ValueId rhsPerp = find(
            closure, complements_[static_cast<std::size_t>(rhs)]
        );
        if (lhsPerp == rhs || leq(lhs, rhsPerp) || leq(rhs, lhsPerp)) {
            return BOTTOM_VALUE;
        }
        if (leq(lhs, rhs)) return lhs;
        if (leq(rhs, lhs)) return rhs;
    } else {
        if (lhs == TOP_VALUE || rhs == TOP_VALUE) return TOP_VALUE;
        if (lhs == BOTTOM_VALUE) return rhs;
        if (rhs == BOTTOM_VALUE) return lhs;
        if (find(closure, complements_[static_cast<std::size_t>(lhs)]) == rhs) {
            return TOP_VALUE;
        }
        if (leq(lhs, rhs)) return rhs;
        if (leq(rhs, lhs)) return lhs;
    }

    std::optional<ValueId> result;
    for (const OperationFact& fact : closure.facts) {
        if (fact.operation != operation) continue;
        ValueId a = find(closure, fact.lhs);
        ValueId b = find(closure, fact.rhs);
        if (a > b) std::swap(a, b);
        if (a != lhs || b != rhs) continue;
        const ValueId r = find(closure, fact.result);
        if (!result) result = r;
        else if (find(closure, *result) != r) return std::nullopt;
    }
    if (result) return find(closure, *result);
    return std::nullopt;
}

bool GeneratedLattice::applyOperationCongruence(Closure& closure) const {
    bool changed = false;

    std::map<OpKey, ValueId> resultByKey;
    for (const OperationFact& fact : closure.facts) {
        ValueId lhs = find(closure, fact.lhs);
        ValueId rhs = find(closure, fact.rhs);
        if (lhs > rhs) std::swap(lhs, rhs);
        ValueId result = find(closure, fact.result);
        const OpKey key = keyFor(
            static_cast<std::uint8_t>(fact.operation), lhs, rhs
        );
        const auto [it, inserted] = resultByKey.emplace(key, result);
        if (!inserted) {
            changed |= unite(closure, it->second, result);
            if (!closure.consistent) return changed;
        }
    }

    rebuildOrder(closure);

    for (const OperationFact& fact : closure.facts) {
        const auto expected = lookupOperation(
            closure, fact.operation, fact.lhs, fact.rhs
        );
        if (expected) {
            changed |= unite(closure, fact.result, *expected);
            if (!closure.consistent) return changed;
        }
    }

    return changed;
}

bool GeneratedLattice::applyDimensionOrderEqualities(Closure& closure) const {
    bool changed = false;
    rebuildOrder(closure);
    const std::size_t count = activeValues_;

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (!closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)] &&
                !closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(lhs)]) {
                continue;
            }
            if (dimensions_[static_cast<std::size_t>(lhs)] ==
                dimensions_[static_cast<std::size_t>(rhs)]) {
                changed |= unite(closure, lhs, rhs);
                if (!closure.consistent) return changed;
            }
        }
    }
    return changed;
}

bool GeneratedLattice::applyAssociativity(Closure& closure) const {
    bool changed = false;
    rebuildOrder(closure);
    const auto tryOperation = [&](Operation operation, ValueId a, ValueId b)
        -> std::optional<ValueId> {
        return lookupOperation(closure, operation, a, b);
    };

    const std::size_t count = activeValues_;
    for (const Operation operation : {Operation::Meet, Operation::Join}) {
        for (ValueId a = 0; a < static_cast<ValueId>(count); ++a) {
            for (ValueId b = 0; b < static_cast<ValueId>(count); ++b) {
                const auto ab = tryOperation(operation, a, b);
                if (!ab) continue;
                for (ValueId c = 0; c < static_cast<ValueId>(count); ++c) {
                    const auto left = tryOperation(operation, *ab, c);
                    if (!left) continue;
                    const auto bc = tryOperation(operation, b, c);
                    if (!bc) continue;
                    const auto right = tryOperation(operation, a, *bc);
                    if (!right) continue;
                    changed |= unite(closure, *left, *right);
                    if (!closure.consistent) return changed;
                }
            }
        }
    }
    return changed;
}

bool GeneratedLattice::applyModularity(Closure& closure) const {
    bool changed = false;
    rebuildOrder(closure);
    const std::size_t count = activeValues_;

    for (ValueId a = 0; a < static_cast<ValueId>(count); ++a) {
        for (ValueId c = 0; c < static_cast<ValueId>(count); ++c) {
            if (!closure.leq[static_cast<std::size_t>(a)][static_cast<std::size_t>(c)]) {
                continue;
            }
            for (ValueId b = 0; b < static_cast<ValueId>(count); ++b) {
                const auto bcMeet = lookupOperation(closure, Operation::Meet, b, c);
                if (!bcMeet) continue;
                const auto lhs = lookupOperation(closure, Operation::Join, a, *bcMeet);
                if (!lhs) continue;
                const auto abJoin = lookupOperation(closure, Operation::Join, a, b);
                if (!abJoin) continue;
                const auto rhs = lookupOperation(closure, Operation::Meet, *abJoin, c);
                if (!rhs) continue;

                changed |= unite(closure, *lhs, *rhs);
                if (!closure.consistent) return changed;
            }
        }
    }
    return changed;
}

bool GeneratedLattice::applyOrthomodularity(Closure& closure) const {
    bool changed = false;
    rebuildOrder(closure);
    const std::size_t count = activeValues_;

    for (ValueId a = 0; a < static_cast<ValueId>(count); ++a) {
        for (ValueId b = 0; b < static_cast<ValueId>(count); ++b) {
            if (!closure.leq[static_cast<std::size_t>(a)][static_cast<std::size_t>(b)]) {
                continue;
            }
            const ValueId aPerp = complements_[static_cast<std::size_t>(a)];
            const auto rest = lookupOperation(closure, Operation::Meet, b, aPerp);
            if (!rest) continue;
            const auto reconstructed = lookupOperation(
                closure, Operation::Join, a, *rest
            );
            if (!reconstructed) continue;
            changed |= unite(closure, *reconstructed, b);
            if (!closure.consistent) return changed;
        }
    }
    return changed;
}

bool GeneratedLattice::applyDimensionDistributivity(Closure& closure) const {
    const std::size_t count = activeValues_;
    const std::size_t dimension = static_cast<std::size_t>(hilbertDimension_);
    if (dimension == 0 || count == 0) return false;

    bool anyChanged = false;
    rebuildOrder(closure);

    for (const auto [outer, inner] : {
             std::pair{Operation::Meet, Operation::Join},
             std::pair{Operation::Join, Operation::Meet}}) {
        std::vector<std::vector<ValueId>> memo(count);
        std::vector<std::uint8_t> state(count, 0);

        std::function<std::vector<ValueId>(ValueId)> flatten =
            [&](ValueId raw) -> std::vector<ValueId> {
                const ValueId value = find(closure, raw);
                const std::size_t vi = static_cast<std::size_t>(value);
                if (state[vi] == 2) return memo[vi];
                if (state[vi] == 1) return {value};
                state[vi] = 1;

                std::vector<ValueId> best{value};
                for (const OperationFact& fact : closure.facts) {
                    if (fact.operation != inner ||
                        find(closure, fact.result) != value) {
                        continue;
                    }
                    const ValueId lhs = find(closure, fact.lhs);
                    const ValueId rhs = find(closure, fact.rhs);
                    if (lhs == value || rhs == value) continue;

                    std::vector<ValueId> candidate = flatten(lhs);
                    const std::vector<ValueId> right = flatten(rhs);
                    candidate.insert(candidate.end(), right.begin(), right.end());
                    for (ValueId& x : candidate) x = find(closure, x);
                    std::sort(candidate.begin(), candidate.end());
                    candidate.erase(
                        std::unique(candidate.begin(), candidate.end()),
                        candidate.end()
                    );
                    if (candidate.size() > best.size()) best = std::move(candidate);
                }

                state[vi] = 2;
                memo[vi] = best;
                return memo[vi];
            };

        std::map<std::vector<ValueId>, ValueId> valueForLeaves;
        for (ValueId value = 0; value < static_cast<ValueId>(count); ++value) {
            std::vector<ValueId> leaves = flatten(value);
            valueForLeaves.emplace(std::move(leaves), find(closure, value));
        }

        for (const OperationFact& fact : closure.facts) {
            if (fact.operation != outer) continue;

            for (int orientation = 0; orientation < 2; ++orientation) {
                const ValueId x = find(
                    closure,
                    orientation == 0 ? fact.lhs : fact.rhs
                );
                const ValueId aggregate = find(
                    closure,
                    orientation == 0 ? fact.rhs : fact.lhs
                );
                const ValueId lhsResult = find(closure, fact.result);

                const std::vector<ValueId> ys = flatten(aggregate);

                if (ys.size() < dimension + 1) continue;

                std::vector<ValueId> partialResults;
                partialResults.reserve(ys.size());
                bool complete = true;

                for (std::size_t omitted = 0; omitted < ys.size(); ++omitted) {
                    std::vector<ValueId> subset;
                    subset.reserve(ys.size() - 1);
                    for (std::size_t i = 0; i < ys.size(); ++i) {
                        if (i != omitted) subset.push_back(ys[i]);
                    }
                    std::sort(subset.begin(), subset.end());
                    subset.erase(std::unique(subset.begin(), subset.end()), subset.end());

                    const auto aggregateIt = valueForLeaves.find(subset);
                    if (aggregateIt == valueForLeaves.end()) {
                        complete = false;
                        break;
                    }
                    const auto partial = lookupOperation(
                        closure, outer, x, aggregateIt->second
                    );
                    if (!partial) {
                        complete = false;
                        break;
                    }
                    partialResults.push_back(find(closure, *partial));
                }
                if (!complete) continue;

                std::sort(partialResults.begin(), partialResults.end());
                partialResults.erase(
                    std::unique(partialResults.begin(), partialResults.end()),
                    partialResults.end()
                );
                const auto rhsIt = valueForLeaves.find(partialResults);
                if (rhsIt == valueForLeaves.end()) continue;

                anyChanged |= unite(closure, lhsResult, rhsIt->second);
                if (!closure.consistent) return anyChanged;
            }
        }
    }

    return anyChanged;
}

bool GeneratedLattice::validateClosure(Closure& closure) const {
    rebuildOrder(closure);
    const std::size_t count = activeValues_;

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (find(closure, lhs) == find(closure, rhs) &&
                relations_[index(lhs, rhs)] != Relation::Undefined) {
                return false;
            }
        }
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)] &&
                closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(lhs)] &&
                find(closure, lhs) != find(closure, rhs)) {
                return false;
            }
        }
    }

    for (ValueId value = 0; value < static_cast<ValueId>(count); ++value) {
        const ValueId c = complements_[static_cast<std::size_t>(value)];
        if (c < 0 || static_cast<std::size_t>(c) >= count) return false;
        if (complements_[static_cast<std::size_t>(c)] != value) return false;
        if (dimensions_[static_cast<std::size_t>(value)] +
                dimensions_[static_cast<std::size_t>(c)] !=
            static_cast<std::int32_t>(hilbertDimension_)) {
            return false;
        }
    }
    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = 0; rhs < static_cast<ValueId>(count); ++rhs) {
            if (!closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)]) {
                continue;
            }
            const ValueId lhsC = complements_[static_cast<std::size_t>(lhs)];
            const ValueId rhsC = complements_[static_cast<std::size_t>(rhs)];
            if (!closure.leq[static_cast<std::size_t>(rhsC)][static_cast<std::size_t>(lhsC)]) {
                return false;
            }
        }
    }

    for (ValueId a = 0; a < static_cast<ValueId>(count); ++a) {
        for (ValueId b = a; b < static_cast<ValueId>(count); ++b) {
            const auto meet = lookupOperation(closure, Operation::Meet, a, b);
            const auto join = lookupOperation(closure, Operation::Join, a, b);
            if (!meet || !join) continue;
            const std::int32_t lhs =
                dimensions_[static_cast<std::size_t>(find(closure, *meet))] +
                dimensions_[static_cast<std::size_t>(find(closure, *join))];
            const std::int32_t rhs =
                dimensions_[static_cast<std::size_t>(find(closure, a))] +
                dimensions_[static_cast<std::size_t>(find(closure, b))];
            if (lhs != rhs) return false;
        }
    }

    for (ValueId lhs = 0; lhs < static_cast<ValueId>(count); ++lhs) {
        for (ValueId rhs = lhs + 1; rhs < static_cast<ValueId>(count); ++rhs) {
            if (relations_[index(lhs, rhs)] != Relation::Incomparable) continue;
            if (closure.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)] ||
                closure.leq[static_cast<std::size_t>(rhs)][static_cast<std::size_t>(lhs)]) {
                return false;
            }
        }
    }

    return true;
}

GeneratedLattice::Closure GeneratedLattice::computeClosure() const {
    Closure closure;
    closure.parent.resize(activeValues_);
    closure.rank.assign(activeValues_, 0);
    for (ValueId value = 0;
         value < static_cast<ValueId>(activeValues_);
         ++value) {
        closure.parent[static_cast<std::size_t>(value)] = value;
    }

    closure.facts.reserve(operationFacts_.size() * 2);
    for (const OperationFact& fact : operationFacts_) {
        if (fact.lhs >= static_cast<ValueId>(activeValues_) ||
            fact.rhs >= static_cast<ValueId>(activeValues_) ||
            fact.result >= static_cast<ValueId>(activeValues_)) {
            closure.consistent = false;
            return closure;
        }
        closure.facts.push_back(fact);
        closure.facts.push_back(dualFact(fact));
    }

    refineClosure(closure);
    return closure;
}

void GeneratedLattice::refineClosure(Closure& closure) const {
    if (!closure.consistent) return;

    bool changed = true;
    while (changed && closure.consistent) {
        changed = false;
        rebuildOrder(closure);
        changed |= applyOperationCongruence(closure);
        if (!closure.consistent) break;
        changed |= applyComplementCongruence(closure);
        if (!closure.consistent) break;
        changed |= applyDimensionOrderEqualities(closure);
        if (!closure.consistent) break;
        changed |= applyAssociativity(closure);
        if (!closure.consistent) break;
        changed |= applyModularity(closure);
        if (!closure.consistent) break;
        changed |= applyOrthomodularity(closure);
        if (!closure.consistent) break;
        changed |= applyDimensionDistributivity(closure);
    }

    if (closure.consistent && !validateClosure(closure)) {
        closure.consistent = false;
    }
    rebuildOrder(closure);
}

void GeneratedLattice::invalidateClosure() noexcept {
    cachedClosure_.reset();
}

GeneratedLattice::Closure& GeneratedLattice::closure() const {
    if (!cachedClosure_) {
        cachedClosure_ = computeClosure();
    }
    return *cachedClosure_;
}

bool GeneratedLattice::consistent() const {
    return closure().consistent;
}

bool GeneratedLattice::equivalent(ValueId lhs, ValueId rhs) const {
    requireActive(lhs);
    requireActive(rhs);
    Closure& state = closure();
    return state.consistent && find(state, lhs) == find(state, rhs);
}

ValueId GeneratedLattice::canonical(ValueId value) const {
    requireActive(value);
    Closure& state = closure();
    if (!state.consistent) return value;
    return find(state, value);
}

bool GeneratedLattice::lessOrEqual(ValueId lhs, ValueId rhs) const {
    requireActive(lhs);
    requireActive(rhs);
    Closure& state = closure();
    if (!state.consistent) return false;
    return state.leq[static_cast<std::size_t>(lhs)][static_cast<std::size_t>(rhs)];
}

std::optional<ValueId> GeneratedLattice::knownMeet(
    ValueId lhs,
    ValueId rhs
) const {
    requireActive(lhs);
    requireActive(rhs);
    Closure& state = closure();
    if (!state.consistent) return std::nullopt;
    const auto value = lookupOperation(state, Operation::Meet, lhs, rhs);
    if (!value) return std::nullopt;
    return find(state, *value);
}

std::optional<ValueId> GeneratedLattice::knownJoin(
    ValueId lhs,
    ValueId rhs
) const {
    requireActive(lhs);
    requireActive(rhs);
    Closure& state = closure();
    if (!state.consistent) return std::nullopt;
    const auto value = lookupOperation(state, Operation::Join, lhs, rhs);
    if (!value) return std::nullopt;
    return find(state, *value);
}

GeneratedLattice::Quotient GeneratedLattice::quotient() const {
    Quotient out;
    Closure closure = this->closure();
    out.consistent = closure.consistent;
    if (!closure.consistent) return out;

    const std::size_t count = activeValues_;
    std::vector<ValueId> rootToNew(count, UNASSIGNED_VALUE);
    out.oldToNew.assign(count, UNASSIGNED_VALUE);

    const ValueId bottomRoot = find(closure, BOTTOM_VALUE);
    const ValueId topRoot = find(closure, TOP_VALUE);
    rootToNew[static_cast<std::size_t>(bottomRoot)] = BOTTOM_VALUE;
    rootToNew[static_cast<std::size_t>(topRoot)] = TOP_VALUE;
    ValueId next = 2;

    for (ValueId old = 0; old < static_cast<ValueId>(count); ++old) {
        const ValueId root = find(closure, old);
        ValueId& mapped = rootToNew[static_cast<std::size_t>(root)];
        if (mapped == UNASSIGNED_VALUE) mapped = next++;
        out.oldToNew[static_cast<std::size_t>(old)] = mapped;
    }

    const std::size_t newCount = static_cast<std::size_t>(next);
    out.dimensions.assign(newCount, UNDEFINED_DIMENSION);
    out.complements.assign(newCount, UNASSIGNED_VALUE);
    out.relations.assign(newCount * newCount, Relation::Undefined);

    for (ValueId old = 0; old < static_cast<ValueId>(count); ++old) {
        const ValueId mapped = out.oldToNew[static_cast<std::size_t>(old)];
        out.dimensions[static_cast<std::size_t>(mapped)] =
            dimensions_[static_cast<std::size_t>(old)];
        out.complements[static_cast<std::size_t>(mapped)] =
            out.oldToNew[static_cast<std::size_t>(
                complements_[static_cast<std::size_t>(old)]
            )];
    }

    std::vector<ValueId> representative(newCount, UNASSIGNED_VALUE);
    for (ValueId old = 0; old < static_cast<ValueId>(count); ++old) {
        const ValueId mapped = out.oldToNew[static_cast<std::size_t>(old)];
        if (representative[static_cast<std::size_t>(mapped)] == UNASSIGNED_VALUE) {
            representative[static_cast<std::size_t>(mapped)] = old;
        }
    }

    for (ValueId a = 0; a < static_cast<ValueId>(newCount); ++a) {
        for (ValueId b = a + 1; b < static_cast<ValueId>(newCount); ++b) {
            const ValueId oldA = representative[static_cast<std::size_t>(a)];
            const ValueId oldB = representative[static_cast<std::size_t>(b)];
            Relation rel = Relation::Incomparable;
            if (closure.leq[static_cast<std::size_t>(oldA)][static_cast<std::size_t>(oldB)]) {
                rel = Relation::Below;
            } else if (closure.leq[static_cast<std::size_t>(oldB)][static_cast<std::size_t>(oldA)]) {
                rel = Relation::Above;
            } else {
                const Relation raw = relations_[index(oldA, oldB)];
                if (raw == Relation::Undefined) rel = Relation::Undefined;
            }
            out.relations[static_cast<std::size_t>(a) * newCount + static_cast<std::size_t>(b)] = rel;
            out.relations[static_cast<std::size_t>(b) * newCount + static_cast<std::size_t>(a)] = inverse(rel);
        }
    }

    std::vector<bool> baseClass(newCount, false);
    for (ValueId old = 0; old < static_cast<ValueId>(baseValueCount_); ++old) {
        baseClass[static_cast<std::size_t>(out.oldToNew[static_cast<std::size_t>(old)])] = true;
    }
    out.baseValueCount = static_cast<std::size_t>(
        std::count(baseClass.begin(), baseClass.end(), true)
    );

    return out;
}
}
