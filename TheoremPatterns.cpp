#include "TheoremPatterns.hpp"

#include <algorithm>
#include <cstdlib>
#include <map>
#include <optional>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

namespace ql {
namespace {
class View {
public:
    explicit View(const Formula& formula)
        {
        for (const auto& [name, node] : formula.variables()) {
            (void)name;
            variables_.insert(node);
        }
        for (const AndGate& gate : formula.gates()) {
            gates_.emplace(gate.out, &gate);
        }
    }

    const AndGate* gate(NodeId node) const {
        const auto it = gates_.find(node);
        return it == gates_.end() ? nullptr : it->second;
    }

    bool isVariable(NodeId node) const {
        return variables_.contains(node);
    }

    bool isPositiveVariable(Lit literal) const {
        return literal > 1 && isVariable(static_cast<NodeId>(literal));
    }

    bool isVariableLiteral(Lit literal) const {
        if (literal == TRUE_LIT || literal == FALSE_LIT) return false;
        return isVariable(static_cast<NodeId>(std::abs(literal)));
    }

private:
    std::set<NodeId> variables_;
    std::unordered_map<NodeId, const AndGate*> gates_;
};

template<class T>
void sortUnique(std::vector<T>& values) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
}

void flattenMeet(const View& view, Lit literal, std::vector<Lit>& out) {
    if (literal > 1) {
        if (const AndGate* gate = view.gate(static_cast<NodeId>(literal))) {
            flattenMeet(view, gate->lhs, out);
            flattenMeet(view, gate->rhs, out);
            return;
        }
    }
    out.push_back(literal);
}

void flattenJoin(const View& view, Lit literal, std::vector<Lit>& out) {
    if (literal < -1) {
        if (const AndGate* gate = view.gate(static_cast<NodeId>(-literal))) {
            flattenJoin(view, static_cast<Lit>(-gate->lhs), out);
            flattenJoin(view, static_cast<Lit>(-gate->rhs), out);
            return;
        }
    }
    out.push_back(literal);
}

std::vector<Lit> meetLeaves(const View& view, Lit literal) {
    std::vector<Lit> result;
    flattenMeet(view, literal, result);
    sortUnique(result);
    return result;
}

std::vector<Lit> joinLeaves(const View& view, Lit literal) {
    std::vector<Lit> result;
    flattenJoin(view, literal, result);
    sortUnique(result);
    return result;
}

bool allDistinctPositiveVariables(const View& view, const std::vector<Lit>& xs) {
    if (xs.empty()) return false;
    for (Lit x : xs) {
        if (!view.isPositiveVariable(x)) return false;
    }
    return std::adjacent_find(xs.begin(), xs.end()) == xs.end();
}

bool matchesNDPartial(
    const View& view,
    Lit complementedFactor,
    Lit x,
    const std::vector<Lit>& ys,
    std::size_t& omittedOut
) {
    if (complementedFactor >= -1) return false;
    const Lit positive = static_cast<Lit>(-complementedFactor);
    std::vector<Lit> factors = meetLeaves(view, positive);
    if (factors.size() != 2) return false;

    Lit aggregate = 0;
    if (factors[0] == x) aggregate = factors[1];
    else if (factors[1] == x) aggregate = factors[0];
    else return false;

    std::vector<Lit> subset = joinLeaves(view, aggregate);
    if (subset.size() + 1 != ys.size()) return false;

    std::size_t omitted = ys.size();
    for (std::size_t i = 0; i < ys.size(); ++i) {
        std::vector<Lit> expected;
        expected.reserve(ys.size() - 1);
        for (std::size_t j = 0; j < ys.size(); ++j) {
            if (j != i) expected.push_back(ys[j]);
        }
        if (subset == expected) {
            if (omitted != ys.size()) return false;
            omitted = i;
        }
    }
    if (omitted == ys.size()) return false;
    omittedOut = omitted;
    return true;
}

std::optional<std::size_t> matchNDistributivityCounterexample(
    const Formula& formula
) {
    const View view(formula);
    std::vector<Lit> factors = meetLeaves(view, formula.output());
    if (factors.size() < 5) return std::nullopt;

    for (Lit x : factors) {
        if (!view.isPositiveVariable(x)) continue;

        for (Lit aggregate : factors) {
            if (aggregate == x) continue;
            std::vector<Lit> ys = joinLeaves(view, aggregate);
            if (ys.size() < 3) continue;
            if (!allDistinctPositiveVariables(view, ys)) continue;
            if (std::binary_search(ys.begin(), ys.end(), x)) continue;

            std::vector<Lit> remaining;
            remaining.reserve(factors.size() - 2);
            bool removedX = false;
            bool removedAggregate = false;
            for (Lit factor : factors) {
                if (!removedX && factor == x) {
                    removedX = true;
                    continue;
                }
                if (!removedAggregate && factor == aggregate) {
                    removedAggregate = true;
                    continue;
                }
                remaining.push_back(factor);
            }
            if (!removedX || !removedAggregate || remaining.size() != ys.size()) {
                continue;
            }

            std::vector<bool> seenOmitted(ys.size(), false);
            bool complete = true;
            for (Lit factor : remaining) {
                std::size_t omitted = ys.size();
                if (!matchesNDPartial(view, factor, x, ys, omitted) ||
                    seenOmitted[omitted]) {
                    complete = false;
                    break;
                }
                seenOmitted[omitted] = true;
            }
            if (!complete ||
                std::find(seenOmitted.begin(), seenOmitted.end(), false) !=
                    seenOmitted.end()) {
                continue;
            }

            return ys.size() - 1;
        }
    }

    return std::nullopt;
}

std::optional<std::size_t> matchCompatibilityFailureFamily(
    const Formula& formula
) {
    const View view(formula);
    std::vector<Lit> factors = meetLeaves(view, formula.output());
    if (factors.size() < 3) return std::nullopt;

    for (Lit state : factors) {
        if (!view.isPositiveVariable(state)) continue;

        std::map<NodeId, std::pair<bool, bool>> contextSigns;
        bool removedState = false;
        bool valid = true;

        for (Lit factor : factors) {
            if (!removedState && factor == state) {
                removedState = true;
                continue;
            }
            if (factor >= -1) {
                valid = false;
                break;
            }

            const Lit positiveMeet = static_cast<Lit>(-factor);
            std::vector<Lit> pair = meetLeaves(view, positiveMeet);
            if (pair.size() != 2) {
                valid = false;
                break;
            }

            Lit contextLiteral = 0;
            if (pair[0] == state) contextLiteral = pair[1];
            else if (pair[1] == state) contextLiteral = pair[0];
            else {
                valid = false;
                break;
            }

            if (!view.isVariableLiteral(contextLiteral)) {
                valid = false;
                break;
            }
            const NodeId context = static_cast<NodeId>(std::abs(contextLiteral));
            if (context == state) {
                valid = false;
                break;
            }

            auto& signs = contextSigns[context];
            if (contextLiteral > 0) {
                if (signs.first) { valid = false; break; }
                signs.first = true;
            } else {
                if (signs.second) { valid = false; break; }
                signs.second = true;
            }
        }

        if (!valid || !removedState || contextSigns.empty()) continue;
        bool complete = true;
        for (const auto& [context, signs] : contextSigns) {
            (void)context;
            if (!signs.first || !signs.second) {
                complete = false;
                break;
            }
        }
        if (!complete) continue;

        return contextSigns.size();
    }

    return std::nullopt;
}
}

TheoremPatternMatch matchStandardTheoremPattern(const Formula& formula) {
    if (const auto n = matchNDistributivityCounterexample(formula)) {
        return {
            formula.dimension() <= *n
                ? TheoremDecision::Unsat
                : TheoremDecision::Sat,
            "n-distributivity-counterexample",
            *n
        };
    }

    if (const auto contexts = matchCompatibilityFailureFamily(formula)) {
        return {
            formula.dimension() >= 2
                ? TheoremDecision::Sat
                : TheoremDecision::Unsat,
            "compatibility-failure-family",
            *contexts
        };
    }

    return {};
}
}
