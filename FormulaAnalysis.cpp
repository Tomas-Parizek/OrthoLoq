#include "FormulaAnalysis.hpp"
#include "Lattice.hpp"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <numeric>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <utility>

namespace ql {
namespace {
struct View {
    explicit View(const Formula& source)
        : formula(source) {
        for (const auto& [name, node] : source.variables()) {
            variableNames.emplace(node, name);
        }
        for (const AndGate& gate : source.gates()) {
            gates.emplace(gate.out, &gate);
        }
    }

    const Formula& formula;
    std::unordered_map<NodeId, std::string> variableNames;
    std::unordered_map<NodeId, const AndGate*> gates;

    const AndGate* gate(NodeId node) const {
        const auto it = gates.find(node);
        return it == gates.end() ? nullptr : it->second;
    }

    bool isVariable(NodeId node) const {
        return variableNames.find(node) != variableNames.end();
    }
};

using Substitutions = std::unordered_map<NodeId, Lit>;
using NodeAbstractions = std::unordered_map<NodeId, std::string>;

Formula copyFromRoots(
    const Formula& source,
    const std::vector<Lit>& roots,
    bool combineByMeet,
    const Substitutions& substitutions = {},
    const NodeAbstractions& abstractions = {}
) {
    const View view(source);
    Formula target(source.dimension());
    std::unordered_map<NodeId, Lit> memo;

    std::function<Lit(Lit)> copyLit = [&](Lit literal) -> Lit {
        if (literal == TRUE_LIT || literal == FALSE_LIT) {
            return literal;
        }

        const bool negated = literal < 0;
        const NodeId node = static_cast<NodeId>(std::abs(literal));

        if (const auto abstraction = abstractions.find(node);
            abstraction != abstractions.end()) {
            Lit positive = UNASSIGNED_VALUE;
            if (const auto cached = memo.find(node); cached != memo.end()) {
                positive = cached->second;
            } else {
                positive = target.variable(abstraction->second);
                memo.emplace(node, positive);
            }
            return negated ? target.makeNot(positive) : positive;
        }

        if (const auto substitution = substitutions.find(node);
            substitution != substitutions.end()) {
            const Lit base = substitution->second;
            return negated ? target.makeNot(base) : base;
        }

        Lit positive = UNASSIGNED_VALUE;
        if (const auto cached = memo.find(node); cached != memo.end()) {
            positive = cached->second;
        } else if (const auto variable = view.variableNames.find(node);
                   variable != view.variableNames.end()) {
            positive = target.variable(variable->second);
            memo.emplace(node, positive);
        } else {
            const AndGate* gate = view.gate(node);
            if (gate == nullptr) {
                throw std::logic_error("AIG contains a reference to an unknown node");
            }
            positive = target.makeAnd(copyLit(gate->lhs), copyLit(gate->rhs));
            memo.emplace(node, positive);
        }

        return negated ? target.makeNot(positive) : positive;
    };

    if (roots.empty()) {
        target.setOutput(combineByMeet ? TRUE_LIT : FALSE_LIT);
        return target;
    }

    std::vector<Lit> level;
    level.reserve(roots.size());
    for (const Lit root : roots) {
        level.push_back(copyLit(root));
    }

    while (level.size() > 1) {
        std::vector<Lit> next;
        next.reserve((level.size() + 1) / 2);
        for (std::size_t i = 0; i < level.size(); i += 2) {
            if (i + 1 == level.size()) {
                next.push_back(level[i]);
            } else {
                next.push_back(
                    combineByMeet
                        ? target.makeAnd(level[i], level[i + 1])
                        : target.makeOr(level[i], level[i + 1])
                );
            }
        }
        level = std::move(next);
    }

    target.setOutput(level.front());
    return target;
}

void flattenMeet(const View& view, Lit literal, std::vector<Lit>& out) {
    if (literal > 1) {
        if (const AndGate* gate = view.gate(literal)) {
            flattenMeet(view, gate->lhs, out);
            flattenMeet(view, gate->rhs, out);
            return;
        }
    }
    out.push_back(literal);
}

void flattenJoin(const View& view, Lit literal, std::vector<Lit>& out) {
    if (literal < -1) {
        const NodeId node = static_cast<NodeId>(-literal);
        if (const AndGate* gate = view.gate(node)) {
            flattenJoin(view, -gate->lhs, out);
            flattenJoin(view, -gate->rhs, out);
            return;
        }
    }
    out.push_back(literal);
}

void collectVariables(
    const View& view,
    Lit literal,
    std::unordered_set<NodeId>& out,
    std::unordered_set<NodeId>& expandedGates
) {
    if (literal == TRUE_LIT || literal == FALSE_LIT) return;
    const NodeId node = static_cast<NodeId>(std::abs(literal));
    if (view.isVariable(node)) {
        out.insert(node);
        return;
    }
    const AndGate* gate = view.gate(node);
    if (gate == nullptr) {
        throw std::logic_error("AIG contains a reference to an unknown node");
    }
    if (!expandedGates.insert(node).second) return;
    collectVariables(view, gate->lhs, out, expandedGates);
    collectVariables(view, gate->rhs, out, expandedGates);
}

struct Polarity {
    bool positive = false;
    bool negative = false;
};

struct RangeInfo {
    std::unordered_set<NodeId> support;
    bool canBeZero = false;
    bool canBeTop = false;
    bool surjective = false;
};

bool disjointSupports(
    const std::unordered_set<NodeId>& a,
    const std::unordered_set<NodeId>& b
) {
    if (a.size() > b.size()) return disjointSupports(b, a);
    for (const NodeId x : a) {
        if (b.contains(x)) return false;
    }
    return true;
}

class RangeAnalyzer {
public:
    explicit RangeAnalyzer(const Formula& formula)
        : view_(formula) {}

    RangeInfo literal(Lit literal) {
        if (literal == TRUE_LIT) {
            return {{}, false, true, false};
        }
        if (literal == FALSE_LIT) {
            return {{}, true, false, false};
        }

        const bool negated = literal < 0;
        const NodeId node = static_cast<NodeId>(std::abs(literal));
        RangeInfo info = positive(node);
        if (negated) std::swap(info.canBeZero, info.canBeTop);
        return info;
    }

private:
    const View view_;
    std::unordered_map<NodeId, RangeInfo> memo_;

    RangeInfo positive(NodeId node) {
        if (const auto cached = memo_.find(node); cached != memo_.end()) {
            return cached->second;
        }

        RangeInfo result;
        if (view_.isVariable(node)) {
            result.support.insert(node);
            result.canBeZero = true;
            result.canBeTop = true;
            result.surjective = true;
            memo_.emplace(node, result);
            return result;
        }

        const AndGate* gate = view_.gate(node);
        if (gate == nullptr) {
            throw std::logic_error("AIG contains a reference to an unknown node");
        }

        const RangeInfo lhs = literal(gate->lhs);
        const RangeInfo rhs = literal(gate->rhs);
        result.support = lhs.support;
        result.support.insert(rhs.support.begin(), rhs.support.end());

        result.canBeZero = lhs.canBeZero || rhs.canBeZero;

        const bool independent = disjointSupports(lhs.support, rhs.support);
        result.canBeTop =
            independent && lhs.canBeTop && rhs.canBeTop;
        result.surjective = independent && (
            (lhs.surjective && rhs.canBeTop) ||
            (rhs.surjective && lhs.canBeTop)
        );

        memo_.emplace(node, result);
        return result;
    }
};

void collectVariablesOutsideNode(
    const View& view,
    Lit literal,
    NodeId opaqueNode,
    std::unordered_set<NodeId>& out,
    std::unordered_set<NodeId>& expanded
) {
    if (literal == TRUE_LIT || literal == FALSE_LIT) return;
    const NodeId node = static_cast<NodeId>(std::abs(literal));
    if (node == opaqueNode) return;
    if (view.isVariable(node)) {
        out.insert(node);
        return;
    }
    if (!expanded.insert(node).second) return;
    const AndGate* gate = view.gate(node);
    if (gate == nullptr) {
        throw std::logic_error("AIG contains a reference to an unknown node");
    }
    collectVariablesOutsideNode(view, gate->lhs, opaqueNode, out, expanded);
    collectVariablesOutsideNode(view, gate->rhs, opaqueNode, out, expanded);
}

struct PrivateAbstractionCandidate {
    NodeId node = 0;
    std::size_t supportSize = 0;
};

std::optional<PrivateAbstractionCandidate> findPrivateSurjectiveSubterm(
    const Formula& formula
) {
    const View view(formula);
    RangeAnalyzer ranges(formula);
    std::optional<PrivateAbstractionCandidate> best;

    for (const AndGate& gate : formula.gates()) {
        const RangeInfo info = ranges.literal(gate.out);
        if (!info.surjective || info.support.size() < 2) continue;

        std::unordered_set<NodeId> outside;
        std::unordered_set<NodeId> expanded;
        collectVariablesOutsideNode(
            view,
            formula.output(),
            gate.out,
            outside,
            expanded
        );

        bool privateSupport = true;
        for (const NodeId variable : info.support) {
            if (outside.contains(variable)) {
                privateSupport = false;
                break;
            }
        }
        if (!privateSupport) continue;

        const PrivateAbstractionCandidate candidate{
            gate.out,
            info.support.size()
        };
        if (!best ||
            candidate.supportSize > best->supportSize ||
            (candidate.supportSize == best->supportSize &&
             candidate.node > best->node)) {
            best = candidate;
        }
    }

    return best;
}

std::string freshAbstractionName(const Formula& formula, std::size_t serial) {
    for (;;) {
        const std::string name = "__ql_private_" + std::to_string(serial++);
        if (formula.variables().find(name) == formula.variables().end()) {
            return name;
        }
    }
}

Formula abstractPrivateSurjectiveSubterms(
    const Formula& formula,
    std::size_t& abstracted,
    std::size_t& variablesCompressed
) {
    Formula current = copyOutputCone(formula);
    std::size_t serial = 0;

    for (;;) {
        const auto candidate = findPrivateSurjectiveSubterm(current);
        if (!candidate) break;

        const std::string freshName = freshAbstractionName(current, serial++);
        NodeAbstractions abstractions;
        abstractions.emplace(candidate->node, freshName);
        current = copyFromRoots(
            current,
            {current.output()},
            true,
            {},
            abstractions
        );
        ++abstracted;
        variablesCompressed += candidate->supportSize - 1;
    }

    return current;
}

std::unordered_map<NodeId, Polarity> polarities(const Formula& formula) {
    const View view(formula);
    std::unordered_map<NodeId, Polarity> result;

    std::unordered_set<std::uint64_t> seen;
    std::function<void(Lit, bool)> visit = [&](Lit literal, bool outerNegation) {
        if (literal == TRUE_LIT || literal == FALSE_LIT) return;
        const bool negated = outerNegation ^ (literal < 0);
        const NodeId node = static_cast<NodeId>(std::abs(literal));

        if (view.isVariable(node)) {
            Polarity& p = result[node];
            if (negated) p.negative = true;
            else p.positive = true;
            return;
        }

        const std::uint64_t key =
            (static_cast<std::uint64_t>(static_cast<std::uint32_t>(node)) << 1) |
            static_cast<std::uint64_t>(negated);
        if (!seen.insert(key).second) return;

        const AndGate* gate = view.gate(node);
        if (gate == nullptr) {
            throw std::logic_error("AIG contains a reference to an unknown node");
        }

        visit(gate->lhs, negated);
        visit(gate->rhs, negated);
    };

    visit(formula.output(), false);
    return result;
}

class DisjointSet {
public:
    explicit DisjointSet(std::size_t count)
        : parent_(count), rank_(count, 0) {
        std::iota(parent_.begin(), parent_.end(), std::size_t{0});
    }

    std::size_t find(std::size_t x) {
        if (parent_[x] != x) parent_[x] = find(parent_[x]);
        return parent_[x];
    }

    void unite(std::size_t a, std::size_t b) {
        a = find(a);
        b = find(b);
        if (a == b) return;
        if (rank_[a] < rank_[b]) std::swap(a, b);
        parent_[b] = a;
        if (rank_[a] == rank_[b]) ++rank_[a];
    }

private:
    std::vector<std::size_t> parent_;
    std::vector<std::uint8_t> rank_;
};
}

Formula copyOutputCone(const Formula& formula) {
    return copyFromRoots(formula, {formula.output()}, true);
}

Formula preprocessFormula(const Formula& formula, PreprocessStats* stats) {
    if (stats != nullptr) {
        *stats = PreprocessStats{};
        stats->originalVariables = formula.variables().size();
        stats->originalGates = formula.gates().size();
    }

    Formula current = copyOutputCone(formula);
    std::size_t eliminated = 0;
    std::size_t abstracted = 0;
    std::size_t compressed = 0;

    for (;;) {
        const std::size_t beforeVariables = current.variables().size();
        const std::size_t beforeGates = current.gates().size();

        current = abstractPrivateSurjectiveSubterms(
            current,
            abstracted,
            compressed
        );

        const auto occurrence = polarities(current);
        Substitutions substitutions;
        for (const auto& [node, polarity] : occurrence) {
            if (polarity.positive == polarity.negative) continue;
            substitutions.emplace(
                node,
                polarity.positive ? TRUE_LIT : FALSE_LIT
            );
        }

        if (!substitutions.empty()) {
            eliminated += substitutions.size();
            current = copyFromRoots(
                current,
                {current.output()},
                true,
                substitutions
            );
        }
        current = copyOutputCone(current);

        if (substitutions.empty() &&
            current.variables().size() == beforeVariables &&
            current.gates().size() == beforeGates) {
            break;
        }
    }

    if (stats != nullptr) {
        stats->finalVariables = current.variables().size();
        stats->finalGates = current.gates().size();
        stats->pureVariablesEliminated = eliminated;
        stats->privateSubtermsAbstracted = abstracted;
        stats->privateVariablesCompressed = compressed;
    }
    return current;
}

std::vector<Lit> flattenTopLevelMeet(const Formula& formula) {
    std::vector<Lit> factors;
    flattenMeet(View(formula), formula.output(), factors);
    return factors;
}

std::vector<Lit> flattenTopLevelJoin(const Formula& formula) {
    std::vector<Lit> factors;
    flattenJoin(View(formula), formula.output(), factors);
    return factors;
}

std::vector<Formula> splitIndependentTopLevelMeet(const Formula& formula) {
    const View view(formula);
    std::vector<Lit> factors;
    flattenMeet(view, formula.output(), factors);
    if (factors.size() <= 1) {
        return {copyOutputCone(formula)};
    }

    std::vector<std::vector<NodeId>> factorVariables(factors.size());
    std::unordered_map<NodeId, std::size_t> firstFactor;
    DisjointSet dsu(factors.size());

    for (std::size_t i = 0; i < factors.size(); ++i) {
        std::unordered_set<NodeId> variables;
        std::unordered_set<NodeId> expanded;
        collectVariables(view, factors[i], variables, expanded);
        factorVariables[i].assign(variables.begin(), variables.end());

        for (const NodeId variable : factorVariables[i]) {
            const auto [it, inserted] = firstFactor.emplace(variable, i);
            if (!inserted) dsu.unite(i, it->second);
        }
    }

    std::unordered_map<std::size_t, std::vector<Lit>> rootsByComponent;
    std::vector<std::size_t> componentOrder;
    for (std::size_t i = 0; i < factors.size(); ++i) {
        const std::size_t root = dsu.find(i);
        if (rootsByComponent.find(root) == rootsByComponent.end()) {
            componentOrder.push_back(root);
        }
        rootsByComponent[root].push_back(factors[i]);
    }

    if (componentOrder.size() <= 1) {
        return {copyOutputCone(formula)};
    }

    std::vector<Formula> result;
    result.reserve(componentOrder.size());
    for (const std::size_t component : componentOrder) {
        result.push_back(copyFromRoots(
            formula,
            rootsByComponent[component],
            true
        ));
    }
    return result;
}

std::vector<Formula> splitTopLevelJoin(const Formula& formula) {
    const View view(formula);
    std::vector<Lit> factors;
    flattenJoin(view, formula.output(), factors);
    if (factors.size() <= 1) {
        return {copyOutputCone(formula)};
    }

    std::vector<Formula> result;
    result.reserve(factors.size());
    for (const Lit factor : factors) {
        result.push_back(copyFromRoots(formula, {factor}, true));
    }
    return result;
}

std::unordered_map<NodeId, std::size_t> variableOccurrenceCounts(
    const Formula& formula
) {
    const View view(formula);
    std::unordered_map<NodeId, std::size_t> counts;

    std::unordered_set<std::uint64_t> expanded;
    std::function<void(Lit, bool)> visit = [&](Lit literal, bool outerNegation) {
        if (literal == TRUE_LIT || literal == FALSE_LIT) return;
        const bool negated = outerNegation ^ (literal < 0);
        const NodeId node = static_cast<NodeId>(std::abs(literal));
        if (view.isVariable(node)) {
            ++counts[node];
            return;
        }
        const std::uint64_t key =
            (static_cast<std::uint64_t>(static_cast<std::uint32_t>(node)) << 1) |
            static_cast<std::uint64_t>(negated);
        if (!expanded.insert(key).second) return;
        const AndGate* gate = view.gate(node);
        if (gate == nullptr) return;
        visit(gate->lhs, negated);
        visit(gate->rhs, negated);
    };
    visit(formula.output(), false);
    return counts;
}
}
