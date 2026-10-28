#include "FormulaSymmetry.hpp"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace ql {
namespace {
class View {
public:
    explicit View(const Formula& formula) {
        for (const auto& [name, node] : formula.variables()) {
            (void)name;
            variables_[node] = true;
        }
        for (const AndGate& gate : formula.gates()) gates_[gate.out] = &gate;
    }

    bool isVariable(NodeId node) const {
        return variables_.find(node) != variables_.end();
    }

    const AndGate* gate(NodeId node) const {
        const auto it = gates_.find(node);
        return it == gates_.end() ? nullptr : it->second;
    }

private:
    std::unordered_map<NodeId, bool> variables_;
    std::unordered_map<NodeId, const AndGate*> gates_;
};

struct Swap {
    NodeId a = 0;
    NodeId b = 0;

    NodeId map(NodeId x) const noexcept {
        if (x == a) return b;
        if (x == b) return a;
        return x;
    }
};

std::string canonicalSemantic(
    const View& view,
    Lit root,
    const Swap& swap
) {
    std::unordered_map<std::int64_t, std::string> memo;

    std::function<std::string(Lit)> canonical;
    std::function<void(Lit, char, std::vector<std::string>&)> collect;

    collect = [&](Lit literal, char operation, std::vector<std::string>& out) {
        if (operation == 'M' && literal > 1) {
            if (const AndGate* gate = view.gate(static_cast<NodeId>(literal))) {
                collect(gate->lhs, operation, out);
                collect(gate->rhs, operation, out);
                return;
            }
        }
        if (operation == 'J' && literal < -1) {
            if (const AndGate* gate = view.gate(static_cast<NodeId>(-literal))) {
                collect(static_cast<Lit>(-gate->lhs), operation, out);
                collect(static_cast<Lit>(-gate->rhs), operation, out);
                return;
            }
        }
        out.push_back(canonical(literal));
    };

    canonical = [&](Lit literal) -> std::string {
        if (literal == TRUE_LIT) return "1";
        if (literal == FALSE_LIT) return "0";

        const std::int64_t key = static_cast<std::int64_t>(literal);
        if (const auto it = memo.find(key); it != memo.end()) return it->second;

        const bool negated = literal < 0;
        const NodeId node = static_cast<NodeId>(std::abs(literal));
        std::string result;

        if (view.isVariable(node)) {
            const NodeId mapped = swap.map(node);
            result = negated
                ? "N(V" + std::to_string(mapped) + ")"
                : "V" + std::to_string(mapped);
        } else if (!negated) {
            const AndGate* gate = view.gate(node);
            if (gate == nullptr) return "?" + std::to_string(literal);
            std::vector<std::string> operands;
            collect(gate->lhs, 'M', operands);
            collect(gate->rhs, 'M', operands);
            std::sort(operands.begin(), operands.end());
            operands.erase(std::unique(operands.begin(), operands.end()), operands.end());
            result = "M(";
            for (const auto& x : operands) result += x + ",";
            result += ")";
        } else {
            const AndGate* gate = view.gate(node);
            if (gate == nullptr) return "?" + std::to_string(literal);
            std::vector<std::string> operands;
            collect(static_cast<Lit>(-gate->lhs), 'J', operands);
            collect(static_cast<Lit>(-gate->rhs), 'J', operands);
            std::sort(operands.begin(), operands.end());
            operands.erase(std::unique(operands.begin(), operands.end()), operands.end());
            result = "J(";
            for (const auto& x : operands) result += x + ",";
            result += ")";
        }

        memo.emplace(key, result);
        return result;
    };

    return canonical(root);
}

class DisjointSet {
public:
    explicit DisjointSet(std::size_t n) : parent_(n), rank_(n, 0) {
        std::iota(parent_.begin(), parent_.end(), std::size_t{0});
    }
    std::size_t find(std::size_t x) {
        if (parent_[x] != x) parent_[x] = find(parent_[x]);
        return parent_[x];
    }
    void unite(std::size_t a, std::size_t b) {
        a = find(a); b = find(b);
        if (a == b) return;
        if (rank_[a] < rank_[b]) std::swap(a,b);
        parent_[b] = a;
        if (rank_[a] == rank_[b]) ++rank_[a];
    }
private:
    std::vector<std::size_t> parent_;
    std::vector<unsigned char> rank_;
};
}

std::vector<std::vector<NodeId>> variableSwapSymmetryOrbits(
    const Formula& formula
) {
    std::vector<NodeId> vars;
    vars.reserve(formula.variables().size());
    for (const auto& [name, node] : formula.variables()) {
        (void)name;
        vars.push_back(node);
    }
    std::sort(vars.begin(), vars.end());
    if (vars.size() < 2) return {};

    const View view(formula);
    const std::string baseline = canonicalSemantic(view, formula.output(), {});
    DisjointSet dsu(vars.size());

    for (std::size_t i = 0; i < vars.size(); ++i) {
        for (std::size_t j = i + 1; j < vars.size(); ++j) {
            if (canonicalSemantic(view, formula.output(), {vars[i], vars[j]}) == baseline) {
                dsu.unite(i, j);
            }
        }
    }

    std::unordered_map<std::size_t, std::vector<NodeId>> grouped;
    for (std::size_t i = 0; i < vars.size(); ++i) {
        grouped[dsu.find(i)].push_back(vars[i]);
    }

    std::vector<std::vector<NodeId>> result;
    for (auto& [root, orbit] : grouped) {
        (void)root;
        if (orbit.size() <= 1) continue;
        std::sort(orbit.begin(), orbit.end());
        result.push_back(std::move(orbit));
    }
    std::sort(result.begin(), result.end());
    return result;
}
}
