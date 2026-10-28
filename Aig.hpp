#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace ql {
using Lit = std::int32_t;
using NodeId = std::int32_t;

inline constexpr Lit TRUE_LIT  =  1;
inline constexpr Lit FALSE_LIT = -1;

struct AndGate {
    NodeId out;
    Lit lhs;
    Lit rhs;
};

class Formula {
public:
    explicit Formula(std::uint32_t dimension = 0);

    std::uint32_t dimension() const noexcept;
    void setDimension(std::uint32_t dimension);

    Lit output() const noexcept;
    void setOutput(Lit output) noexcept;

    Lit variable(const std::string& name);

    Lit makeNot(Lit x) const noexcept;
    Lit makeAnd(Lit a, Lit b);
    Lit makeOr(Lit a, Lit b);

    const std::vector<AndGate>& gates() const noexcept;
    const std::unordered_map<std::string, NodeId>& variables() const noexcept;
    NodeId maxNodeId() const noexcept;

private:
    struct PairHash {
        std::size_t operator()(const std::pair<Lit, Lit>& p) const noexcept;
    };

    std::uint32_t dimension_;
    Lit output_ = FALSE_LIT;

    NodeId nextId_ = 2;

    std::unordered_map<std::string, NodeId> variables_;
    std::vector<AndGate> gates_;

    std::unordered_map<std::pair<Lit, Lit>, NodeId, PairHash> andTable_;
};
}
