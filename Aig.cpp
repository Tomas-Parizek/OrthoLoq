#include "Aig.hpp"

#include <algorithm>
#include <functional>
#include <stdexcept>

namespace ql {
Formula::Formula(std::uint32_t dimension)
    : dimension_(dimension) {}

std::uint32_t Formula::dimension() const noexcept {
    return dimension_;
}

void Formula::setDimension(std::uint32_t dimension) {
    if (dimension == 0) {
        throw std::invalid_argument("dimension must be positive");
    }
    dimension_ = dimension;
}

Lit Formula::output() const noexcept {
    return output_;
}

void Formula::setOutput(Lit output) noexcept {
    output_ = output;
}

Lit Formula::variable(const std::string& name) {
    if (const auto it = variables_.find(name); it != variables_.end()) {
        return it->second;
    }

    const NodeId id = nextId_++;
    variables_.emplace(name, id);
    return id;
}

Lit Formula::makeNot(Lit x) const noexcept {
    return -x;
}

Lit Formula::makeAnd(Lit a, Lit b) {
    if (a == FALSE_LIT || b == FALSE_LIT) {
        return FALSE_LIT;
    }
    if (a == TRUE_LIT) {
        return b;
    }
    if (b == TRUE_LIT) {
        return a;
    }

    if (a == b) {
        return a;
    }
    if (a == -b) {
        return FALSE_LIT;
    }

    if (a > b) {
        std::swap(a, b);
    }

    const std::pair<Lit, Lit> key{a, b};

    if (const auto it = andTable_.find(key); it != andTable_.end()) {
        return it->second;
    }

    const NodeId out = nextId_++;
    gates_.push_back({out, a, b});
    andTable_.emplace(key, out);

    return out;
}

Lit Formula::makeOr(Lit a, Lit b) {
    return makeNot(makeAnd(makeNot(a), makeNot(b)));
}

const std::vector<AndGate>& Formula::gates() const noexcept {
    return gates_;
}

const std::unordered_map<std::string, NodeId>& Formula::variables() const noexcept {
    return variables_;
}

NodeId Formula::maxNodeId() const noexcept {
    return nextId_ - 1;
}

std::size_t Formula::PairHash::operator()(
    const std::pair<Lit, Lit>& p
) const noexcept {
    const std::size_t h1 = std::hash<Lit>{}(p.first);
    const std::size_t h2 = std::hash<Lit>{}(p.second);

    return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
}
}
