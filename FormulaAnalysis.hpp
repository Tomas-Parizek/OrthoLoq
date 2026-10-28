#pragma once

#include "Aig.hpp"

#include <cstddef>
#include <cstdint>
#include <unordered_map>
#include <vector>

namespace ql {
struct PreprocessStats {
    std::size_t originalVariables = 0;
    std::size_t originalGates = 0;
    std::size_t finalVariables = 0;
    std::size_t finalGates = 0;
    std::size_t pureVariablesEliminated = 0;
    std::size_t privateSubtermsAbstracted = 0;
    std::size_t privateVariablesCompressed = 0;
};

Formula copyOutputCone(const Formula& formula);

Formula preprocessFormula(const Formula& formula, PreprocessStats* stats = nullptr);

std::vector<Lit> flattenTopLevelMeet(const Formula& formula);
std::vector<Lit> flattenTopLevelJoin(const Formula& formula);

std::vector<Formula> splitIndependentTopLevelMeet(const Formula& formula);

std::vector<Formula> splitTopLevelJoin(const Formula& formula);

std::unordered_map<NodeId, std::size_t> variableOccurrenceCounts(
    const Formula& formula
);
}
