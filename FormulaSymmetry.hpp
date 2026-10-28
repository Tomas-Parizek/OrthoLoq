#pragma once

#include "Aig.hpp"

#include <vector>

namespace ql {
std::vector<std::vector<NodeId>> variableSwapSymmetryOrbits(
    const Formula& formula
);
}
