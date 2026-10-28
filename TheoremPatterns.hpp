#pragma once

#include "Aig.hpp"

#include <cstddef>
#include <cstdint>
#include <string>

namespace ql {
enum class TheoremDecision : std::uint8_t {
    None,
    Sat,
    Unsat
};

struct TheoremPatternMatch {
    TheoremDecision decision = TheoremDecision::None;
    std::string rule;
    std::size_t parameter = 0;
};

TheoremPatternMatch matchStandardTheoremPattern(const Formula& formula);
}
