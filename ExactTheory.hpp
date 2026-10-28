#pragma once

#include "Aig.hpp"
#include "Witness.hpp"

#include <cstddef>
#include <cstdint>
#include <string>

namespace ql {
enum class ExactTheoryResult : std::uint8_t {
    Sat,
    Unsat
};

struct ExactTheoryStats {
    std::uint64_t backendCalls = 0;
    std::uint64_t realVariables = 0;
    std::uint64_t polynomialEqualities = 0;
    std::uint64_t polynomialInequalities = 0;
    std::size_t smtBytes = 0;
    std::string backend;
};

class ExactTheorySolver {
public:
    explicit ExactTheorySolver(const Formula& formula);

    ExactTheoryResult solve();
    const ExactTheoryStats& stats() const noexcept;

    std::string encodeSmt2();

private:
    const Formula& formula_;
    ExactTheoryStats stats_;
};

class ExactMembershipTheorySolver {
public:
    explicit ExactMembershipTheorySolver(const Formula& formula);

    ExactTheoryResult solve();
    const ExactTheoryStats& stats() const noexcept;
    std::string encodeSmt2();

private:
    const Formula& formula_;
    ExactTheoryStats stats_;
};

class ExactWitnessTheorySolver {
public:
    ExactWitnessTheorySolver(
        const Formula& formula,
        const AbstractWitness& witness
    );

    ExactTheoryResult solve();
    const ExactTheoryStats& stats() const noexcept;
    std::string encodeSmt2();

private:
    const Formula& formula_;
    const AbstractWitness& witness_;
    ExactTheoryStats stats_;
};

const char* toString(ExactTheoryResult result) noexcept;
}
