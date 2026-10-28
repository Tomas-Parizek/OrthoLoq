#pragma once

#include "Aig.hpp"
#include "Witness.hpp"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>

#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace ql {
using BigInt = boost::multiprecision::cpp_int;
using Rational = boost::rational<BigInt>;
using ExactMatrix = std::vector<std::vector<Rational>>;

struct ModelEntry {
    std::string name;
    ExactMatrix basis;
    ExactMatrix projector;
};

struct ConcreteModel {
    std::uint32_t hilbertDimension = 0;
    std::vector<ModelEntry> variables;
    ExactMatrix outputBasis;
    ExactMatrix outputProjector;
};

class Realizer {
public:
    Realizer(const Formula& formula, const AbstractWitness& witness);

    std::optional<ConcreteModel> realize() const;

private:
    struct Subspace {
        ExactMatrix basis;
    };

    const Formula& formula_;
    const AbstractWitness& witness_;

    std::optional<std::vector<Subspace>> realizeWitnessValues() const;
    bool verifyWitness(const std::vector<Subspace>& spaces) const;
    std::optional<ConcreteModel> buildModel(
        const std::vector<Subspace>& spaces
    ) const;

    static Subspace zero(std::size_t ambientDimension);
    static Subspace whole(std::size_t ambientDimension);
    static Subspace fromRows(ExactMatrix rows, std::size_t ambientDimension);
    static Subspace span(const Subspace& lhs, const Subspace& rhs);
    static Subspace orthogonalComplement(
        const Subspace& value,
        std::size_t ambientDimension
    );
    static Subspace meet(
        const Subspace& lhs,
        const Subspace& rhs,
        std::size_t ambientDimension
    );

    static bool equal(const Subspace& lhs, const Subspace& rhs);
    static bool isSubspaceOf(const Subspace& lhs, const Subspace& rhs);
    static std::size_t dimension(const Subspace& value) noexcept;

    static ExactMatrix rref(ExactMatrix matrix);
    static ExactMatrix nullspaceBasis(
        const ExactMatrix& matrix,
        std::size_t columnCount
    );
    static ExactMatrix projector(
        const Subspace& value,
        std::size_t ambientDimension
    );
    static ExactMatrix inverse(ExactMatrix matrix);
    static ExactMatrix transpose(const ExactMatrix& matrix);
    static ExactMatrix multiply(
        const ExactMatrix& lhs,
        const ExactMatrix& rhs
    );

    static ValueId valueOfLiteral(
        Lit literal,
        const std::vector<ValueId>& nodeValues,
        const AbstractWitness& witness
    );
};

void printModel(std::ostream& out, const ConcreteModel& model);
}
