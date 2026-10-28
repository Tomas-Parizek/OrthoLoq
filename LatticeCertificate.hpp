#pragma once

#include "Aig.hpp"
#include "Witness.hpp"

#include <cstdint>
#include <optional>
#include <vector>

namespace ql {
struct SupportCertificate {
    std::uint32_t hilbertDimension = 0;

    std::vector<ValueId> lineValues;
    std::vector<std::uint64_t> supportMasks;
};

class LatticeCertificate {
public:

    static bool certify(
        const Formula& formula,
        const AbstractWitness& witness
    );

    static std::optional<SupportCertificate> supportCertificate(
        const Formula& formula,
        const AbstractWitness& witness
    );

private:
    static bool trivialGeometryCertified(const AbstractWitness& witness);
    static bool relationsWellFormed(const AbstractWitness& witness);
    static bool rankThreeGateSemantics(
        const Formula& formula,
        const AbstractWitness& witness
    );
};
}
