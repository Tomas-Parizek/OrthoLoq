#pragma once

#include "Aig.hpp"

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace ql {
class Parser {
public:
    Formula parseFile(const std::string& path);
    Formula parseString(const std::string& input);

private:
    struct ParsedExpr {
        enum class Kind {
            Ref,
            And,
            Or,
            Not
        };

        Kind kind;
        std::vector<std::string> args;
    };

    static std::string trim(std::string_view s);
    static bool startsWith(std::string_view s, std::string_view prefix);
    static bool isPositiveInteger(std::string_view s);
    static bool isVariableName(std::string_view s);

    static std::uint32_t parseDimension(const std::string& line, std::size_t lineNo);
    static std::string parseOutput(const std::string& line, std::size_t lineNo);

    static ParsedExpr parseExpression(const std::string& text, std::size_t lineNo);
    static std::vector<std::string> splitArguments(
        std::string_view text,
        std::size_t lineNo
    );

    static Lit resolveReference(
        const std::string& ref,
        Formula& formula,
        const std::unordered_map<std::string, Lit>& namedGates,
        std::size_t lineNo
    );

    static Lit buildBalanced(
        Formula& formula,
        const std::vector<Lit>& args,
        bool isAnd
    );
};
}
