#include "Parser.hpp"

#include <cctype>
#include <fstream>
#include <limits>
#include <sstream>
#include <stdexcept>

namespace ql {
namespace {
[[noreturn]] void fail(std::size_t lineNo, const std::string& message) {
    throw std::runtime_error(
        "line " + std::to_string(lineNo) + ": " + message
    );
}

std::string insideParentheses(
    const std::string& line,
    const std::string& keyword,
    std::size_t lineNo
) {
    const std::string prefix = keyword + "(";

    if (!line.starts_with(prefix) || line.empty() || line.back() != ')') {
        fail(lineNo, "expected " + keyword + "(...)");
    }

    return line.substr(prefix.size(), line.size() - prefix.size() - 1);
}
}

Formula Parser::parseFile(const std::string& path) {
    std::ifstream input(path);
    if (!input) {
        throw std::runtime_error("cannot open file: " + path);
    }

    std::ostringstream buffer;
    buffer << input.rdbuf();
    return parseString(buffer.str());
}

Formula Parser::parseString(const std::string& input) {
    Formula formula;

    std::unordered_map<std::string, Lit> namedGates;

    bool sawMagic = false;
    bool sawDimension = false;
    bool sawOutput = false;

    std::string outputRef;

    std::istringstream stream(input);
    std::string rawLine;
    std::size_t lineNo = 0;

    while (std::getline(stream, rawLine)) {
        ++lineNo;
        const std::string line = trim(rawLine);

        if (line.empty()) {
            continue;
        }

        if (line == "#QLCIR-G1") {
            if (sawMagic) {
                fail(lineNo, "duplicate #QLCIR-G1 header");
            }
            sawMagic = true;
            continue;
        }

        if (line.front() == '#') {
            continue;
        }

        if (startsWith(line, "dim(")) {
            if (sawDimension) {
                fail(lineNo, "duplicate dimension declaration");
            }
            formula.setDimension(parseDimension(line, lineNo));
            sawDimension = true;
            continue;
        }

        if (startsWith(line, "output(")) {
            if (sawOutput) {
                fail(lineNo, "duplicate output declaration");
            }
            outputRef = parseOutput(line, lineNo);
            sawOutput = true;
            continue;
        }

        const std::size_t eq = line.find('=');
        if (eq == std::string::npos) {
            fail(lineNo, "expected gate definition");
        }

        const std::string lhs = trim(
            std::string_view(line).substr(0, eq)
        );
        const std::string rhs = trim(
            std::string_view(line).substr(eq + 1)
        );

        if (!isPositiveInteger(lhs)) {
            fail(lineNo, "gate id must be a positive integer");
        }

        if (namedGates.contains(lhs)) {
            fail(lineNo, "gate " + lhs + " is defined more than once");
        }

        const ParsedExpr expr = parseExpression(rhs, lineNo);

        Lit result = 0;

        if (expr.kind == ParsedExpr::Kind::Not) {
            const Lit x = resolveReference(
                expr.args.at(0),
                formula,
                namedGates,
                lineNo
            );
            result = formula.makeNot(x);
        } else if (
            expr.kind == ParsedExpr::Kind::And ||
            expr.kind == ParsedExpr::Kind::Or
        ) {
            std::vector<Lit> args;
            args.reserve(expr.args.size());

            for (const std::string& arg : expr.args) {
                args.push_back(
                    resolveReference(arg, formula, namedGates, lineNo)
                );
            }

            result = buildBalanced(
                formula,
                args,
                expr.kind == ParsedExpr::Kind::And
            );
        } else {
            fail(lineNo, "gate right-hand side must be and/or/not");
        }

        namedGates.emplace(lhs, result);
    }

    if (!sawMagic) {
        throw std::runtime_error("missing #QLCIR-G1 header");
    }
    if (!sawDimension) {
        throw std::runtime_error("missing dim(...) declaration");
    }
    if (!sawOutput) {
        throw std::runtime_error("missing output(...) declaration");
    }

    const Lit out = resolveReference(
        outputRef,
        formula,
        namedGates,
        lineNo + 1
    );
    formula.setOutput(out);

    return formula;
}

std::string Parser::trim(std::string_view s) {
    std::size_t begin = 0;
    while (begin < s.size() &&
           std::isspace(static_cast<unsigned char>(s[begin]))) {
        ++begin;
    }

    std::size_t end = s.size();
    while (end > begin &&
           std::isspace(static_cast<unsigned char>(s[end - 1]))) {
        --end;
    }

    return std::string{s.substr(begin, end - begin)};
}

bool Parser::startsWith(
    std::string_view s,
    std::string_view prefix
) {
    return s.substr(0, prefix.size()) == prefix;
}

bool Parser::isPositiveInteger(std::string_view s) {
    if (s.empty()) {
        return false;
    }

    for (char c : s) {
        if (!std::isdigit(static_cast<unsigned char>(c))) {
            return false;
        }
    }

    return s != "0";
}

bool Parser::isVariableName(std::string_view s) {
    if (s.empty()) {
        return false;
    }

    const auto first = static_cast<unsigned char>(s.front());

    if (!(std::isalpha(first) || s.front() == '_')) {
        return false;
    }

    for (char c : s.substr(1)) {
        const auto uc = static_cast<unsigned char>(c);
        if (!(std::isalnum(uc) || c == '_')) {
            return false;
        }
    }

    return s != "dim" &&
           s != "output" &&
           s != "and" &&
           s != "or" &&
           s != "not";
}

std::uint32_t Parser::parseDimension(
    const std::string& line,
    std::size_t lineNo
) {
    const std::string value = trim(
        insideParentheses(line, "dim", lineNo)
    );

    if (!isPositiveInteger(value)) {
        fail(lineNo, "dimension must be a positive integer");
    }

    const unsigned long long n = std::stoull(value);

    if (n > std::numeric_limits<std::uint32_t>::max()) {
        fail(lineNo, "dimension is too large");
    }

    return static_cast<std::uint32_t>(n);
}

std::string Parser::parseOutput(
    const std::string& line,
    std::size_t lineNo
) {
    const std::string ref = trim(
        insideParentheses(line, "output", lineNo)
    );

    if (!isPositiveInteger(ref) && !isVariableName(ref)) {
        fail(lineNo, "invalid output reference");
    }

    return ref;
}

Parser::ParsedExpr Parser::parseExpression(
    const std::string& text,
    std::size_t lineNo
) {
    auto parseCall = [&](const std::string& name, ParsedExpr::Kind kind) {
        const std::string inner = insideParentheses(text, name, lineNo);
        return ParsedExpr{
            kind,
            splitArguments(inner, lineNo)
        };
    };

    if (startsWith(text, "and(")) {
        ParsedExpr expr = parseCall("and", ParsedExpr::Kind::And);
        if (expr.args.size() < 2) {
            fail(lineNo, "and(...) requires at least two arguments");
        }
        return expr;
    }

    if (startsWith(text, "or(")) {
        ParsedExpr expr = parseCall("or", ParsedExpr::Kind::Or);
        if (expr.args.size() < 2) {
            fail(lineNo, "or(...) requires at least two arguments");
        }
        return expr;
    }

    if (startsWith(text, "not(")) {
        ParsedExpr expr = parseCall("not", ParsedExpr::Kind::Not);
        if (expr.args.size() != 1) {
            fail(lineNo, "not(...) requires exactly one argument");
        }
        return expr;
    }

    fail(lineNo, "unknown operation");
}

std::vector<std::string> Parser::splitArguments(
    std::string_view text,
    std::size_t lineNo
) {
    std::vector<std::string> args;

    std::size_t begin = 0;

    while (begin <= text.size()) {
        const std::size_t comma = text.find(',', begin);
        const std::size_t end =
            comma == std::string_view::npos ? text.size() : comma;

        const std::string arg = trim(text.substr(begin, end - begin));

        if (arg.empty()) {
            fail(lineNo, "empty argument");
        }

        if (!isPositiveInteger(arg) && !isVariableName(arg)) {
            fail(lineNo, "invalid reference: " + arg);
        }

        args.push_back(arg);

        if (comma == std::string_view::npos) {
            break;
        }

        begin = comma + 1;
    }

    return args;
}

Lit Parser::resolveReference(
    const std::string& ref,
    Formula& formula,
    const std::unordered_map<std::string, Lit>& namedGates,
    std::size_t lineNo
) {
    if (isPositiveInteger(ref)) {
        if (const auto it = namedGates.find(ref); it != namedGates.end()) {
            return it->second;
        }

        fail(lineNo, "reference to undefined gate " + ref);
    }

    if (!isVariableName(ref)) {
        fail(lineNo, "invalid reference " + ref);
    }

    return formula.variable(ref);
}

Lit Parser::buildBalanced(
    Formula& formula,
    const std::vector<Lit>& args,
    bool isAnd
) {
    if (args.empty()) {
        throw std::logic_error("cannot build an empty operation");
    }

    if (args.size() == 1) {
        return args.front();
    }

    std::vector<Lit> level = args;

    while (level.size() > 1) {
        std::vector<Lit> next;
        next.reserve((level.size() + 1) / 2);

        for (std::size_t i = 0; i < level.size(); i += 2) {
            if (i + 1 == level.size()) {
                next.push_back(level[i]);
                continue;
            }

            next.push_back(
                isAnd
                    ? formula.makeAnd(level[i], level[i + 1])
                    : formula.makeOr(level[i], level[i + 1])
            );
        }

        level = std::move(next);
    }

    return level.front();
}
}
