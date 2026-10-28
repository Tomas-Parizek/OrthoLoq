#include "FormulaAnalysis.hpp"
#include "Model.hpp"
#include "Parser.hpp"
#include "Solver.hpp"

#include <exception>
#include <iostream>
#include <string>

namespace {
void printStats(
    const ql::PreprocessStats& preprocessing,
    const ql::SolveStats& solving
) {
    std::cerr
        << "preprocess.original_variables=" << preprocessing.originalVariables << '\n'
        << "preprocess.original_gates=" << preprocessing.originalGates << '\n'
        << "preprocess.final_variables=" << preprocessing.finalVariables << '\n'
        << "preprocess.final_gates=" << preprocessing.finalGates << '\n'
        << "preprocess.pure_variables_eliminated="
        << preprocessing.pureVariablesEliminated << '\n'
        << "preprocess.private_subterms_abstracted="
        << preprocessing.privateSubtermsAbstracted << '\n'
        << "preprocess.private_variables_compressed="
        << preprocessing.privateVariablesCompressed << '\n'
        << "solve.recursive_calls=" << solving.recursiveCalls << '\n'
        << "solve.branches=" << solving.branches << '\n'
        << "solve.leaves=" << solving.leaves << '\n'
        << "solve.reused_value_branches=" << solving.reusedValueBranches << '\n'
        << "solve.fresh_value_branches=" << solving.freshValueBranches << '\n'
        << "solve.relation_decisions=" << solving.relationDecisions << '\n'
        << "solve.relation_configurations=" << solving.relationConfigurations << '\n'
        << "solve.pruned_relation_branches=" << solving.prunedRelationBranches << '\n'
        << "solve.structural_subproblems=" << solving.structuralSubproblems << '\n'
        << "solve.independent_meet_splits=" << solving.independentMeetSplits << '\n'
        << "solve.top_level_join_splits=" << solving.topLevelJoinSplits << '\n'
        << "solve.partial_dimension_prunes=" << solving.partialDimensionPrunes << '\n'
        << "solve.dimension_domain_prunes=" << solving.dimensionDomainPrunes << '\n'
        << "solve.memo_hits=" << solving.memoHits << '\n'
        << "solve.memo_stores=" << solving.memoStores << '\n'
        << "solve.demanded_relation_pairs=" << solving.demandedRelationPairs << '\n'
        << "solve.relation_state_memo_hits=" << solving.relationStateMemoHits << '\n'
        << "solve.relation_state_memo_stores=" << solving.relationStateMemoStores << '\n'
        << "solve.deferred_relation_completions="
        << solving.deferredRelationCompletions << '\n'
        << "solve.theorem_pattern_hits=" << solving.theoremPatternHits << '\n'
        << "solve.symmetry_dimension_prunes=" << solving.symmetryDimensionPrunes << '\n'
        << "solve.exact_theory_calls=" << solving.exactTheoryCalls << '\n'
        << "solve.exact_theory_sat=" << solving.exactTheorySat << '\n'
        << "solve.exact_theory_unsat=" << solving.exactTheoryUnsat << '\n'
        << "solve.exact_theory_real_variables=" << solving.exactTheoryRealVariables << '\n'
        << "solve.exact_theory_equalities=" << solving.exactTheoryEqualities << '\n'
        << "solve.exact_theory_inequalities=" << solving.exactTheoryInequalities << '\n'
        << "solve.exact_theory_smt_bytes=" << solving.exactTheorySmtBytes << '\n'
        << "solve.adaptive_exact_handoffs=" << solving.adaptiveExactHandoffs << '\n'
        << "solve.max_active_values=" << solving.maxActiveValues << '\n';
}
}

int main(int argc, char** argv) {
    bool modelRequested = false;
    bool statsRequested = false;
    ql::SolveMode solveMode = ql::SolveMode::Complete;
    std::string inputPath;

    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (arg == "--model") {
            modelRequested = true;
            continue;
        }
        if (arg == "--stats") {
            statsRequested = true;
            continue;
        }
        if (arg == "--fast-only") {
            if (solveMode == ql::SolveMode::ExactOnly) {
                std::cerr << "--fast-only and --exact-only are mutually exclusive\n";
                return 1;
            }
            solveMode = ql::SolveMode::FastOnly;
            continue;
        }
        if (arg == "--exact-only") {
            if (solveMode == ql::SolveMode::FastOnly) {
                std::cerr << "--fast-only and --exact-only are mutually exclusive\n";
                return 1;
            }
            solveMode = ql::SolveMode::ExactOnly;
            continue;
        }
        if (!inputPath.empty()) {
            std::cerr << "usage: ortholoq [--model] [--stats] [--fast-only|--exact-only] <file.qlcir>\n";
            return 1;
        }
        inputPath = arg;
    }

    if (inputPath.empty()) {
        std::cerr << "usage: ortholoq [--model] [--stats] [--fast-only|--exact-only] <file.qlcir>\n";
        return 1;
    }

    try {
        ql::Parser parser;
        const ql::Formula parsedFormula = parser.parseFile(inputPath);

        ql::PreprocessStats preprocessStats;
        ql::Formula formula = modelRequested

            ? ql::copyOutputCone(parsedFormula)
            : ql::preprocessFormula(parsedFormula, &preprocessStats);

        if (modelRequested) {
            preprocessStats.originalVariables = parsedFormula.variables().size();
            preprocessStats.originalGates = parsedFormula.gates().size();
            preprocessStats.finalVariables = formula.variables().size();
            preprocessStats.finalGates = formula.gates().size();
            preprocessStats.pureVariablesEliminated = 0;
            preprocessStats.privateSubtermsAbstracted = 0;
            preprocessStats.privateVariablesCompressed = 0;
        }

        ql::Solver solver(formula, modelRequested, solveMode);
        const ql::SolveResult result = solver.solve();

        std::cout << ql::toString(result) << '\n';

        if (statsRequested) {
            printStats(preprocessStats, solver.stats());
        }

        if (result == ql::SolveResult::Sat && modelRequested) {
            const ql::AbstractWitness* witness = solver.witness();
            if (witness == nullptr) {
                std::cout << "model: unavailable (winning witness was not captured)\n";
                return 0;
            }

            const ql::Realizer realizer(formula, *witness);
            const auto model = realizer.realize();
            if (!model) {
                std::cout
                    << "model: unavailable (exact realizer does not yet support "
                       "this certified witness)\n";
                return 0;
            }

            ql::printModel(std::cout, *model);
        }

        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 2;
    }
}
