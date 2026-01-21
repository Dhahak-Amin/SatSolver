/**
 * Simple SAT solver executable.
 * Place this file in the main project directory as solve.cpp
 *
 * Usage:
 *   ./solve path/to/file.cnf
 *
 * Output rules:
 * - If UNSAT: print "UNSAT"
 * - If SAT: print solution (unit literals) in DIMACS format using sat::inout::to_dimacs
 * - Any extra output must be prefixed with 'c'
 */

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <chrono>

#include "Solver/Solver.hpp"
#include "Solver/inout.hpp"

static std::vector<std::vector<sat::Literal>> extractUnitSolution(const sat::Solver &solver) {
    std::vector<std::vector<sat::Literal>> solution;
    for (auto l : solver.getUnitLiterals()) {
        solution.push_back(std::vector<sat::Literal>{l});
    }
    return solution;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cout << "c Usage: " << argv[0] << " path/to/problem.cnf\n";
        return 1;
    }

    const std::string cnfFile = argv[1];
    std::ifstream ifs(cnfFile);
    if (!ifs.is_open()) {
        std::cout << "c Could not open file " << cnfFile << "\n";
        return 1;
    }

    auto [clauses, numVariables] = sat::inout::read_from_dimacs(ifs);

    sat::Solver solverWeighted(numVariables);
    sat::Solver solverFirst(numVariables);

    for (auto &cl : clauses) {
        std::vector<sat::Literal> copy = cl; // keep a copy for solverFirst
        solverWeighted.addClause(sat::Clause(std::move(cl)));
        solverFirst.addClause(sat::Clause(std::move(copy)));
    }

    auto t0 = std::chrono::steady_clock::now();
    bool satWeighted = solverWeighted.solve();
    auto t1 = std::chrono::steady_clock::now();
    auto msWeighted = std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();

    auto t2 = std::chrono::steady_clock::now();
    bool satFirst = solverFirst.solveFirstVariable();
    auto t3 = std::chrono::steady_clock::now();
    auto msFirst = std::chrono::duration_cast<std::chrono::milliseconds>(t3 - t2).count();

    std::cout << "c File: " << cnfFile << "\n";
    std::cout << "c Vars: " << numVariables << "\n";
    std::cout << "c Time WeightedDegree+Restart: " << msWeighted << " ms\n";
    std::cout << "c Time FirstVariable: " << msFirst << " ms\n";

    if (satWeighted != satFirst) {
        std::cout << "c WARNING: solvers disagree (one says SAT, the other UNSAT)\n";
    }

    if (!satWeighted) {
        std::cout << "UNSAT\n";
        return 0;
    }

    auto solution = extractUnitSolution(solverWeighted);
    std::cout << sat::inout::to_dimacs(solution);
    return 0;
}
