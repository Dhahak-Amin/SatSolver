/**
 * Simple SAT solver executable.
 * Place this file in the main project directory as solve.cpp
 *
 * Usage:
 *   ./solve path/to/file.cnf
 */
#include <iostream>
#include <fstream>
#include <string>
#include <vector>

#include "Solver/Solver.hpp"
#include "Solver/inout.hpp"

int main(int argc, char **argv) {
     std::cout << "salut au debut \n";
    if (argc < 2) {
        std::cout << "c Usage: " << argv[0] << " path/to/problem.cnf\n";
        return 1;
    }

    const std::string cnfFile = argv[1];
    std::ifstream ifs(cnfFile);
    if (!ifs.is_open()) {
             std::cout << "salut dans ouverture fichier prblm \n";

        std::cout << "c Could not open file " << cnfFile << "\n";
        return 1;
    }

    // Read DIMACS CNF
    auto [clauses, numVariables] = sat::inout::read_from_dimacs(ifs);
         std::cout << "salut apres le read de DIMACS CNF  \n";


    // Build solver
    sat::Solver solver(numVariables);
    for (auto &cl : clauses) {

        // addClause expects sat::Clause
        solver.addClause(sat::Clause(std::move(cl)));
    }

    // Solve
    const bool satResult = solver.solve();
    std::cout << "salut ON recup le rst de solveur  \n";


    if (!satResult) {
        std::cout << "UNSAT\n";
        return 0;
    }

    // SAT: print all unit literals in DIMACS format
    std::vector<std::vector<sat::Literal>> solution;
    for (auto l : solver.getUnitLiterals()) {
        solution.push_back(std::vector<sat::Literal>{l});
    }
    std::cout << sat::inout::to_dimacs(solution);
    return 0;

}
