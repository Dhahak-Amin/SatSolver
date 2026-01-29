

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <chrono>
#include "Solver/Solver_CDCL.hpp"
#include "Solver/inout.hpp"


static std::vector<std::vector<sat::Literal>> extractSolutionCDCL(const sat_cdcl::SolverCDCL& solver) {
    std::vector<std::vector<sat::Literal>> solution;
    for (auto l : solver.getUnitLiterals()) {
        solution.push_back(std::vector<sat::Literal>{sat::Literal(l.get())});
    }
    return solution;
}

int main(int argc, char** argv) {
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

    std::cout << "c Fichier : " << cnfFile << "\n";
    std::cout << "c Variables : " << numVariables << "\n";
    std::cout << "c Clauses : " << clauses.size() << "\n";

    
    sat_cdcl::SolverCDCL solverCDCL(static_cast<unsigned>(numVariables));
    for (auto& cl : clauses) {
        std::vector<sat::Literal> copy = cl;
        solverCDCL.addClause(sat::Clause(std::move(copy)));
    }

    auto t0 = std::chrono::steady_clock::now();
    bool satCDCL = solverCDCL.solve();
    auto t1 = std::chrono::steady_clock::now();
    auto msCDCL = std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();

    std::cout << "c [CDCL] : " << (satCDCL ? "SAT" : "UNSAT") 
              << " en " << msCDCL << " ms\n";

  

    if (!satCDCL) {
        std::cout << "UNSAT\n";
        return 0;
    }

    auto solution = extractSolutionCDCL(solverCDCL);
    std::string dimacsOutput = sat::inout::to_dimacs(solution);
    std::cout << dimacsOutput;

    std::ofstream outFile("solution.cnf");
    if (outFile.is_open()) {
        outFile << dimacsOutput;
        outFile.close();
    }

    return 0;
}
