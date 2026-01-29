

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <chrono>

// Solveur CDCL (nouveau)
#include "Solver/Solver_CDCL.hpp"

// Solveurs DPLL (existants, pour comparaison)
#include "Solver/Solver.hpp"
#include "Solver/inout.hpp"

/**
 * Extrait la solution du solveur CDCL
 */
static std::vector<std::vector<sat::Literal>> extractSolutionCDCL(const sat_cdcl::SolverCDCL& solver) {
    std::vector<std::vector<sat::Literal>> solution;
    for (auto l : solver.getUnitLiterals()) {
        // Conversion sat_cdcl::Literal -> sat::Literal (même encodage)
        solution.push_back(std::vector<sat::Literal>{sat::Literal(l.get())});
    }
    return solution;
}

/**
 * Extrait la solution du solveur DPLL
 */
static std::vector<std::vector<sat::Literal>> extractSolutionDPLL(const sat::Solver& solver) {
    std::vector<std::vector<sat::Literal>> solution;
    for (auto l : solver.getUnitLiterals()) {
        solution.push_back(std::vector<sat::Literal>{l});
    }
    return solution;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cout << "c Usage: " << argv[0] << " path/to/problem.cnf\n";
        std::cout << "c \n";
        std::cout << "c Ce programme compare les performances de CDCL vs DPLL\n";
        return 1;
    }

    const std::string cnfFile = argv[1];
    std::ifstream ifs(cnfFile);
    if (!ifs.is_open()) {
        std::cout << "c Could not open file " << cnfFile << "\n";
        return 1;
    }

    // Lecture du fichier DIMACS
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

    sat::Solver solverDPLL(static_cast<unsigned>(numVariables));
    for (auto& cl : clauses) {
        std::vector<sat::Literal> copy = cl;
        solverDPLL.addClause(sat::Clause(std::move(copy)));
    }

    auto t2 = std::chrono::steady_clock::now();
    bool satDPLL = solverDPLL.solve();
    auto t3 = std::chrono::steady_clock::now();
    auto msDPLL = std::chrono::duration_cast<std::chrono::milliseconds>(t3 - t2).count();


    
  
            std::cout << "c CDCL a mis :  " << msCDCL << " ms\n";
     
            std::cout << "c DPLL a mis : " << msDPLL << " ms\n";
      
    

    if (!satCDCL) {
        std::cout << "UNSAT\n";
        return 0;
    }

    auto solution = extractSolutionCDCL(solverCDCL);
    std::cout << sat::inout::to_dimacs(solution);

    return 0;
}
