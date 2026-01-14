/**
* @author Tim Luchterhand
* @date 27.11.24
* @file Solver.hpp
* @brief Contains the main solver class
*/

#ifndef SOLVER_HPP
#define SOLVER_HPP

#include <memory>
#include <vector>

#include "basic_structures.hpp"
#include "Clause.hpp"

namespace sat {
    /*
     * These two types might be useful for your implementation. A shared pointer manages an object on the heap. It can
     * be copied without copying the actual object. This can be useful if you want to access the same clause from
     * multiple locations without copying it. Once all copies of the pointer have been destroyed, the actual object
     * is also destroyed
     */
    using ClausePointer = std::shared_ptr<Clause>;
    using ConstClausePointer = std::shared_ptr<const Clause>;


    /**
     * @brief Main solver class
     */
    class Solver {
        // @TODO private members here
        unsigned numVariables;
        std::vector<TruthValue> model;

        // All non-unit clauses stored once (no duplicates by copying)
        std::vector<ClausePointer> clauses;

        // All unit literals (from unit clauses / propagation)
        std::vector<Literal> unitLiterals;

        // une Watch lists: for each literal id, store clauses currently watching this literal ( to be checked)
        std::vector<std::vector<ClausePointer>> watchLists;

    public:

        /**
         * Ctor. Allocates enough space for the variables.
         * @param numVariables Number of variables in the problem
         * @note This Ctor needs to exist for the tests. You can add other Ctors if you want
         */
        explicit Solver(unsigned numVariables);

        /*
         * @TODO if you want, you can declare additional constructors here
         */


        /*
         * You can design the interface of your solver as you want. You can for example add clauses already in the
         * constructor. The tests require the addClause method, however.
         */

        /**
         * Adds a clause to the solver.
         * @param clause The clause to add
         * @return bool true if clause was successfully added, false if clause is empty or unit and violates the current
         * model
         */
        bool addClause(Clause clause);

        /**
         * Returns a reduced set of clauses. Excludes satisfied clauses and removes falsified literals from clauses
         * @return equivalent set of clauses
         */
        auto rebase() const -> std::vector<Clause>;

        /**
         * Returns the truth value of the given variable
         * @param x a variable (needs to be contained in the solver)
         * @return TruthValue of the given variable
         */
        TruthValue val(Variable x) const;

        /**
         * Checks if a literal holds
         * @param l literal (needs ti be contained in the solver)
         * @return true if literal holds under current model, false otherwise
         */
        bool satisfied(Literal l) const;

        /**
         * Checks if a literal does not hold
         * @param l literal (needs ti be contained in the solver)
         * @return true if literal the negated literal is satisfied, false otherwise
         */
        bool falsified(Literal l) const;

        /**
         * Assigns the given literal
         * @param l Literal to assign
         * @return false if literal is already falsified, true otherwise
         */
        bool assign(Literal l);

        /**
         * Does the unit propagation.
         * @return true if unit propagation was successful, false otherwise
         */
        bool unitPropagate();

    };
} // sat

#endif //SOLVER_HPP
