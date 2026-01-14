/**
* @author Tim Luchterhand
* @date 27.11.24
* @brief
*/

#include <algorithm>
#include <ranges>
#include <cassert>
#include "Solver.hpp"
#include "util/exception.hpp"

namespace sat {
    Solver::Solver(unsigned numVariables)
        : numVariables(numVariables),
          model(numVariables, TruthValue::Undefined),
          watchLists(2u * numVariables) {}

    bool Solver::addClause(Clause clause) {
   
        if (clause.isEmpty()) return false;

        std::vector<Literal> newLits;
        newLits.reserve(clause.size());

        for (auto l : clause) {
            if (satisfied(l)) {
                return true; 
            }
            if (!falsified(l)) {
                newLits.emplace_back(l); 
            }
        }

        if (newLits.empty()) {
            return false;
        }

        if (newLits.size() == 1) {
            // unit clause
            Literal u = newLits[0];
            if (falsified(u)) return false;

            if (!assign(u)) return false;

            auto it = std::find(unitLiterals.begin(), unitLiterals.end(), u);
            if (it == unitLiterals.end()) unitLiterals.emplace_back(u);

            return unitPropagate();
        }

        ClausePointer cptr = std::make_shared<Clause>(Clause(std::move(newLits)));

        clauses.emplace_back(cptr);

        // register watchers in watch lists
        Literal w0 = cptr->getWatcherByRank(0);
        Literal w1 = cptr->getWatcherByRank(1);

        watchLists[w0.get()].push_back(cptr);
        if (!(w1 == w0)) {
            watchLists[w1.get()].push_back(cptr);
        }

        return unitPropagate();
    }

    /**
     * Here you have a possible implementation of the rebase-method. It should work out of the box.
     * To use it, remove the throw-expression and un-comment the code below. The implementation requires that
     * your solver has some sort of container of pointer types to clause called 'clauses'
     * (e.g. std::vector<ClausePointer>). Additionally, your solver needs to have a container of unit literals
     * called 'unitLiterals'.
     */
    auto Solver::rebase() const -> std::vector<Clause> {
        std::vector<Clause> reducedClauses;
        // We check all clauses in the solver. If the clause is SAT (at least one literal is satisfied), we don't include it.
        // Additionally, we remove all falsified literals from the clauses since we only care about unassigned literals.
        for (const auto &c: clauses) {
            bool sat = false;
            std::vector<Literal> newLits;
            newLits.reserve(c->size());
            for (auto l: *c) {
                if (satisfied(l)) {
                    sat = true;
                    break;
                }

                if (!falsified(l)) {
                    newLits.emplace_back(l);
                }
            }

            if (!sat) {
                Clause newClause(std::move(newLits));
                auto res = std::ranges::find_if(reducedClauses, [&newClause](const auto &clause) {
                    return clause.sameLiterals(newClause);
                });

                if (res == reducedClauses.end()) {
                    reducedClauses.emplace_back(std::move(newClause));
                }
               // else: duplicate clause after reduction => do not add
            }
        }

       
        for (Literal l: unitLiterals) {
            reducedClauses.emplace_back(std::vector{l});
        }

        return reducedClauses;
    }

    TruthValue Solver::val(Variable x) const {
        // variable id must be in range
        assert(x.get() < numVariables);
        return model[x.get()];
    }

    bool Solver::satisfied(Literal l) const {
        Variable x = var(l);
        TruthValue v = val(x);
        if (v == TruthValue::Undefined) return false;

        
        if (l.sign() > 0) return v == TruthValue::True;
        return v == TruthValue::False;
    }

    bool Solver::falsified(Literal l) const {
        return satisfied(l.negate());
    }

    bool Solver::assign(Literal l) {
        Variable x = var(l);
        assert(x.get() < numVariables);

        if (falsified(l)) return false;

        if (satisfied(l)) return true;

        model[x.get()] = (l.sign() > 0) ? TruthValue::True : TruthValue::False;
        return true;
    }

    bool Solver::unitPropagate() {
        std::vector<Literal> queue = unitLiterals;
        std::size_t qHead = 0;

        while (qHead < queue.size()) {
            Literal l = queue[qHead++];
            
            Literal falselit = l.negate();
            auto &watchVec = watchLists[falselit.get()];

            std::size_t i = 0;
            while (i < watchVec.size()) {
                ClausePointer c = watchVec[i];

                // Identify which watcher is the falsified one 
                short rank = c->getRank(falselit);
                //  If for some reason it's not a watcher anymore, skip it
                if (rank == -1) {
                    ++i;
                    continue;
                }

                short otherRank = (rank == 0) ? 1 : 0;
                Literal other = c->getWatcherByRank(otherRank);

                // If the other watcher is satisfied, clause is satisfied
                if (satisfied(other)) {
                    ++i;
                    continue;
                }

                // Try to find a replacement watcher that is not falsified
                bool moved = false;
                for (auto cand : *c) {
                    if (cand == other) continue;
                    if (cand == falselit) continue;

                    if (!falsified(cand)) {
                        bool ok = c->setWatcher(cand, rank);
                        (void)ok;
                        watchVec[i] = watchVec.back();
                        watchVec.pop_back();
                        watchLists[cand.get()].push_back(c);
                        moved = true;
                        break;
                    }
                }

                if (moved) {
                    // do not increment i because we swapped in a new element
                    continue;
                }

                // No replacement found => clause is unit or conflict TBD ??
                if (falsified(other)) {
                    // both watchers falsified => conflict
                    return false;
                }

                if (!assign(other)) return false;

                auto it = std::find(unitLiterals.begin(), unitLiterals.end(), other);
                if (it == unitLiterals.end()) unitLiterals.emplace_back(other);

                queue.push_back(other);

                ++i; 
            }
        }

        return true;
    }
} // sat
