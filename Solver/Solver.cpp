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
#include "heuristics.hpp"

namespace sat {
    

    static std::size_t luby(std::size_t i) {
        std::size_t k = 1;
        while ((1ULL << k) - 1 < i) ++k;
        while (i != (1ULL << k) - 1) {
            i = i - ((1ULL << (k - 1)) - 1);
            k = 1;
            while ((1ULL << k) - 1 < i) ++k;
        }
        return 1ULL << (k - 1);
    }
    
   

    SolveStatus Solver::dpll(WeightedDegree &h, std::size_t &decisionBudget) {
    if (!unitPropagate()) {
        if (!lastConflictVars.empty()) {
            h.onConflict(lastConflictVars);
        }
        return SolveStatus::Unsat;
    }

    std::size_t open = 0;
    for (auto v : model) {
        if (v == TruthValue::Undefined) ++open;
    }
    if (open == 0) {
        return SolveStatus::Sat;
    }

    if (decisionBudget == 0) {
        return SolveStatus::Restart;
    }

    Variable x = h(model, open);
    --decisionBudget;

    // branch True
    {
        Solver s1 = clone();
        if (s1.assign(pos(x))) {
            SolveStatus st = s1.dpll(h, decisionBudget);
            if (st == SolveStatus::Sat) { *this = std::move(s1); return SolveStatus::Sat; }
            if (st == SolveStatus::Restart) return SolveStatus::Restart;
        }
    }

    // branch False
    {
        Solver s2 = clone();
        if (s2.assign(neg(x))) {
            SolveStatus st = s2.dpll(h, decisionBudget);
            if (st == SolveStatus::Sat) { *this = std::move(s2); return SolveStatus::Sat; }
            if (st == SolveStatus::Restart) return SolveStatus::Restart;
        }
    }

    return SolveStatus::Unsat;
}


 Solver::Solver(unsigned numVariables)
        : numVariables(numVariables),
          model(numVariables, TruthValue::Undefined),
          watchLists(2u * numVariables) {}

     bool Solver::solve() {
    Solver base = clone();
    WeightedDegree h(numVariables, 1.0, 0.95);

    const std::size_t baseBudget = 200;
    const std::size_t maxRestarts = 50;

    for (std::size_t r = 1; r <= maxRestarts; ++r) {
        Solver attempt = base.clone();
        std::size_t budget = baseBudget * luby(r);

        SolveStatus st = attempt.dpll(h, budget);

        if (st == SolveStatus::Sat) {
            *this = std::move(attempt);
            return true;
        }
        if (st == SolveStatus::Unsat) {
            return false;
        }

        // restart
        h.decay();
    }

    return false;
}



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

        auto it = std::find(unitLiterals.begin(), unitLiterals.end(), u);
        if (it == unitLiterals.end()) unitLiterals.emplace_back(u);

        if (falsified(u)) return false;

        return true;
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
    return true;
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

    // store assignment as unit literal (tests expect this)
    auto it = std::find(unitLiterals.begin(), unitLiterals.end(), l);
    if (it == unitLiterals.end()) unitLiterals.emplace_back(l);

    return true;
}

    bool Solver::unitPropagate() {
    std::vector<Literal> queue = unitLiterals;
    std::size_t qHead = 0;
    lastConflictVars.clear();


    while (qHead < queue.size()) {
        Literal l = queue[qHead++];

        if (!assign(l)) return false;

        Literal falselit = l.negate();
        auto &watchVec = watchLists[falselit.get()];

        std::size_t i = 0;
        while (i < watchVec.size()) {
            ClausePointer c = watchVec[i];

            short rank = c->getRank(falselit);
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
                continue;
            }

            if (falsified(other)) {
                // conflict: store vars from conflicting clause for heuristic update
                lastConflictVars.clear();
                lastConflictVars.reserve(c->size());
                for (auto lit : *c) {
                    lastConflictVars.emplace_back(var(lit));
                }
                return false;
            }


            if (!assign(other)) return false;

            queue.push_back(other);

            ++i;
        }
    }

    return true;
}

 /*
     * IMPORTANT:
     * Clause objects contain mutable watcher indices. Therefore, we must deep-copy clauses for branching,
     * otherwise different branches share the same Clause instances and interfere.
     */
    Solver Solver::clone() const {
        Solver s(numVariables);
        s.model = model;
        s.unitLiterals = unitLiterals;

        // recreate clauses with new Clause instances
        s.clauses.reserve(clauses.size());
        for (const auto &cp : clauses) {
            ClausePointer np = std::make_shared<Clause>(*cp); // deep copy Clause (literals + watcher indices)
            s.clauses.emplace_back(np);
        }

        // rebuild watchLists
        s.watchLists.assign(2u * numVariables, {});
        for (const auto &cp : s.clauses) {
            if (cp->isEmpty()) continue;
            Literal w0 = cp->getWatcherByRank(0);
            Literal w1 = cp->getWatcherByRank(1);
            s.watchLists[w0.get()].push_back(cp);
            if (!(w1 == w0)) {
                s.watchLists[w1.get()].push_back(cp);
            }
        }

        return s;
    }
    std::vector<Literal> Solver::getUnitLiterals() const {
    return unitLiterals;
    }
        
    bool Solver::solveFirstVariable() {
    return dpllFirstVariable();
}

bool Solver::dpllFirstVariable() {
    // 1) Unit propagation
    if (!unitPropagate()) return false;

    // 2) Check if all assigned
    std::size_t open = 0;
    for (auto v : model) {
        if (v == TruthValue::Undefined) ++open;
    }
    if (open == 0) return true;

    // 3) Choose next variable (FirstVariable)
    FirstVariable hv;
    Variable x = hv(model, open);

    // 4) Branch True
    {
        Solver s1 = clone();
        if (s1.assign(pos(x)) && s1.dpllFirstVariable()) {
            *this = std::move(s1);
            return true;
        }
    }

    // 5) Branch False
    {
        Solver s2 = clone();
        if (s2.assign(neg(x)) && s2.dpllFirstVariable()) {
            *this = std::move(s2);
            return true;
        }
    }

    return false;
}



        



   


} // sat
