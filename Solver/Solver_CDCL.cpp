
#include "Solver_CDCL.hpp"
#include <algorithm>
#include <cassert>
#include <set>

namespace sat_cdcl {


SolverCDCL::SolverCDCL(unsigned numVariables)
    : numVariables(numVariables),
      model(numVariables, TruthValue::Undefined),
      watchLists(2u * numVariables),
      decisionLevel(0),
      qHead(0),
      reason(numVariables, nullptr),
      level(numVariables, 0),
      activity(numVariables, 0.0),
      activityIncrement(1.0),
      activityDecay(0.95)
{
    trail.reserve(numVariables);
}


TruthValue SolverCDCL::val(Variable x) const {
    assert(x.get() < numVariables);
    return model[x.get()];
}

bool SolverCDCL::satisfied(Literal l) const {
    TruthValue v = val(var(l));
    if (v == TruthValue::Undefined) return false;
    return (l.sign() > 0) ? (v == TruthValue::True) : (v == TruthValue::False);
}

bool SolverCDCL::falsified(Literal l) const {
    return satisfied(l.negate());
}



bool SolverCDCL::assign(Literal l, ClausePtr r) {
    Variable x = var(l);
    
    if (falsified(l)) {
        return false;
    }
    
    if (satisfied(l)) {
        return true;
    }
    
    model[x.get()] = (l.sign() > 0) ? TruthValue::True : TruthValue::False;
    level[x.get()] = decisionLevel;
    reason[x.get()] = r; 
    
    trail.push_back(l);
    
    return true;
}

ClausePtr SolverCDCL::unitPropagate() {
    while (qHead < trail.size()) {
        Literal l = trail[qHead++];
        
       
        Literal falseLit = l.negate();
        auto& watchVec = watchLists[falseLit.get()];

        std::size_t i = 0;
        while (i < watchVec.size()) {
            ClausePtr c = watchVec[i];
            
            // Trouve le rang du watcher falsifié
            short rank = c->getRank(falseLit);
            if (rank == -1) {
                ++i;
                continue;
            }

            short otherRank = (rank == 0) ? 1 : 0;
            Literal other = c->getWatcherByRank(otherRank);

            if (satisfied(other)) {
                ++i;
                continue;
            }

            bool moved = false;
            for (auto cand : *c) {
                if (cand == other || cand == falseLit) continue;
                
                if (!falsified(cand)) {
                    c->setWatcher(cand, rank);
                    
                    watchVec[i] = watchVec.back();
                    watchVec.pop_back();
                    
                    watchLists[cand.get()].push_back(c);
                    
                    moved = true;
                    break;
                }
            }

            if (moved) continue;

     
            
            if (falsified(other)) {
                
                return c;  
            }

            if (!assign(other, c)) {
                return c;  
            }

            ++i;
        }
    }

    return nullptr;
}


void SolverCDCL::analyzeConflict(ClausePtr conflict, std::vector<Literal>& outLearnt, unsigned& outBacktrackLevel) {
    outLearnt.clear();
    outBacktrackLevel = 0;
    
    if (decisionLevel == 0) return;

    int pathC = 0;
    Literal p = sat::Literal(0); 

    outLearnt.push_back(sat::Literal(0)); 
    ClausePtr c = conflict;
    
    int index = trail.size() - 1;

    
    std::vector<bool> seen(numVariables, false);

    do {
        if (c == nullptr) break; 

        
        for (auto q : *c) {
            Variable v = var(q);
            
            if (q == p.negate()) continue; 
            
            if (!seen[v.get()] && level[v.get()] > 0) {
                seen[v.get()] = true;
                bumpActivity(v); 

                if (level[v.get()] >= decisionLevel) {
                    pathC++; 
                } else {
                    outLearnt.push_back(q); 
                }
            }
        }
        
      
        while (index >= 0 && !seen[var(trail[index]).get()]) {
            index--;
        }
        
        if (index < 0) break; 
        
        p = trail[index--];
        c = reason[var(p).get()]; 
       
        seen[var(p).get()] = false; 
        pathC--;

    } while (pathC > 0);

   
    outLearnt[0] = p.negate();
    
    decayActivities();
    

    if (outLearnt.size() == 1) {
        outBacktrackLevel = 0;
    } else {
        unsigned maxLvl = 0;
        int maxIdx = 1;
        
        for (size_t i = 1; i < outLearnt.size(); i++) {
            unsigned lvl = level[var(outLearnt[i]).get()];
            if (lvl > maxLvl) {
                maxLvl = lvl;
                maxIdx = (int)i;
            }
        }
        outBacktrackLevel = maxLvl;
        
        std::swap(outLearnt[1], outLearnt[maxIdx]);
    }
}



void SolverCDCL::backjumpTo(unsigned targetLevel) {
    while (!trail.empty()) {
        Literal l = trail.back();
        Variable v = var(l);
        
        if (level[v.get()] <= targetLevel) {
            break;  
        }
        
        model[v.get()] = TruthValue::Undefined;
        reason[v.get()] = nullptr;
        level[v.get()] = 0;
        
        trail.pop_back();
    }
    
    while (!trailLim.empty() && trailLim.back() > trail.size()) {
        trailLim.pop_back();
    }
    
    decisionLevel = targetLevel;
    
    qHead = trail.size();
}


Variable SolverCDCL::selectVariable() const {
    double bestActivity = -1.0;
    unsigned bestVar = 0;
    bool found = false;
    
    for (unsigned i = 0; i < numVariables; i++) {
        if (model[i] == TruthValue::Undefined) {
            if (!found || activity[i] > bestActivity) {
                bestActivity = activity[i];
                bestVar = i;
                found = true;
            }
        }
    }
    
    if (!found) {
        return Variable(0);
    }
    
    return Variable(bestVar);
}

void SolverCDCL::bumpActivity(Variable v) {
    activity[v.get()] += activityIncrement;
    
    if (activity[v.get()] > 1e100) {
        for (auto& a : activity) {
            a *= 1e-100;
        }
        activityIncrement *= 1e-100;
    }
}

void SolverCDCL::decayActivities() {
    activityIncrement /= activityDecay;
}


bool SolverCDCL::addClause(Clause clause) {
    if (clause.isEmpty()) return false;
    
    std::vector<Literal> newLits;
    for (auto l : clause) {
        if (satisfied(l)) {
            return true; 
        }
        if (!falsified(l)) {
            newLits.push_back(l);
        }
    }
    
    if (newLits.empty()) {
        return false;  
    }
    
    if (newLits.size() == 1) {
        
        return assign(newLits[0], nullptr);
    }
    
   
    ClausePtr cptr = std::make_shared<Clause>(Clause(std::move(newLits)));
    clauses.push_back(cptr);
    
    Literal w0 = cptr->getWatcherByRank(0);
    Literal w1 = cptr->getWatcherByRank(1);
    
    watchLists[w0.get()].push_back(cptr);
    if (!(w1 == w0)) {
        watchLists[w1.get()].push_back(cptr);
    }
    
    return true;
}

void SolverCDCL::addLearntClause(const std::vector<Literal>& learnt) {
    if (learnt.empty()) return;
    
    if (learnt.size() == 1) {
        assign(learnt[0], nullptr);
        return;
    }
    
    ClausePtr cptr = std::make_shared<Clause>(Clause(learnt));
    clauses.push_back(cptr);
    
    Literal w0 = cptr->getWatcherByRank(0);
    Literal w1 = cptr->getWatcherByRank(1);
    
    watchLists[w0.get()].push_back(cptr);
    if (!(w1 == w0)) {
        watchLists[w1.get()].push_back(cptr);
    }
    
 
    assign(learnt[0], cptr);
}



bool SolverCDCL::solve() {
    ClausePtr conflict = unitPropagate();
    
    if (conflict != nullptr) {
        return false;
    }
    
    // Boucle principale CDCL
    while (true) {
        std::size_t unassigned = 0;
        for (auto v : model) {
            if (v == TruthValue::Undefined) unassigned++;
        }
        
        if (unassigned == 0) {
            return true;
        }
        
        decisionLevel++;
        trailLim.push_back(trail.size());
        
        Variable x = selectVariable();
        

        assign(pos(x), nullptr);
        
        conflict = unitPropagate();
        
        while (conflict != nullptr) {
            
            if (decisionLevel == 0) {

                return false;
            }
            
            std::vector<Literal> learntClause;
            unsigned backtrackLevel;
            
            analyzeConflict(conflict, learntClause, backtrackLevel);
            
            if (learntClause.empty()) {
                return false;
            }
            

            backjumpTo(backtrackLevel);
            

            addLearntClause(learntClause);
            
            conflict = unitPropagate();
        }
    }
}



std::vector<Literal> SolverCDCL::getUnitLiterals() const {
    std::vector<Literal> result;
    result.reserve(numVariables);
    
    for (unsigned i = 0; i < numVariables; i++) {
        if (model[i] == TruthValue::True) {
            result.push_back(pos(Variable(i)));
        } else if (model[i] == TruthValue::False) {
            result.push_back(neg(Variable(i)));
        }
    }
    
    return result;
}

} // namespace sat_cdcl
