
#ifndef SOLVER_CDCL_HPP
#define SOLVER_CDCL_HPP

#include <vector>
#include <memory>
#include "basic_structures.hpp"
#include "Clause.hpp"

namespace sat_cdcl {

    using sat::Literal;
    using sat::Variable;
    using sat::TruthValue;
    using sat::Clause;
    using sat::pos;
    using sat::neg;
    using sat::var;

    using ClausePtr = std::shared_ptr<Clause>;

   
    class SolverCDCL {
    public:
        explicit SolverCDCL(unsigned numVariables);

        
        bool addClause(Clause clause);

       
        bool solve();

       
        std::vector<Literal> getUnitLiterals() const;

        TruthValue val(Variable x) const;
        bool satisfied(Literal l) const;
        bool falsified(Literal l) const;

    private:
       
        
        unsigned numVariables;
        
        std::vector<TruthValue> model;
        
        std::vector<ClausePtr> clauses;
        
 
        std::vector<std::vector<ClausePtr>> watchLists;

   
        std::vector<Literal> trail;
        
      
        std::vector<std::size_t> trailLim;
        
     
        unsigned decisionLevel;

        std::size_t qHead;
     
        std::vector<ClausePtr> reason;
        
        std::vector<unsigned> level;

        

        bool assign(Literal l, ClausePtr r);

        
        ClausePtr unitPropagate();

        
        void analyzeConflict(ClausePtr conflict, std::vector<Literal>& outLearnt, unsigned& outBacktrackLevel);

       
        void backjumpTo(unsigned level);

       
        Variable selectVariable() const;

        
        void addLearntClause(const std::vector<Literal>& learnt);

        std::vector<double> activity;   // Score de chaque variable
        double activityIncrement;       // Quantité à ajouter lors d'un conflit
        double activityDecay;           // Facteur de décroissance

        void bumpActivity(Variable v);
        void decayActivities();
    };

} 

#endif // SOLVER_CDCL_HPP
