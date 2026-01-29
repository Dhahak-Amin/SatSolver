

#ifndef HEURISTICS_CDCL_HPP
#define HEURISTICS_CDCL_HPP

#include <vector>
#include "basic_structures.hpp"

namespace sat_cdcl {

using sat::Variable;
using sat::TruthValue;


class VSIDS_CDCL {
public:
    std::vector<double> activity;
    double increment;
    double decayFactor;

    explicit VSIDS_CDCL(std::size_t numVars, double initialIncrement = 1.0, double decay = 0.95)
        : activity(numVars, 0.0),
          increment(initialIncrement),
          decayFactor(decay)
    {}

    
    Variable operator()(const std::vector<TruthValue>& model, std::size_t /*numOpen*/) const {
        double best = -1.0;
        unsigned bestIdx = 0;
        bool found = false;

        for (unsigned i = 0; i < model.size(); ++i) {
            if (model[i] == TruthValue::Undefined) {
                if (!found || activity[i] > best) {
                    best = activity[i];
                    bestIdx = i;
                    found = true;
                }
            }
        }

        return Variable(bestIdx);
    }

    
    void bump(Variable v) {
        activity[v.get()] += increment;

        // Renormalise si les valeurs deviennent trop grandes
        if (activity[v.get()] > 1e100) {
            for (auto& a : activity) {
                a *= 1e-100;
            }
            increment *= 1e-100;
        }
    }

    
    void decay() {
        increment /= decayFactor;
    }
};


struct FirstVariable_CDCL {
    Variable operator()(const std::vector<TruthValue>& model, std::size_t /*numOpen*/) const {
        for (unsigned i = 0; i < model.size(); ++i) {
            if (model[i] == TruthValue::Undefined) {
                return Variable(i);
            }
        }
        return Variable(0);
    }
};


class WeightedDegree_CDCL {
public:
    std::vector<double> weight;
    double bumpAmount;
    double decayFactor;

    explicit WeightedDegree_CDCL(std::size_t numVars, double bump = 1.0, double decay = 0.95)
        : weight(numVars, 1.0),
          bumpAmount(bump),
          decayFactor(decay)
    {}

    Variable operator()(const std::vector<TruthValue>& model, std::size_t /*numOpen*/) const {
        double bestW = -1.0;
        unsigned bestId = 0;
        bool found = false;

        for (unsigned i = 0; i < model.size(); ++i) {
            if (model[i] == TruthValue::Undefined) {
                if (!found || weight[i] > bestW) {
                    bestW = weight[i];
                    bestId = i;
                    found = true;
                }
            }
        }

        return Variable(bestId);
    }

    void onConflict(const std::vector<Variable>& vars) {
        for (auto v : vars) {
            if (v.get() < weight.size()) {
                weight[v.get()] += bumpAmount;
            }
        }
    }

    void decay() {
        for (auto& w : weight) {
            w *= decayFactor;
        }
    }
};



} // namespace sat_cdcl

#endif // HEURISTICS_CDCL_HPP
