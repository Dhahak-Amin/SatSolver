/**
* @author Tim Luchterhand
* @date 29.11.24
* @brief
*/

#include <Iterators.hpp>

#include "heuristics.hpp"
#include "util/exception.hpp"

namespace sat {

    Variable FirstVariable::operator()(const std::vector<TruthValue> &model, std::size_t) const {
        for (auto [varId, val]: iterators::enumerate(model, 0u)) {
            if (val == TruthValue::Undefined) {
                return Variable(varId);
            }
        }

        throw std::runtime_error("Found no open variable");
    }

    Variable Heuristic::operator()(const std::vector<TruthValue> &values, std::size_t numOpenVariables) const {
        if (nullptr == impl) {
            throw BadHeuristicCall("heuristic wrapper does not contain a heuristic");
        }

        return impl->invoke(values, numOpenVariables);
    }

    bool Heuristic::isValid() const {
        return nullptr != impl;
    }

        Variable WeightedDegree::operator()(const std::vector<TruthValue> &model, std::size_t) const {
        double bestW = -1.0;
        unsigned bestId = 0;
        bool found = false;

        for (unsigned i = 0; i < model.size(); ++i) {
            if (model[i] == TruthValue::Undefined) {
                double w = weight[i];
                if (!found || w > bestW || (w == bestW && i < bestId)) {
                    bestW = w;
                    bestId = i;
                    found = true;
                }
            }
        }

        if (!found) {
            throw std::runtime_error("Found no open variable");
        }
        return Variable(bestId);
    }

    void WeightedDegree::onConflict(const std::vector<Variable> &vars) {
        for (auto v : vars) {
            if (v.get() < weight.size()) {
                weight[v.get()] += bumpAmount;
            }
        }
    }

    void WeightedDegree::decay() {
        for (auto &w : weight) {
            w *= (1.0 / decayFactor); // small “boost” effect over time
        }
    }



}
