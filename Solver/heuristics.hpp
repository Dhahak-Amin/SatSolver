/**
* @author Tim Luchterhand
* @date 29.11.24
* @file heuristics.hpp
* @brief Contains different branching heuristics
*/

#ifndef HEURISTICS_HPP
#define HEURISTICS_HPP

#include <vector>
#include <memory>

#include "basic_structures.hpp"
#include "util/concepts.hpp"

namespace sat {
    /**
     * Concept modelling the heuristic interface. A heuristic is a type that can be called with a vector of truth
     * values (the model) and an unsigned integer representing the number of variables that are undecided and returns
     * a sat::Variable
     */
    template<typename H>
    concept heuristic = concepts::callable_r<H, Variable, const std::vector<TruthValue>, std::size_t>;

    /**
     * @brief Variable selection strategy that selects the first unassigned variable
     */
    struct FirstVariable {
        Variable operator()(const std::vector<TruthValue> &model, std::size_t) const;
    };

    namespace detail {
        /**
         * @brief This is a helper class for the implementation of a type erasure heuristic wrapper
         */
        struct HeuristicCallableBase {
            HeuristicCallableBase() = default;

            virtual ~HeuristicCallableBase() = default;

            HeuristicCallableBase(HeuristicCallableBase &&) = default;

            HeuristicCallableBase &operator=(HeuristicCallableBase &&) = default;

            HeuristicCallableBase(const HeuristicCallableBase &) = default;

            HeuristicCallableBase &operator=(const HeuristicCallableBase &) = default;

            virtual Variable invoke(const std::vector<TruthValue> &, std::size_t) = 0;
        };

        /**
         * @brief This is a helper class for the implementation of a type erasure heuristic wrapper
         */
        template<heuristic H>
        struct HeuristicCallable : HeuristicCallableBase {
            H impl;

            template<typename... Args>
            explicit HeuristicCallable(Args &&... args): impl(std::forward<Args>(args)...) {
            }

            Variable invoke(const std::vector<TruthValue> &values, std::size_t numOpenVariables) override {
                return impl(values, numOpenVariables);
            }
        };
    }

    /**
     * @brief Type erasure heuristic wrapper that can hold any type of heuristic
     */
    class Heuristic {
        std::unique_ptr<detail::HeuristicCallableBase> impl;
    public:
        /**
         * Default Ctor. Constructs an empty heuristic that must not be called
         */
        Heuristic() = default;

        /**
         * Ctor.
         * @tparam H Heuristic type
         * @param heuristic The heuristic to store in the wrapper
         */
        template<heuristic H>
        Heuristic(H &&heuristic): impl(
            std::make_unique<detail::HeuristicCallable<std::remove_cvref_t<H>>>(std::forward<H>(heuristic))) {
        }

        Variable operator()(const std::vector<TruthValue> &values, std::size_t numOpenVariables) const;

        /**
         * Whether the wrapper holds a valid heuristic
         * @return true if heuristic wrapper is valid, false otherwise
         */
        bool isValid() const;
    };

    /**
     * @brief Wrapper for heuristics that do not support move construction or assignment
     * @tparam H heuristic type
     */
    template<heuristic H>
    class MovableHeuristic {
        std::unique_ptr<H> h;
    public:
        /**
         * Ctor
         * @tparam Args argument types
         * @param args ctor arguments to heuristic
         */
        template<typename... Args>
        explicit MovableHeuristic(Args &&...args): h(std::make_unique<H>(std::forward<Args>(args)...)) {}

        Variable operator()(const std::vector<TruthValue> &values, std::size_t numOpenVariables) const {
            return h->operator()(values, numOpenVariables);
        }
    };

        /**
     * @brief Dynamic heuristic: Weighted Degree (simple version)
     * @details
     * Keeps a weight per variable. On conflicts, weights of variables involved are increased.
     * Next decision variable = unassigned var with maximum weight (tie -> smallest id).
     */
    struct WeightedDegree {
        std::vector<double> weight;
        double bumpAmount = 1.0;
        double decayFactor = 0.95;

        explicit WeightedDegree(std::size_t numVars, double bump = 1.0, double decay = 0.95)
            : weight(numVars, 1.0), bumpAmount(bump), decayFactor(decay) {}

        Variable operator()(const std::vector<TruthValue> &model, std::size_t) const;

        
        void onConflict(const std::vector<Variable> &vars);

        
        void decay();
    };


    


}

#endif //HEURISTICS_HPP
