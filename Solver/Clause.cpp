/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include <cassert>
#include <algorithm>

#include "Clause.hpp"
#include "util/exception.hpp"

namespace sat {
    //TODO implementation here

    Clause::Clause(std::vector<Literal> literals) : literals(std::move(literals)) {
        // Initialize watchers (watch literals)
        if (this->literals.empty()) {
            watcherIdx0 = 0;
            watcherIdx1 = 0;
        } else if (this->literals.size() == 1) {
            watcherIdx0 = 0;
            watcherIdx1 = 0; 
        } else {
            watcherIdx0 = 0;
            watcherIdx1 = 1;
        }
    }

    short Clause::getRank(Literal l) const {
        if (literals.empty()) return -1;

        if (literals[watcherIdx0] == l) return 0;
        if (literals[watcherIdx1] == l) return 1;
        return -1;
    }

    std::size_t Clause::getIndex(short rank) const {
        // rank: 0 -> first watcher, otherwise -> second watcher
        return (rank == 0) ? watcherIdx0 : watcherIdx1;
    }

    bool Clause::setWatcher(Literal l, short watcherNo) {
        // watcherNo should be 0 or 1
        assert(watcherNo == 0 || watcherNo == 1);

        auto it = std::find(literals.begin(), literals.end(), l);
        if (it == literals.end()) return false;

        std::size_t idx = static_cast<std::size_t>(std::distance(literals.begin(), it));
        if (watcherNo == 0) watcherIdx0 = idx;
        else watcherIdx1 = idx;
        return true;
    }

    auto Clause::begin() const -> std::vector<Literal>::const_iterator {
        return literals.begin();
    }

    auto Clause::end() const -> std::vector<Literal>::const_iterator {
        return literals.end();
    }

    bool Clause::isEmpty() const {
        return literals.empty();
    }

    Literal Clause::operator[](std::size_t index) const {
        assert(index < literals.size());
        return literals[index];
    }

    std::size_t Clause::size() const {
        return literals.size();
    }

    Literal Clause::getWatcherByRank(short rank) const {
        assert(!literals.empty());
        return literals[getIndex(rank)];
    }

    bool Clause::sameLiterals(const Clause &other) const {
        if (literals.size() != other.literals.size()) return false;

        std::vector<Literal> a = literals;
        std::vector<Literal> b = other.literals;

        auto cmp = [](Literal x, Literal y) {
            return x.get() < y.get();
        };

        std::sort(a.begin(), a.end(), cmp);
        std::sort(b.begin(), b.end(), cmp);

        for (std::size_t i = 0; i < a.size(); ++i) {
            if (!(a[i] == b[i])) return false;
        }
        return true;
    }

}
