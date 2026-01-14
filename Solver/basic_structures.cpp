/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include "basic_structures.hpp"
#include "util/exception.hpp"

namespace sat {
    // @TODO implementation here

    Variable::Variable(unsigned val) : val(val) {}

    unsigned Variable::get() const {
        return val;
    }

    bool Variable::operator==(Variable other) const {
        return val == other.val;
    }

    Literal::Literal(unsigned val) : val(val) {}

    unsigned Literal::get() const {
        return val;
    }

    Literal Literal::negate() const {
        // flip last bit: even <-> odd (negative <-> positive)
        return Literal(val ^ 1u);
    }

    short Literal::sign() const {
        // even => negative => -1, odd => positive => +1
        return (val & 1u) ? (short) +1 : (short) -1;
    }

    bool Literal::operator==(Literal other) const {
        return val == other.val;
    }

    Literal pos(Variable x) {
        // positive literal => odd id = 2*var + 1
        return Literal(2u * x.get() + 1u);
    }

    Literal neg(Variable x) {
        // negative literal => even id = 2*var
        return Literal(2u * x.get());
    }

    Variable var(Literal l) {
        // var id = lit id / 2
        return Variable(l.get() / 2u);
    }
}
