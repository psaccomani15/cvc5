#include "cvc5_private.h"
#ifndef CVC5__THEORY__FF__PACHECK_RULES_H
#define CVC5__THEORY__FF__PACHECK_RULES_H

#include <string>
namespace cvc5::internal {

namespace theory {

namespace ff {

enum class PacheckRule : uint32_t
{
  Axiom,
  Modulus,
  LinComp,
  Branch,
  Root,
  Exhaust
};

std::string pacheckRuleToString(PacheckRule id);
std::ostream& operator<<(std::ostream& out, PacheckRule id);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

// Axiom rule
// Delete rule -> will not be used
// Modulus rule
// LinComp rule
// Branch instantiation
// Root Declaration
#endif /* CVC5__THEORY__FF__PACHECK_RULES_H */
