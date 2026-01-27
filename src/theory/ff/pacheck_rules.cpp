
#include "theory/ff/pacheck_rules.h"

#include "cvc5_private.h"

namespace cvc5::internal {

namespace theory {

namespace ff {

std::string pacheckRuleToString(PacheckRule id)
{
  switch (id)
  {
    case PacheckRule::Axiom: return "a";
    case PacheckRule::Branch: return "b";
    case PacheckRule::LinComp: return "%";
    case PacheckRule::Modulus: return "m";
    case PacheckRule::Root: return "r";
  }
}

std::ostream& operator<<(std::ostream& out, PacheckRule id)
{
  out << pacheckRuleToString(id);
  return out; 
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
