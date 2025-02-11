#include <sstream>
#include "cvc5_public.h"
#ifndef CVC5__FINITE_FIELDIDEAL_H
#define CVC5__FINITE_FIELDIDEAL_H

#include <vector>
#include <string>
#include "expr/node.h"

namespace cvc5::internal{
class FiniteFieldIdeal
{
 public:
  
  std::string toString(){
    std::ostringstream str;
    str << "<";
    for(auto term )

  } 
  size_t hash() const;
 private:
  /** A vector of terms that represents polynomials. */
  const std::vector<Node> d_gens; 
};
}
#endif
