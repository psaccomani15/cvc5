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
  /** A representation of the polynomial ideal of a given, known Finite Field */
 FiniteFieldIdeal(const std::vector<Node> generators) : d_gens(generators){}
  /** Return a string representation of the Ideal: The vector of generators enclosed by <> symbols. */
  std::string toString() const; 
  size_t hash() const;
 private:
  /** A vector of terms that represents polynomials. */
  const std::vector<Node> d_gens; 
};
}
#endif
