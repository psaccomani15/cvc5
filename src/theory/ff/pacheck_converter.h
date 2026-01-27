
#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PACHECK_CONVERTER_H
#define CVC5__THEORY__FF__PACHECK_CONVERTER_H

#include "theory/ff/pacheck_rules.h"
#include "theory/theory.h"
#include "theory/ff/cocoa_util.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"
#include <string>
namespace cvc5::internal {

namespace theory {

namespace ff {
class PacheckPolynomial
{
 public:
  PacheckPolynomial(std::string poly, size_t id);
  std::string getRepr() {return d_polyRepr;}
  size_t getId() {return d_id;}
 private:
  std::string d_polyRepr;
  size_t d_id;
  
};
class PacheckProofPrinter : protected EnvObj
{
 public:
  PacheckProofPrinter(Env& env, const FfSize& size, CDProof& cdp);
  ~PacheckProofPrinter() {};
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  PacheckPolynomial nodeToPoly(Node poly);
  std::string convertPP(Node pp);
  std::string convertVar(Node var);
  void printInternal(std::ostream& out, std::shared_ptr<ProofNode> pfn, size_t branchSize);
  const FfSize& d_size;
  size_t d_maxId;
  CDProof* d_proof;
  std::unordered_map<Node, PacheckPolynomial> d_nodeToPacheckPoly;
  std::unordered_map<Node, std::string> d_varToPacheckVar;
};
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5__THEORY__FF__PACHECK_CONVERTER_H */
