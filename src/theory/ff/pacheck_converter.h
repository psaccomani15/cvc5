
#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PACHECK_CONVERTER_H
#define CVC5__THEORY__FF__PACHECK_CONVERTER_H

#include <string>

#include "proof/proof_node.h"
#include "proof/proof.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_util.h"
#include "theory/ff/pacheck_rules.h"
#include "theory/theory.h"

namespace cvc5::internal {
class CDProof;
namespace theory {

namespace ff {
class PacheckPolynomial
{
 public:
  PacheckPolynomial(std::string poly, size_t id, size_t branch);
  std::string getRepr() { return d_polyRepr; }
  size_t getId() { return d_id; }
  size_t getBranch() { return d_branch; }

 private:
  std::string d_polyRepr;
  size_t d_id;
  size_t d_branch;
};
class PacheckProofPrinter : protected EnvObj
{
 public:
  PacheckProofPrinter(Env& env, const FfSize& size, CDProof& cdp);
  ~PacheckProofPrinter() {};
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  PacheckPolynomial nodeToPoly(Node poly, size_t branch);
  std::string convertPP(Node pp);
  std::string convertVar(Node var);
  void printInternal(std::ostream& out,
                     std::shared_ptr<ProofNode> pfn,
                     size_t branchSize);
  const FfSize& d_size;
  size_t d_maxId;
  size_t d_varId;
  CDProof* d_proof;
  std::unordered_map<Node, PacheckPolynomial> d_nodeToPacheckPoly;
  std::unordered_map<Node, std::string> d_varToPacheckVar;
};
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5__THEORY__FF__PACHECK_CONVERTER_H */
