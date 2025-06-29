#include "cvc5_private.h"

#ifndef CVC5_THEORY_FF_PROOF_CHECKER_H
#define CVC5_THEORY_FF_PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"
namespace cvc5::internal {
namespace theory {
namespace ff {

class FfProofRuleChecker : public ProofRuleChecker
{
 public:
  FfProofRuleChecker(NodeManager* nm);
  void registerTo(ProofChecker* pc) override;

 protected:
  Node checkInternal(ProofRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_THEORY_FF_PROOF_CHECKER_H */
