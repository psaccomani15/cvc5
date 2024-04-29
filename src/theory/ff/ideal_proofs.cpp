/******************************************************************************
 *
 *
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields Ideal Proof Construction
 */

#if CVC5_USE_COCOA

#include "theory/ff/ideal_proofs.h"

#include <CoCoA/TmpGPoly.H>

#include <sstream>

#include "proof/proof.h"
#include "smt/assertions.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

Node produceNonNullVarPred(Node ideal)
{
  TypeNode typeOfIdealB = ideal.getType();
  NodeManager* nm = NodeManager::currentNM();
  TypeNode pType = nm->mkFunctionType(typeOfIdealB, nm->booleanType());
  Node nonNullVarietySymb = nm->mkBoundVar("nonNullVariety", pType);
  Node nonNullVarietyPred =
      nm->mkNode(Kind::APPLY_UF, nonNullVarietySymb, ideal);
  return nonNullVarietyPred;
}
IdealProof::IdealProof(Env& env,
                       const std::vector<CoCoA::RingElem>& inputs,
                       Node varNonEmpty,
                       CDProof* proof)
    : EnvObj(env), d_validFact(varNonEmpty), d_proof(proof)
{
  std::vector<Node> polys;
  NodeManager* nm = NodeManager::currentNM();
  for (auto gen : inputs)
  {
    Node polyVar = nm->mkBoundVar(ostring(gen), nm->sExprType());
    polys.push_back(polyVar);
  }
  d_ideal = nm->mkNode(Kind::SEXPR, polys);
  d_membershipProofs = new GBProof(env, inputs, d_ideal, d_proof);
  d_membershipProofs->setFunctionPointers();
};

 Node IdealProof::oneInUnsat(CoCoA::RingElem p) {
   Node unsatVar = nodeManager()->mkNode(Kind::NOT, d_validFact);
   Node membershipFact = d_membershipProofs->getMembershipFact(p);
   d_proof->addStep(unsatVar, ProofRule::FF_ONE_UNSAT, {membershipFact}, {});
   return unsatVar;
 }
 void IdealProof::setFunctionPointers()
{
  d_membershipProofs->setFunctionPointers();
}

/* TODO: ADD SUPPORT FOR BRANCHING PROOFS*/
// std::vector<IdealProof> IdealProof::registerRootBranch(
//     CoCoA::RingElem poly,
//     std::vector<CoCoA::RingElem> roots,
//     std::vector<CoCoA::RingElem> basis)
// {
//   std::vector<Node> premises {d_validFact};
//   Node polyMembership = d_membershipProofs->proofIdealMembership(poly);
//   premises.push_back(polyMembership);
//   for (auto gen : basis)
//   {
//     premises.push_back(d_membershipProofs->getMembershipFact(gen));
//   }

// }

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
