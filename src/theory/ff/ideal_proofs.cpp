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

#include <CoCoA/SparsePolyOps-ideal.H>
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
                       Node nonNullVarPred,
                       CoCoA::ideal cocoaIdeal,
                       CDProof* proof)
    : EnvObj(env),
      d_cocoaIdeal(cocoaIdeal),
      d_validFact(nonNullVarPred),
      d_branchPolyProof(),
      d_branchPolyRoots(),
      d_childrenProofs(),
      d_proof(proof)
{
  std::vector<Node> polys;
  NodeManager* nm = nodeManager();
  for (auto gen : inputs)
  {
    Node polyVar = nm->mkBoundVar(ostring(gen), nm->sExprType());
    polys.push_back(polyVar);
  }
  d_ideal = nm->mkNode(Kind::SEXPR, polys);
  d_membershipProofs = new GBProof(env, inputs, d_ideal, d_proof);
}

Node IdealProof::oneInUnsat(CoCoA::RingElem p)
{
  Node unsatVar = nodeManager()->mkNode(Kind::NOT, d_validFact);
  Node membershipFact = d_membershipProofs->getMembershipFact(p);
  d_proof->addStep(unsatVar, ProofRule::FF_ONE_UNSAT, {membershipFact}, {});
  return unsatVar;
}
void IdealProof::setFunctionPointers()
{
  d_membershipProofs->setFunctionPointers();
}

void IdealProof::registerBranchPolynomial(CoCoA::RingElem branchPoly)
{
  Trace("ff::trace") << "registering Proof for branchPoly: " << branchPoly << std::endl; 
  NodeManager* nm = nodeManager();
  d_branchPoly = nm->mkBoundVar(ostring(branchPoly), nm->sExprType());
  d_branchPolyProof =
      d_membershipProofs->proofIdealMembership(branchPoly, d_cocoaIdeal);
  Trace("ff::trace") << d_branchPolyProof << std::endl;
}

void IdealProof::registerRoots(std::vector<CoCoA::RingElem> roots) {
  for (auto root : roots)
  {
    NodeManager *nm = nodeManager(); 
    Node rootRepr = nm->mkBoundVar(ostring(root), nm->sExprType());
    d_branchPolyRoots.push_back(rootRepr);
  }
}
  IdealProof IdealProof::registerConclusion(CoCoA::RingElem choicePoly,
                                          CoCoA::ideal newIdeal)
{
  
  NodeManager* nm = nodeManager();
  std::vector<Node> polysRepr{
      nm->mkBoundVar(ostring(choicePoly), nm->sExprType())};
  std::vector<CoCoA::RingElem> newGens;
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
    polysRepr.push_back(nm->mkBoundVar(ostring(poly), nm->sExprType()));
  Node idealRepr = nm->mkNode(Kind::SEXPR, polysRepr);
  Node nonNullVarPred = produceNonNullVarPred(idealRepr);
  d_childrenProofs.push_back(nonNullVarPred);
  return IdealProof(d_env, newGens, nonNullVarPred, newIdeal, d_proof);
}

void IdealProof::finishProof(bool rootBranching)
{
  Node conclusion = nodeManager()->mkOr(d_childrenProofs);
  std::vector<Node> premises{d_validFact};
  std::vector<Node> arguments {};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
    premises.push_back(d_membershipProofs->getMembershipFact(poly));
  if (rootBranching)
  {
    premises.push_back(d_branchPolyProof);
    arguments = d_branchPolyRoots;
    arguments.push_back(d_branchPoly);
    d_proof->addStep(conclusion, ProofRule::FF_ROOT_BRANCH,premises, arguments);
  }
  else
  {
    d_proof->addStep(conclusion, ProofRule::FF_EXHAUST_BRANCH, premises, arguments);
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
