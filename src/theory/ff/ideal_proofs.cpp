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
#include "proof/proof_node.h"
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
std::string buildName(size_t id)
{
  std::ostringstream name;
  name << "Internal Ideal Proofs id: " << id;
  return name.str();
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
                       size_t id,
                       const std::vector<CoCoA::RingElem>& inputs,
                       Node nonNullVarPred,
                       CoCoA::ideal cocoaIdeal)
    : EnvObj(env),
      d_cocoaIdeal(cocoaIdeal),
      d_validFact(nonNullVarPred),
      d_branchPolyProof(),
      d_branchPolyRoots(),
      d_childrenProofs(),
      d_proof(env, nullptr, buildName(id)),
      d_id(id)

{
  //  std::string name = buildName(id);
  // d_proof(env, nullptr, name);
  std::vector<Node> polys;
  NodeManager* nm = nodeManager();
  for (auto gen : inputs)
  {
    Node polyVar = nm->mkBoundVar(ostring(gen), nm->sExprType());
    polys.push_back(polyVar);
  }
  d_ideal = nm->mkNode(Kind::SEXPR, polys);
  d_membershipProofs = new GBProof(env, inputs, d_ideal, &d_proof);
}
Node IdealProof::getSatFact() { return d_validFact; }
Node IdealProof::getUnsatFact() { return d_emptyVarFact; }

Node IdealProof::oneInUnsat(CoCoA::RingElem p, CDProof* globalTheoryProofs)
{
  d_emptyVarFact
    = nodeManager()->mkNode(Kind::NOT, d_validFact);
  Node membershipFact = d_membershipProofs->getMembershipFact(p);
  d_proof.addStep(
      d_emptyVarFact, ProofRule::FF_ONE_UNSAT, {membershipFact}, {});
  std::shared_ptr<ProofNode> emptyVarProof = d_proof.getProof(d_emptyVarFact);
  globalTheoryProofs->addProof(emptyVarProof);
  return d_emptyVarFact;
}

Node IdealProof::oneInUnsat(CoCoA::RingElem p){
  d_emptyVarFact
    = nodeManager()->mkNode(Kind::NOT, d_validFact);
  Node membershipFact = d_membershipProofs->getMembershipFact(p);
  d_proof.addStep(
      d_emptyVarFact, ProofRule::FF_ONE_UNSAT, {membershipFact}, {});
  return d_emptyVarFact;
  }
void IdealProof::setFunctionPointers()
{
  d_membershipProofs->setFunctionPointers();
}

void IdealProof::enableProofHooks()
{
  CoCoA::proofEnabled = true;
}
void IdealProof::disableProofHooks()
{
  CoCoA::proofEnabled = false;
}

void IdealProof::registerBranchPolynomial(CoCoA::RingElem branchPoly)
{
  Trace("ff::trace") << "registering Proof for branchPoly: " << branchPoly
                     << std::endl;
  NodeManager* nm = nodeManager();
  d_branchPoly = nm->mkBoundVar(ostring(branchPoly), nm->sExprType());
  d_branchPolyProof =
      d_membershipProofs->proofIdealMembership(branchPoly, d_cocoaIdeal);
  Trace("ff::trace") << d_branchPolyProof << std::endl;
}

void IdealProof::registerRoots(std::vector<CoCoA::RingElem> roots)
{
  for (auto root : roots)
  {
    NodeManager* nm = nodeManager();
    Node rootRepr = nm->mkBoundVar(ostring(root), nm->sExprType());
    d_branchPolyRoots.push_back(rootRepr);
  }
}
std::shared_ptr<IdealProof> IdealProof::registerConclusion(
    CoCoA::RingElem choicePoly, CoCoA::ideal newIdeal)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> polysRepr{
      nm->mkBoundVar(ostring(choicePoly), nm->sExprType())};
  std::vector<CoCoA::RingElem> newGens{choicePoly};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal)){
    newGens.push_back(poly);
    polysRepr.push_back(nm->mkBoundVar(ostring(poly), nm->sExprType()));
  }
  Node idealRepr = nm->mkNode(Kind::SEXPR, polysRepr);
  Node nonNullVarPred = produceNonNullVarPred(idealRepr);
  //  Trace("ff::trace") << "Created new idealProof object\n";
  std::shared_ptr<IdealProof> childrenProof(
      new IdealProof(d_env, d_id + 1, newGens, nonNullVarPred, newIdeal));
  d_childrenProofs.push_back(childrenProof);
  return childrenProof;
}

void IdealProof::finishProof(bool rootBranching, CDProof* globalTheoryProofs)
{
  std::vector<Node> childrenSatFact;
  std::vector<Node> childrenUnsatFact;
  for (auto internalProofs : d_childrenProofs)
  {
    childrenSatFact.push_back(internalProofs->getSatFact());
    childrenUnsatFact.push_back(internalProofs->getUnsatFact());
  }
  Node conclusion = nodeManager()->mkOr(childrenSatFact);
  std::vector<Node> premises{d_validFact};
  std::vector<Node> arguments{};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
    premises.push_back(d_membershipProofs->getMembershipFact(poly));
  if (rootBranching)
  {
    premises.push_back(d_branchPolyProof);
    arguments = d_branchPolyRoots;
    arguments.push_back(d_branchPoly);
    d_proof.addStep(conclusion, ProofRule::FF_ROOT_BRANCH, premises, arguments);
  }
  else
  {
    d_proof.addStep(
        conclusion, ProofRule::FF_EXHAUST_BRANCH, premises, arguments);
  }
  Node falseNode;
  if (!d_childrenProofs.size())
    falseNode = conclusion;
  else
  {
    falseNode = nodeManager()->mkConst<bool>(false);
    Node trueNode = nodeManager()->mkConst<bool>(true);
    std::vector<Node> polarity;
    std::vector<Node> pivot;
    std::vector<Node> resolutionPremises{conclusion};
    for (Node unsatFacts : childrenUnsatFact)
    {
      d_proof.addProof(globalTheoryProofs->getProofFor(unsatFacts));
      resolutionPremises.push_back(unsatFacts);
    }
    for (size_t it = 0; it < childrenSatFact.size(); ++it)
      polarity.push_back(trueNode);
    for (Node satFact : childrenSatFact) pivot.push_back(satFact);
    d_proof.addStep(falseNode,
                    ProofRule::CHAIN_RESOLUTION,
                    resolutionPremises,
                    {nodeManager()->mkNode(Kind::SEXPR, polarity),
                     nodeManager()->mkNode(Kind::SEXPR, pivot)});
  }
  d_emptyVarFact = nodeManager()->mkNode(Kind::NOT, d_validFact);
  d_proof.addStep(d_emptyVarFact, ProofRule::SCOPE, {falseNode}, {d_validFact});
  globalTheoryProofs->addProof(d_proof.getProof(d_emptyVarFact));
  std::shared_ptr<ProofNode> pf = d_proof.getProofFor(conclusion);
  std::ostringstream pfStr;
  //(pf.get())->printDebug(pfStr, true);
  Trace("ff::trace") << "Conclusion Node " << conclusion << std::endl;
  Trace("ff::trace") << "Conclusion pf Node " << pfStr.str() << std::endl;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
