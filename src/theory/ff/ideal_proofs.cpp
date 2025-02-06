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
 * Finite fields Ideal Branching Proofs Generator 
 */

#include "theory/shared_terms_database.h"
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


std::string buildName(size_t id)
{
  std::ostringstream name;
  name << "Ideal Proofs id: " << id;
  return name.str();
}
IdealProof::IdealProof(Env& env,
                       size_t id,
                       const std::vector<CoCoA::RingElem>& inputs,
                       Node nonNullVarPred, CocoaEncoder &enc, 
                       CoCoA::ideal cocoaIdeal)
    : EnvObj(env),
      d_cocoaIdeal(cocoaIdeal),
      d_enc(enc),
      d_validFact(nonNullVarPred),
      d_branchPolyProof(),
      d_branchPolyRoots(),
      d_childrenProofs(),
      d_proof(env, nullptr, buildName(id)),
      d_id(id)
{
std::vector<Node> polys;
  NodeManager* nm = nodeManager();
  for(auto gen : inputs)
  {
    Node polyVar = d_enc.encodeBack(gen);
    polys.push_back(polyVar);
  }
  d_ideal = nm->mkNode(Kind::FINITE_FIELD_IDEAL, polys);
  d_membershipProofs = new GBProof(env, inputs, d_ideal, enc, &d_proof);
}

Node IdealProof::getSatFact() { return d_validFact; }
Node IdealProof::getUnsatFact() { return d_emptyVarFact; }

Node IdealProof::oneInUnsat(CoCoA::RingElem p,
                                  CDProof* globalTheoryProofs)
{
  d_emptyVarFact = nodeManager()->mkNode(Kind::NOT, d_validFact);
  Node membershipFact = d_membershipProofs->getMembershipFact(p);
  Assert(d_proof.getProof(membershipFact) != nullptr);
  d_proof.addStep(
		  d_emptyVarFact, ProofRule::FF_ONE_UNSAT, {membershipFact}, {}, true);
  std::shared_ptr<ProofNode> emptyVarProof = d_proof.getProof(d_emptyVarFact);
  globalTheoryProofs->addProof(
      emptyVarProof, CDPOverwrite::ASSUME_ONLY, true);  //
  return d_emptyVarFact;
}
void IdealProof::setFunctionPointers()
{
  d_membershipProofs->setFunctionPointers();
}

void IdealProof::enableProofHooks() { CoCoA::proofEnabled = true; }
void IdealProof::disableProofHooks() { CoCoA::proofEnabled = false; }

void IdealProof::registerBranchPolynomial(CoCoA::RingElem branchPoly)
{
  Trace("ff::proof") << "registering Proof for branchPoly: " << branchPoly
                     << std::endl;
  // Should check if the node representation of this polynomial is cached. 
  d_branchPoly = d_enc.encodeBack(branchPoly);
  d_branchPolyProof =
      d_membershipProofs->proofIdealMembership(branchPoly, d_cocoaIdeal);
  Trace("ff::proof") << d_branchPolyProof << std::endl;
}

void IdealProof::registerRoots(std::vector<CoCoA::RingElem> roots)
{
  std::vector<Node> rootsTerms;
  for (auto root : roots)
  {
    rootsTerms.push_back(d_enc.encodeBack(root));
  }
  d_branchPolyRoots = nodeManager()->mkNode(Kind::SEXPR, rootsTerms);
}
std::shared_ptr<IdealProof> IdealProof::registerConclusion(
    CoCoA::RingElem choicePoly, CoCoA::ideal newIdeal)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> polysRepr{
    d_enc.encodeBack(choicePoly)};
  std::vector<CoCoA::RingElem> newGens{choicePoly};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
  {
    newGens.push_back(poly);
    polysRepr.push_back(d_enc.encodeBack(poly));
  }
  Node idealRepr = nm->mkNode(Kind::FINITE_FIELD_IDEAL, polysRepr);
  Node nonNullVarPred = produceNonNullVarPred(nm, idealRepr);
  std::shared_ptr<IdealProof> childrenProof(
					    new IdealProof(d_env, d_id + 1, newGens, nonNullVarPred, d_enc, newIdeal));
  d_childrenProofs.push_back(childrenProof);
  return childrenProof;
}

Node IdealProof::produceConclusion(std::vector<Node>& childrenSatFact,
                                   bool rootBranching)
{
  Node conclusion = nodeManager()->mkOr(childrenSatFact);
  std::vector<Node> premises{d_validFact};
  std::vector<Node> arguments{};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal)){
    premises.push_back(d_membershipProofs->getMembershipFact(poly));
    Assert(d_proof.getProof(premises.back()) != nullptr) << premises.back();
  }
  if (!rootBranching)
  {
    d_proof.addStep(
		    conclusion, ProofRule::FF_EXHAUST_BRANCH, premises, arguments, true);
    return conclusion;
  }
  premises.push_back(d_branchPolyProof);
  Assert(d_proof.getProof(d_branchPolyProof) != nullptr);
  arguments = {d_branchPolyRoots};
  arguments.push_back(d_branchPoly);
  d_proof.addStep(conclusion, ProofRule::FF_ROOT_BRANCH, premises, arguments, true);
  return conclusion;
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
  Node conclusion = produceConclusion(childrenSatFact, rootBranching);
  Node falseNode;
  Assert(conclusion == nodeManager()->mkConst<bool>(false));
  // This usually happens when the Branching Polynomial have no roots. In this
  // case, the conclusion is the disjunction of empty nodes, i.e the node that
  // represents false.
  if (!d_childrenProofs.size()){
    falseNode = conclusion;
  }
  else
  {
    Unreachable();
    falseNode = nodeManager()->mkConst<bool>(false);
    Node trueNode = nodeManager()->mkConst<bool>(true);
    std::vector<Node> polarity;
    std::vector<Node> pivot;
    std::vector<Node> resolutionPremises{conclusion};
    for (Node unsatFacts : childrenUnsatFact)
    {
      d_proof.addProof(globalTheoryProofs->getProofFor(unsatFacts),
                       CDPOverwrite::ASSUME_ONLY,
                       true);
      resolutionPremises.push_back(unsatFacts);
    }
    for (size_t it = 0; it < childrenSatFact.size(); ++it)
      polarity.push_back(trueNode);
    for (Node satFact : childrenSatFact) pivot.push_back(satFact);
    d_proof.addStep(falseNode,
                    ProofRule::CHAIN_RESOLUTION,
                    resolutionPremises,
                    {nodeManager()->mkNode(Kind::SEXPR, polarity),
                     nodeManager()->mkNode(Kind::SEXPR, pivot)}, true);
  }
  d_emptyVarFact = nodeManager()->mkNode(Kind::NOT, d_validFact);
  Assert(d_proof.getProof(falseNode) != nullptr);
  d_proof.addStep(d_emptyVarFact, ProofRule::SCOPE, {falseNode}, {d_validFact}, true);
  std::stringstream s;
  // s << "size is: " << d_proof.getProof(d_emptyVarFact).get()->getChildren().size() << std::endl; 
  // d_proof.getProof(d_emptyVarFact).get()->printDebug(s, true);
  Assert(d_proof.getProof(d_emptyVarFact) != nullptr) << s.str();
  globalTheoryProofs->addProof(
      d_proof.getProof(d_emptyVarFact), CDPOverwrite::ASSUME_ONLY, true);
}

  Node IdealProof::produceNonNullVarPred(NodeManager *nm, Node ideal)
{
  TypeNode typeOfIdealB = ideal.getType();
  Node nonNullVarietyPred =
      nm->mkNode(Kind::FINITE_FIELD_NON_NULL_VAR, ideal);
  return nonNullVarietyPred;
}


}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
