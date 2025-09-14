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
 * Manager for proofs related to a given Ideal:
 *  Stores proof of memberships in d_membershipProofs
 *  Produces proofs using branching rules (translation of findZero rules)
 */

#include <CoCoA-0.99800/PolyRing.H>
#include <CoCoA-0.99800/SparsePolyOps-RingElem.H>
#include <CoCoA-0.99800/ring.H>
#include <CoCoA-0.99800/symbol.H>

#include <algorithm>
#include <iterator>
#include <unordered_set>

#include "theory/shared_terms_database.h"
#if CVC5_USE_COCOA

#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/TmpGPoly.H>

#include <sstream>

#include "proof/proof.h"
#include "proof/proof_node.h"
#include "smt/assertions.h"
#include "theory/ff/ideal_proofs.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

// Useful for debugging: Each different d_proof will have a name identified by
// its ID.
std::string buildName(size_t id)
{
  std::ostringstream name;
  name << "Ideal Proofs id: " << id;
  return name.str();
}
IdealProof::IdealProof(Env& env,
                       size_t id,
                       const std::vector<CoCoA::RingElem>& inputs,
                       CocoaEncoder& enc,
                       CoCoA::ideal cocoaIdeal)
    : EnvObj(env),
      d_cocoaIdeal(cocoaIdeal),
      d_enc(enc),
      d_branchPolyProof(),
      d_branchPolyRoots(),
      d_childrenProofs(),
      d_proof(env, nullptr, buildName(id)),
      d_id(id)
{
  std::vector<Node> polys;
  NodeManager* nm = nodeManager();
  for (auto gen : inputs)
  {
    Node polyVar = d_enc.decode(gen);
    polys.push_back(polyVar);
  }
  d_ideal = nm->mkNode(Kind::FINITE_FIELD_IDEAL, polys);
  d_membershipProofs = new GBProof(env, polys, d_ideal, enc, &d_proof);
}
Node IdealProof::getSatFact()
{
  return emptyVarPred(nodeManager(), d_ideal).negate();
}
Node IdealProof::getUnsatFact() { return d_emptyVarFact; }

Node IdealProof::oneInUnsat(CoCoA::RingElem p, CDProof* globalTheoryProofs)
{
  d_emptyVarFact = emptyVarPred(nodeManager(), d_ideal);
  // We collected all necessary proofs of membership and already have the
  // restriction to the unsat core, then we can register the proofs in d_proof.
  d_membershipProofs->registerProofs();
  // Get the proof of membership for one (p)
  Node membershipFact = d_membershipProofs->getMembershipFact(p);
  Assert(d_proof.getProof(membershipFact) != nullptr);
  d_proof.addStep(
      d_emptyVarFact, ProofRule::FF_ONE_UNSAT, {membershipFact}, {}, true);
  std::shared_ptr<ProofNode> emptyVarProof = d_proof.getProof(d_emptyVarFact);
  // Add this proof to the d_proof of the whole theory.
  globalTheoryProofs->addProof(emptyVarProof, CDPOverwrite::ASSUME_ONLY, true);
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
  d_branchPoly = d_enc.decode(branchPoly);
  d_branchPolyProof  =
      d_membershipProofs->proveIdealMembership(branchPoly, d_cocoaIdeal);
  d_branchVar = d_enc.decode(CoCoA::indet(
      d_cocoaIdeal->myRing(), CoCoA::UnivariateIndetIndex(branchPoly)));
  Trace("ff::proof") << d_branchPolyProof << std::endl;
}

void IdealProof::registerRoots(std::vector<CoCoA::RingElem> roots)
{
  std::vector<Node> rootsNode;
  for (auto root : roots)
  {
    rootsNode.push_back(d_enc.decode(root));
  }
  d_branchPolyRoots = nodeManager()->mkNode(Kind::SEXPR, rootsNode);
}
std::shared_ptr<IdealProof> IdealProof::registerBranch(
    CoCoA::RingElem choicePoly, CoCoA::ideal newIdeal)
{
  std::vector<CoCoA::RingElem> newGens{choicePoly};
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
  {
    newGens.push_back(poly);
  }
  std::shared_ptr<IdealProof> childrenProof(
      new IdealProof(d_env, d_id + 1, newGens, d_enc, newIdeal));
  d_childrenProofs.push_back(childrenProof);
  return childrenProof;
}

std::vector<Node> IdealProof::nonAssignedVars()
{
  std::vector<CoCoA::RingElem> allIndets =
      CoCoA::indets(d_cocoaIdeal->myRing());
  std::vector<Node> varsNodes;
  for (CoCoA::RingElem indet : allIndets)
    varsNodes.push_back(d_enc.decode(indet));
  std::unordered_set<Node> assignedVars;
  // Similar to assignedVars method in multi_roots
  for (auto gen : CoCoA::GBasis(d_cocoaIdeal))
  {
    if (CoCoA::deg(gen) == 1)
    {
      int varNumber = CoCoA::UnivariateIndetIndex(gen);
      if (varNumber >= 0)
        assignedVars.insert(
            d_enc.decode(CoCoA::indet(d_cocoaIdeal->myRing(), varNumber)));
    }
  }
  std::vector<Node> ret;
  // filter for only non-assigned vars.
  std::copy_if(varsNodes.begin(),
               varsNodes.end(),
               std::back_inserter(ret),
               [&assignedVars](auto x) { return assignedVars.count(x) == 0; });
  return ret;
}
Node IdealProof::proveBrancher(std::vector<Node>& childrenSatFact,
                               bool rootBranching)
{
  // Both proofs share a common structure. We first collect this structure.
  Node conclusion = nodeManager()->mkOr(childrenSatFact);
  std::vector<Node> premises{getSatFact()};
  Assert(CoCoA::HasGBasis(d_cocoaIdeal));
  std::vector<Node> arguments = {
      nodeManager()->mkNode(Kind::SEXPR, nonAssignedVars())};
  d_membershipProofs->registerProofs();
  for (auto poly : CoCoA::GBasis(d_cocoaIdeal))
  {
    premises.push_back(d_membershipProofs->getMembershipFact(poly));
  }
  // Here comes the main difference: Exhaust_branch do not contain facts about
  // a branch polynomial.
  if (!rootBranching)
  {
    d_proof.addStep(
        conclusion, ProofRule::FF_EXHAUST_BRANCH, premises, arguments);
    return conclusion;
  }
  // Branch polynomial must be in the ideal. We also need to know its roots to
  // compute the branches.
  premises.push_back(d_branchPolyProof);
  Assert(d_proof.getProof(d_branchPolyProof) != nullptr);
  arguments.push_back(d_branchVar);
  arguments.push_back(d_branchPolyRoots);
  arguments.push_back(d_branchPoly);
  d_proof.addStep(conclusion, ProofRule::FF_ROOT_BRANCH, premises, arguments);
  return conclusion;
}

void IdealProof::finishProof(bool rootBranching, CDProof* globalTheoryProofs)
{
  // Register proofs of membership in d_proof
  d_membershipProofs->registerProofs();
  std::vector<Node> childrenSatFact;
  std::vector<Node> childrenUnsatFact;
  for (const auto& branchProofs : d_childrenProofs)
  {
    childrenSatFact.push_back(branchProofs->getSatFact());
    childrenUnsatFact.push_back(branchProofs->getUnsatFact());
  }
  Node conclusion = proveBrancher(childrenSatFact, rootBranching);
  Node falseNode;
  Assert(conclusion == nodeManager()->mkConst<bool>(false));
  // This happens when the Branching Polynomial have no roots. In this
  // case, the conclusion is the disjunction of empty nodes, i.e false.
  // Thus, we already have a proof for false.
  if (!d_childrenProofs.size())
  {
    falseNode = conclusion;
  }
  else
  {
    // Produce a proof for false by CHAIN_RESOLUTION on the conclusion of a
    // branching step with the refutation of each literal.
    falseNode = nodeManager()->mkConst<bool>(false);
    Node trueNode = nodeManager()->mkConst<bool>(true);
    std::vector<Node> polarity;
    std::vector<Node> pivot;
    std::vector<Node> resolutionPremises{conclusion};
    for (const auto& unsatFacts : childrenUnsatFact)
    {
      d_proof.addProof(globalTheoryProofs->getProofFor(unsatFacts));
      resolutionPremises.push_back(unsatFacts);
    }
    for (size_t it = 0; it < childrenSatFact.size(); ++it)
      polarity.push_back(trueNode);
    for (const auto& satFact : childrenSatFact) pivot.push_back(satFact);
    d_proof.addStep(falseNode,
                    ProofRule::CHAIN_RESOLUTION,
                    resolutionPremises,
                    {nodeManager()->mkNode(Kind::SEXPR, polarity),
                     nodeManager()->mkNode(Kind::SEXPR, pivot)},
                    true);
  }
  // This variety is empty and may be used to either conclude that the ideal
  // that branched into this have an empty variety or conclude unsat
  d_emptyVarFact = emptyVarPred(nodeManager(), d_ideal);
  d_proof.addStep(
      d_emptyVarFact, ProofRule::SCOPE, {falseNode}, {getSatFact()});
  globalTheoryProofs->addProof(d_proof.getProofFor(d_emptyVarFact));
}

void IdealProof::updateIdeal(std::vector<Node>& polys)
{
  Node ideal = nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, polys);
  d_ideal = ideal;
  d_membershipProofs->updateIdeal(ideal);
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
