#include "theory/ff/membership_proofs.h"

#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/TmpGPoly.H>

#include <sstream>

#include "proof/proof.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
GBProof::GBProof(Env& env,
                 const std::vector<CoCoA::RingElem> polys,
                 Node ideal, CocoaEncoder &enc, 
                 CDProof* proof)
  : EnvObj(env), d_ideal(ideal), d_enc(enc), d_proof(proof)
{
  NodeManager* nm = nodeManager();

  for (auto gen : polys)
  {
    Node polyRepr = d_enc.encodeBack(gen);
    // TODO: Add a predicate specific to ideal membership. 
    Node membershipRepr = nm->mkNode(Kind::FINITE_FIELD_IDEAL_MEMBERSHIP, polyRepr, d_ideal);
    std::vector<Node> argsIdeal{polyRepr, d_ideal};
    Trace("ff::proof") << "..will create pf step " << ProofRule::FF_G << ": "
                       << membershipRepr << " " << argsIdeal << "\n";
    d_proof->addStep(membershipRepr, ProofRule::FF_G, {}, argsIdeal, true);
    d_polyToMembership.emplace(polyRepr, membershipRepr);
  }
  Trace( "ff::proof") << "..will create pf step " << ProofRule::FF_Z << " : "
                     << "0 " << d_ideal << std::endl;
  Node zeroConclusion = produceMembershipNode(d_enc.zero(), nm);
  d_proof->addStep(zeroConclusion, ProofRule::FF_Z, {}, {d_ideal}, true);
};

void GBProof::setFunctionPointers()
{ 
  GBProof* t = this;
  d_sPoly =
      std::function([=](CoCoA::ConstRefRingElem p,
                        CoCoA::ConstRefRingElem q,
                        CoCoA::ConstRefRingElem s) { t->sPoly(p, q, s); });
  d_reductionStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStart(p); });
  d_reductionStep =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStep(p); });
  d_reductionEnd =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionEnd(p); });
  d_monicProof = std::function(
      [=](CoCoA::ConstRefRingElem poly, CoCoA::ConstRefRingElem monic) {
        t->monicProof(poly, monic);
      });
  d_membershipStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->membershipStart(p); });
  d_membershipStep =
      std::function([=](CoCoA::RingElem p) { t->membershipStep(p); });
  d_membershipEnd = std::function([=]() { t->membershipEnd(); });
  CoCoA::sPolyProof = d_sPoly;
  CoCoA::reductionStartProof = d_reductionStart;
  CoCoA::reductionStepProof = d_reductionStep;
  CoCoA::reductionEndProof = d_reductionEnd;
  CoCoA::membershipStart = d_membershipStart;
  CoCoA::membershipStep = d_membershipStep;
  CoCoA::membershipEnd = d_membershipEnd;
  CoCoA::monicProof = d_monicProof;
}
Node GBProof::produceMembershipNode(Node poly, NodeManager* nm)
{
  return nm->mkNode(Kind::FINITE_FIELD_IDEAL_MEMBERSHIP, poly, d_ideal);
}

  
// Returns a stored proof por membership of poly
Node GBProof::getMembershipFact(CoCoA::ConstRefRingElem poly)
{
  Node polyRepr = d_enc.encodeBack(poly);
  Assert(d_polyToMembership.count(polyRepr));
  return d_polyToMembership[polyRepr];
}

// Register or returns a membership proof for a given polynomial
Node GBProof::proofIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal)
{
  // Unreachable();
  Node polyRepr = d_enc.encodeBack(poly);
  // Trace("ff::proof") << "Ideal has element " << poly << " with proof fact:"
  // << d_polyToMembership[polyRepr] << std::endl;
  if (d_polyToMembership.count(polyRepr)) return getMembershipFact(poly);
  Assert(CoCoA::HasGBasis(ideal));
  bool hasElem = CoCoA::IsElem(poly, ideal);
  Assert(hasElem);
  Trace("ff::proof") << "Ideal has element " << poly
                     << "with proof fact:" << d_polyToMembership[polyRepr]
                     << std::endl;
  return d_polyToMembership[polyRepr];
}

void GBProof::sPoly(CoCoA::ConstRefRingElem p,
                    CoCoA::ConstRefRingElem q,
                    CoCoA::ConstRefRingElem s)
{
  Node pTerm = d_enc.encodeBack(p);
  Node qTerm = d_enc.encodeBack(q);
  Node sTerm = d_enc.encodeBack(s);
  Trace("ff::proof") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_polyToMembership.count(sTerm) == 0)
  {
    NodeManager* nm = nodeManager();
    Trace("ff::proof") << " keep" << std::endl;
    Node conclusion = produceMembershipNode(sTerm, nm);
    d_polyToMembership.emplace(sTerm, conclusion);
    Node pMNode = d_polyToMembership[pTerm];
    Node qMNode = d_polyToMembership[qTerm];
    std::vector<Node> premises{pMNode, qMNode};
    Trace("ff::proof") << "..will create pf step " << ProofRule::FF_S << ": "
                       << premises << " ---> " << conclusion << "\n";
    d_proof->addStep(conclusion, ProofRule::FF_S, premises, {}, true);
  }
  else
  {
    Trace("ff::proof") << " drop" << std::endl;
  }
}

void GBProof::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof start: " << p << std::endl;
  d_reductionSeq.push_back(d_enc.encodeBack(p));
}

// q is the reducer, we then assert that q already has a membership proof.
void GBProof::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof step: " << q << std::endl;
  d_reductionSeq.push_back(d_enc.encodeBack(q));
}

void GBProof::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  NodeManager* nm = nodeManager();
  Node rTerm = d_enc.encodeBack(r);
  Trace("ff::proof") << "reduction proof end: " << r << " "
                     << d_polyToMembership.count(rTerm) << std::endl;
  if (d_polyToMembership.count(rTerm) == 0)
  {
    std::vector<Node> premises{};
    std::vector<Node> reductorsSeq{};
    std::unordered_set<Node> uniquePolys;
    Trace("ff::proof") << " keep" << std::endl;
    Node conclusion = produceMembershipNode(rTerm, nm);
    d_polyToMembership.emplace(rTerm, conclusion);
    // TODO: Use indices of the premises list for the arguments. 
    for (Node reductorTerm : d_reductionSeq)
    {
      uniquePolys.insert(reductorTerm);
      reductorsSeq.push_back(reductorTerm);
    }
    for (Node poly : uniquePolys)
    {
      premises.push_back(d_polyToMembership[poly]);
    }
    d_proof->addStep(
        conclusion, ProofRule::FF_R_DOWN, premises, reductorsSeq, true);
    Trace("ff::proof") << ".. will create pf step: " << ProofRule::FF_R_DOWN
                       << premises << " ---> " << conclusion << std::endl;
  }
  else
  {
    if (TraceIsOn("ff::proof"))
    {
      Trace("ff::proof") << " drop" << std::endl;
    }
  }
  d_reductionSeq.clear();
}

void GBProof::monicProof(CoCoA::ConstRefRingElem poly,
                         CoCoA::ConstRefRingElem monic)
{
  NodeManager* nm = nodeManager();
  Node polyTerm = d_enc.encodeBack(poly);
  Node monicTerm = d_enc.encodeBack(monic);
  Assert(d_polyToMembership.count(polyTerm));
  std::vector<Node> premises{d_polyToMembership[polyTerm]};
  Node conclusion = produceMembershipNode(monicTerm, nm);
  d_polyToMembership.emplace(monicTerm, conclusion);
  d_proof->addStep(conclusion, ProofRule::FF_MONIC, premises, {}, true);
}
void GBProof::membershipStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_membershipSeq.empty());
  d_reducingPoly = d_enc.encodeBack(p);
  Trace("ff::proof") << "Starting membership proof with: " << p << std::endl;
}

void GBProof::membershipStep(CoCoA::RingElem red)
{
  d_membershipSeq.push_back(d_enc.encodeBack(red));
}

  //TODO:: Refactor this section to reuse code from reduction. 
void GBProof::membershipEnd()
{
  NodeManager* nm = nodeManager();
  Node conclusion = produceMembershipNode(d_reducingPoly, nm);
  std::vector<Node> reductorsSeq;
  std::unordered_set<Node> uniquePolys;
  for (Node p : d_membershipSeq)
  {
    reductorsSeq.push_back(p);
    uniquePolys.insert(p);
  }
  std::vector<Node> premises{};
  for (Node p : uniquePolys)
  {
    Assert(d_polyToMembership.count(p));
    premises.push_back(d_polyToMembership[p]);
  }
  premises.push_back(d_polyToMembership[d_enc.zero()]);
  Trace("ff::proof") << "finish membership Proof for " << d_reducingPoly
                     << std::endl;
  d_polyToMembership.emplace(d_reducingPoly, conclusion);
  d_proof->addStep(
      conclusion, ProofRule::FF_R_UP, premises, reductorsSeq, true);
  d_membershipSeq.clear();
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

//#endif /* CVC5_USE_COCOA */
