#include "theory/ff/membership_proofs.h"

#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/TmpGPoly.H>

#include <algorithm>
#include <sstream>

#include "proof/proof.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "theory/shared_terms_database.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
GBProof::GBProof(Env& env,
                 const std::vector<Node> polys,
                 Node ideal,
                 CocoaEncoder& enc,
                 CDProof* proof)
    : EnvObj(env), d_ideal(ideal), d_factToProof(), d_enc(enc), d_proof(proof)
{
  for (auto polyRepr : polys)
  {
    Node membershipRepr = produceMembershipNode(polyRepr);
    d_polyToMembership.emplace(polyRepr, membershipRepr);
    storeProof(polyRepr, ProofRule::FF_G, {}, {polyRepr});
  }
  Trace("ff::proof") << "..will create pf step " << ProofRule::FF_Z << " : "
                     << "0 " << d_ideal << std::endl;
  Node zeroConclusion = produceMembershipNode(d_enc.zero());
  d_polyToMembership.emplace(d_enc.zero(), zeroConclusion);
  storeProof(d_enc.zero(), ProofRule::FF_Z, {}, {});
};

void GBProof::updateIdeal(Node ideal) { d_ideal = ideal; }
Node GBProof::produceMembershipNode(Node poly)
{
  return nodeManager()->mkNode(Kind::SET_MEMBER, poly, d_ideal);
}
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
void GBProof::storeProof(Node poly,
                         ProofRule id,
                         std::vector<Node> children,
                         std::vector<Node> args)
{
  d_factToProof.emplace(poly, ProofInfo(id, children, args));
}
// Returns a stored proof por membership of poly
Node GBProof::getMembershipFact(CoCoA::ConstRefRingElem poly)
{
  Node polyRepr = d_enc.encodeBack(poly);
  return produceMembershipNode(polyRepr);
}

// Register or returns a membership proof for a given polynomial
Node GBProof::proofIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal)
{
  // Unreachable();
  Node polyRepr = d_enc.encodeBack(poly);
  if (d_polyToMembership.count(polyRepr)) return getMembershipFact(poly);
  Assert(CoCoA::HasGBasis(ideal));
  bool hasElem = CoCoA::IsElem(poly, ideal);
  Assert(hasElem);
  Trace("ff::proof") << "Ideal has element " << poly
                     << "with proof fact:" << d_polyToMembership[polyRepr]
                     << std::endl;
  return d_polyToMembership[polyRepr];
}
void GBProof::registerProofs()
{
  for (auto& it : d_factToProof)
  {
    Node conclusion = produceMembershipNode(it.first);
    ProofRule id = it.second.d_id;
    std::vector<Node> children = it.second.d_children;
    std::vector<Node> args = it.second.d_args;
    if (id == ProofRule::FF_Z || id == ProofRule::FF_G)
      args.push_back(d_ideal);
    else
    {
      std::transform(
          children.begin(), children.end(), children.begin(), [this](Node n) {
            return produceMembershipNode(n);
          });
    }
    d_proof->addStep(conclusion, id, children, args);
  }
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
    Trace("ff::proof") << " keep" << std::endl;
    Node conclusion = produceMembershipNode(sTerm);
    d_polyToMembership.emplace(sTerm, conclusion);
    std::vector<Node> parents{pTerm, qTerm};
    storeProof(sTerm, ProofRule::FF_S, parents, {});
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
  Node rTerm = d_enc.encodeBack(r);
  Trace("ff::proof") << "reduction proof end: " << r << " "
                     << d_polyToMembership.count(rTerm) << std::endl;
  if (d_polyToMembership.count(rTerm) == 0)
  {
    std::vector<Node> premises{};
    std::vector<Node> reductorsSeq{};
    std::unordered_set<Node> uniquePolys;
    Trace("ff::proof") << " keep" << std::endl;
    Node conclusion = produceMembershipNode(rTerm);
    d_polyToMembership.emplace(rTerm, conclusion);
    // TODO: Use indices of the premises list as argument.
    for (Node reductorTerm : d_reductionSeq)
    {
      uniquePolys.insert(reductorTerm);
      reductorsSeq.push_back(reductorTerm);
    }
    for (Node poly : uniquePolys)
    {
      premises.push_back(d_polyToMembership[poly]);
    }
    storeProof(rTerm,
               ProofRule::FF_R_DOWN,
               std::vector(uniquePolys.begin(), uniquePolys.end()),
               reductorsSeq);
  }
  d_reductionSeq.clear();
}

void GBProof::monicProof(CoCoA::ConstRefRingElem poly,
                         CoCoA::ConstRefRingElem monic)
{
  Node polyTerm = d_enc.encodeBack(poly);
  Node monicTerm = d_enc.encodeBack(monic);
  Assert(d_polyToMembership.count(polyTerm));
  std::vector<Node> premises{d_polyToMembership[polyTerm]};
  Node conclusion = produceMembershipNode(monicTerm);
  d_polyToMembership.emplace(monicTerm, conclusion);
  storeProof(monicTerm, ProofRule::FF_MONIC, {polyTerm}, {});
  // d_proof->addStep(conclusion, ProofRule::FF_MONIC, premises, {}, true);
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

// TODO:: Refactor this section to reuse code from reduction.
void GBProof::membershipEnd()
{
  Node conclusion = produceMembershipNode(d_reducingPoly);
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

// #endif /* CVC5_USE_COCOA */
