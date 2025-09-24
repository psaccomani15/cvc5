#include "theory/ff/membership_proof_manager.h"

#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/TmpGPoly.H>
#include <CoCoA/library.H>
#include <CoCoA/ring.H>

#include <algorithm>

#include "options/ff_options.h"
#include "proof/proof.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "theory/shared_terms_database.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
MembershipProofManager::MembershipProofManager(Env& env,
                                               const std::vector<Node> polys,
                                               Node ideal,
                                               CocoaEncoder& enc,
                                               CDProof* proof)
    : EnvObj(env), d_ideal(ideal), d_factToProof(), d_enc(enc), d_proof(proof)
{
  for (auto polyRepr : polys)
  {
    storeProof(polyRepr, ProofRule::FF_IDEAL_GENERATOR, {}, {polyRepr});
  }
  storeProof(d_enc.zero(), ProofRule::FF_IDEAL_ZERO, {}, {d_enc.zero()});
};

void MembershipProofManager::updateIdeal(Node ideal) { d_ideal = ideal; }
Node MembershipProofManager::produceMembershipNode(Node poly)
{
  return nodeManager()->mkNode(Kind::SET_MEMBER, poly, d_ideal);
}
void MembershipProofManager::setFunctionPointers()
{
  MembershipProofManager* t = this;
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
void MembershipProofManager::storeProof(Node poly,
                                        ProofRule id,
                                        std::vector<Node> children,
                                        std::vector<Node> args)
{
  d_factToProof.emplace(poly, ProofInfo(id, children, args));
}
// Returns a stored proof por membership of poly
Node MembershipProofManager::getMembershipFact(CoCoA::ConstRefRingElem poly)
{
  Node polyRepr = d_enc.decode(poly);
  return produceMembershipNode(polyRepr);
}

// Register or returns a membership proof for a given polynomial
Node MembershipProofManager::proveIdealMembership(CoCoA::RingElem poly,
                                                  CoCoA::ideal ideal)
{
  Node polyRepr = d_enc.decode(poly);
  Node membershipRepr = produceMembershipNode(polyRepr);
  if (d_factToProof.count(polyRepr)) return membershipRepr;
  Assert(CoCoA::HasGBasis(ideal));
  bool hasElem = CoCoA::IsElem(poly, ideal);
  Assert(hasElem);
  Trace("ff::proof") << "Ideal has element " << poly
                     << "with membership representation" << membershipRepr
                     << std::endl;
  return membershipRepr;
}

void MembershipProofManager::registerProofs()
{
  for (auto& it : d_factToProof)
  {
    Node conclusion = produceMembershipNode(it.first);
    ProofRule id = it.second.d_id;
    std::vector<Node> children = it.second.d_children;
    std::vector<Node> args = it.second.d_args;
    if (id == ProofRule::FF_IDEAL_ZERO || id == ProofRule::FF_IDEAL_GENERATOR)
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
void MembershipProofManager::sPoly(CoCoA::ConstRefRingElem p,
                                   CoCoA::ConstRefRingElem q,
                                   CoCoA::ConstRefRingElem s)
{
  Node pNode = d_enc.decode(p);
  Node qNode = d_enc.decode(q);
  Node sNode = d_enc.decode(s);
  Trace("ff::proof") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_factToProof.count(sNode) == 0)
  {
    Trace("ff::proof") << " keep" << std::endl;
    std::vector<Node> parents{pNode, qNode};
    std::vector<Node> args{sNode};
    if (options().ff.ffProofOptionalArgs)
    {
      Assert(!CoCoA::owner(p)->IamFiniteField() && !CoCoA::owner(q)->IamFiniteField());
      const CoCoA::SparsePolyRing& polyRing = CoCoA::owner(p);
      auto mulP(CoCoA::monomial(polyRing, CoCoA::colon(CoCoA::LPP(p), CoCoA::LPP(p))));
      args.push_back(d_enc.decode(mulP));
      CoCoA::RingElem newP(polyRing,  mulP * p);
      CoCoA::RingElem mulQ(polyRing);
      Assert(!CoCoA::IsZero(newP) && !CoCoA::IsZero(q));
      polyRing->myDivLM(CoCoA::raw(mulQ), CoCoA::raw(newP), CoCoA::raw(q));
      polyRing->myNegate(CoCoA::raw(mulQ), CoCoA::raw(mulQ));
      args.push_back(d_enc.decode(mulQ));
      polyRing->myAddMulLM(CoCoA::raw(newP), CoCoA::raw(mulQ), CoCoA::raw(q));
      Assert(newP == s);
    }
    storeProof(sNode, ProofRule::FF_IDEAL_SPOLY, parents, {sNode});
  }
  else
  {
    Trace("ff::proof") << " drop" << std::endl;
  }
}

void MembershipProofManager::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof start: " << p << std::endl;
  d_reductionSeq.push_back(p);
}

// q is the reducer, we then assert that q already has a membership proof.
void MembershipProofManager::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof step: " << q << std::endl;
  d_reductionSeq.push_back(q);
}

void MembershipProofManager::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Node rTerm = d_enc.decode(r);
  std::vector<Node> args{rTerm};
  std::vector<Node> optionalArgs;
  Trace("ff::proof") << "reduction proof end: " << std::endl;
  auto currPoly = d_reductionSeq[0];
  if (d_factToProof.count(rTerm) == 0)
  {
    std::unordered_set<Node> uniquePolys;
    Trace("ff::proof") << " keep" << std::endl;
    // TODO: Use indices of the premises list as argument.
    for (auto& reductor : d_reductionSeq)
    {
      Node polyNode = d_enc.decode(reductor);
      args.push_back(polyNode);
      uniquePolys.insert(polyNode);
      if (options().ff.ffProofOptionalArgs)
      {
        const CoCoA::SparsePolyRing& polyRing = CoCoA::owner(r);
        CoCoA::RingElem mul(polyRing);
        polyRing->myDivLM(
            CoCoA::raw(mul), CoCoA::raw(currPoly), CoCoA::raw(reductor));
        polyRing->myNegate(CoCoA::raw(mul), CoCoA::raw(mul));
        polyRing->myAddMulLM(
            CoCoA::raw(currPoly), CoCoA::raw(mul), CoCoA::raw(reductor));
        optionalArgs.push_back(d_enc.decode(mul));
      }
    }
    if (options().ff.ffProofOptionalArgs)
    {
      Assert(currPoly == r);
      args.insert(args.end(), optionalArgs.begin(), optionalArgs.end());
    }
    storeProof(rTerm,
               ProofRule::FF_IDEAL_REDUCE,
               std::vector(uniquePolys.begin(), uniquePolys.end()),
               args);
  }
  d_reductionSeq.clear();
}

void MembershipProofManager::monicProof(CoCoA::ConstRefRingElem poly,
                                        CoCoA::ConstRefRingElem monic)
{
  Node polyTerm = d_enc.decode(poly);
  Node monicTerm = d_enc.decode(monic);
  std::vector<Node> args = {monicTerm};
  Assert(d_factToProof.count(polyTerm));
  storeProof(monicTerm, ProofRule::FF_IDEAL_MONIC, {polyTerm}, {monicTerm});
}
void MembershipProofManager::membershipStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_membershipSeq.empty());
  d_reducingPoly = p;
  Trace("ff::proof") << "Starting membership proof with: " << p << std::endl;
}

void MembershipProofManager::membershipStep(CoCoA::RingElem red)
{
  Trace("ff::proof") << "Membership step done" << std::endl;
  d_membershipSeq.push_back(red);
}

// TODO:: Refactor this section to reuse code from reduction.
void MembershipProofManager::membershipEnd()
{
  Node reducingPolyNode = d_enc.decode(d_reducingPoly);
  auto currPoly = d_reducingPoly;
  std::vector<Node> args{reducingPolyNode};
  std::unordered_set<Node> uniquePolys;
  std::vector<Node> optionalArgs;
  for (auto& reductor : d_membershipSeq)
  {
    Node polyNode = d_enc.decode(reductor);
    args.push_back(polyNode);
    uniquePolys.insert(polyNode);
    if (options().ff.ffProofOptionalArgs)
    {
      CoCoA::SparsePolyRing polyRing = CoCoA::owner(d_reducingPoly);
      CoCoA::RingElem mul;
      polyRing->myDivLM(
          CoCoA::raw(mul), CoCoA::raw(currPoly), CoCoA::raw(reductor));
      polyRing->myNegate(CoCoA::raw(mul), CoCoA::raw(mul));
      polyRing->myAddMulLM(
          CoCoA::raw(currPoly), CoCoA::raw(mul), CoCoA::raw(reductor));
      optionalArgs.push_back(d_enc.decode(mul));
    }
  }
  if (options().ff.ffProofOptionalArgs)
  {
    Assert(CoCoA::IsZero(currPoly));
    args.insert(args.begin(), optionalArgs.begin(), optionalArgs.end());
  }
  std::vector<Node> children(uniquePolys.begin(), uniquePolys.end());
  children.push_back(d_enc.zero());
  Trace("ff::proof") << "finish membership Proof for " << d_reducingPoly
                     << std::endl;
  storeProof(reducingPolyNode, ProofRule::FF_IDEAL_REDUCE_ZERO, children, args);
  d_membershipSeq.clear();
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

// #endif /* CVC5_USE_COCOA */
