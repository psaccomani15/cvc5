#ifdef CVC5_USE_COCOA

#include "theory/ff/membership_proof_manager.h"

#include <CoCoA/DistrMPolyInlPP.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
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
                                               CoCoA::ring ring,
                                               CocoaEncoder& enc,
                                               CDProof* proof)
    : EnvObj(env),
      d_multiplierSeq(),
      d_ideal(ideal),
      d_cocoaRing(ring),
      d_factToProof(),
      d_enc(enc),
      d_proof(proof)
{
  Trace("ff::proof") << "Inputs:" << std::endl;
  for (auto polyRepr : polys)
  {
    Trace("ff::proof") << "\t" << polyRepr << std::endl;
    storeProof(polyRepr, ProofRule::FF_IDEAL_GENERATOR, {}, {polyRepr});
  }
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
      std::function([=](CoCoA::ConstRefRingElem p) { t->membershipStep(p); });
  d_membershipEnd = std::function([=]() { t->membershipEnd(); });
  d_storeMultiplier = std::function(
      [=](CoCoA::ConstRefRingElem mul) { t->storeMultiplier(mul); });
  d_storeMultiplierRaw = std::function(
      [=](CoCoA::DistrMPolyInlPP& mul) { t->storeMultiplierRaw(mul); });
  d_storeMultiplierRawFp = std::function(
      [=](CoCoA::DistrMPolyInlFpPP& mul) { t->storeMultiplierRaw(mul); });

  CoCoA::sPolyProof = d_sPoly;
  CoCoA::reductionStartProof = d_reductionStart;
  CoCoA::reductionStepProof = d_reductionStep;
  CoCoA::reductionEndProof = d_reductionEnd;
  CoCoA::membershipStart = d_membershipStart;
  CoCoA::membershipStep = d_membershipStep;
  CoCoA::membershipEnd = d_membershipEnd;
  CoCoA::monicProof = d_monicProof;
  CoCoA::storeMultiplier = d_storeMultiplier;
  CoCoA::storeMultiplierRaw = d_storeMultiplierRaw;
  CoCoA::storeMultiplierRawFp = d_storeMultiplierRawFp;
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
  AlwaysAssert(hasElem);
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
      for (size_t childIdx = 0; childIdx < children.size(); ++childIdx)
        children[childIdx] = produceMembershipNode(children[childIdx]);
    }
    for (const auto& arg : args)
      Trace("ff::proof") << "arg is: " << arg << std::endl;
    d_proof->addStep(conclusion, id, children, args);
  }
}

void MembershipProofManager::storeMultiplier(CoCoA::ConstRefRingElem p)
{
  Trace("ff::proof") << "Must store reduction multiplier: " << d_enc.decode(p)
                     << std::endl;
  d_multiplierSeq.push_back(p);
}
template <typename T>
void MembershipProofManager::storeMultiplierRaw(T& p)
{
  Trace("ff::mul") << "storeRaw" << std::endl;
  CoCoA::RingElem poly = CoCoA::zero(d_cocoaRing);
  typename T::iter iter(p);
  for (; !CoCoA::IsEnded(iter); ++iter)
  {
    Trace("ff::mul") << "should add" << CoCoA::monomial(d_cocoaRing, CoCoA::coeff(iter), CoCoA::PP(iter)) << std::endl;
    poly += CoCoA::monomial(d_cocoaRing, CoCoA::coeff(iter), CoCoA::PP(iter));
  }
  storeMultiplier(poly);
}
template void MembershipProofManager::storeMultiplierRaw<
    CoCoA::DistrMPolyInlPP>(CoCoA::DistrMPolyInlPP&);
template void MembershipProofManager::storeMultiplierRaw<
    CoCoA::DistrMPolyInlFpPP>(CoCoA::DistrMPolyInlFpPP&);
void MembershipProofManager::sPoly(CoCoA::ConstRefRingElem p,
                                   CoCoA::ConstRefRingElem q,
                                   CoCoA::ConstRefRingElem s)
{
 Node sNode = d_enc.decode(s);
  Trace("ff::proof") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_factToProof.count(sNode) == 0)
  {
    Trace("ff::proof") << " keep" << std::endl;
    Assert(d_multiplierSeq.size() == 2) << d_multiplierSeq.size();
    Node pNode = d_enc.decode(p);
    Node mpNode = d_enc.decode(d_multiplierSeq[0]);
    Node mqNode = d_enc.decode(d_multiplierSeq[1]);
    Node qNode = d_enc.decode(q); 
    Node rs = nodeManager()->mkNode(Kind::SEXPR, {pNode, qNode});
    Node ms = nodeManager()->mkNode(Kind::SEXPR, {mpNode, mqNode});
    storeProof(sNode, ProofRule::MACRO_FF_POLY_COMBINATION, {pNode, qNode}, {rs, ms, sNode});}
  else
  {
    Trace("ff::proof") << " drop" << std::endl;
  }
    d_multiplierSeq.clear();
}

void MembershipProofManager::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof start: " << d_enc.decode(p)
                     << std::endl;
  d_reductionSeq.push_back(p);
}

// q is the reducer, we then assert that q already has a membership proof.
void MembershipProofManager::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::proof") << "GBreduction proof step: " << d_enc.decode(q)
                     << std::endl;
  d_reductionSeq.push_back(q);
}

void MembershipProofManager::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Node rTerm = d_enc.decode(r);
  std::vector<Node> args{rTerm};
  Trace("ff::proof") << "reduction proof end: " << std::endl;
  if (d_factToProof.count(rTerm) == 0)
  {
    std::unordered_set<Node> uniquePolys;
    Trace("ff::proof") << " keep" << std::endl;
    std::vector<Node> reductors{};
    for (auto& reductor : d_reductionSeq)
    {
      Node polyNode = d_enc.decode(reductor);
      reductors.push_back(polyNode);
      uniquePolys.insert(polyNode);
    }
    // Assert(d_multiplierSeq.size() == d_reductionSeq.size() - 1)
     //  << d_reductionSeq.size();
    std::vector<Node> multipliers{d_enc.one()};
    for (auto& mul : d_multiplierSeq) multipliers.push_back(d_enc.decode(mul));
    Node rs = nodeManager()->mkNode(Kind::SEXPR, reductors);
    Node ms = nodeManager()->mkNode(Kind::SEXPR, multipliers);
    args.push_back(nodeManager()->mkNode(Kind::SEXPR, multipliers));
    storeProof(rTerm,
               ProofRule::MACRO_FF_POLY_COMBINATION,
               std::vector(uniquePolys.begin(), uniquePolys.end()),
               {rs, ms, rTerm});
  }
  d_multiplierSeq.clear();
  d_reductionSeq.clear();
}

void MembershipProofManager::monicProof(CoCoA::ConstRefRingElem poly,
                                        CoCoA::ConstRefRingElem monic)
{
  Node polyTerm = d_enc.decode(poly);
  Node monicTerm = d_enc.decode(monic);
  CoCoA::RingElem lcInv = CoCoA::one(d_cocoaRing) / CoCoA::LC(poly);
  Node rs = nodeManager()->mkNode(Kind::SEXPR, polyTerm);
  Node ms = nodeManager()->mkNode(Kind::SEXPR, d_enc.decode(lcInv));
  Trace("ff::monic") << "Orig: " << poly << " New: " << monic;
  Assert(d_factToProof.count(polyTerm));
  storeProof(monicTerm, ProofRule::MACRO_FF_POLY_COMBINATION, {polyTerm}, {rs, ms, monicTerm});
}
void MembershipProofManager::membershipStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_membershipSeq.empty());
  d_reducingPoly = p;
  CoCoA::membershipTest = true;
  Trace("ff::proof") << "Starting membership proof with: " << p << std::endl;
}

void MembershipProofManager::membershipStep(CoCoA::RingElem red)
{
  Trace("ff::proof") << "Membership step done" << std::endl;
  d_membershipSeq.push_back(red);
}

void MembershipProofManager::membershipEnd()
{
  CoCoA::membershipTest = false;
  std::unordered_set<Node> uniquePolys;
  std::vector<Node> reductors;
  for (auto& reductor : d_membershipSeq)
  {
    Node polyNode = d_enc.decode(reductor);
    reductors.push_back(polyNode);
    uniquePolys.insert(polyNode);
  }
  Assert(!d_membershipSeq.empty());
  std::vector<Node> multipliers{};
  for (auto& mul : d_multiplierSeq) multipliers.push_back(d_enc.decode(mul));
  Node rs = nodeManager()->mkNode(Kind::SEXPR, reductors);
  Node ms = nodeManager()->mkNode(Kind::SEXPR, multipliers);
  Node reducingPolyNode = d_enc.decode(d_reducingPoly);
  std::vector<Node> children(uniquePolys.begin(), uniquePolys.end());
  storeProof(reducingPolyNode, ProofRule::MACRO_FF_POLY_COMBINATION, children, {rs, ms, reducingPolyNode});
  d_multiplierSeq.clear();
  d_membershipSeq.clear();
  Trace("ff::proof") << "finish membership Proof for " << d_reducingPoly
                     << std::endl; 
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
