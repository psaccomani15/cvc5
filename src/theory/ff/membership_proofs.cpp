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

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

// TODO string to node, so that same string yields the same node

GBProof::GBProof(Env& env,
                 const std::vector<CoCoA::RingElem> polys,
                 Node ideal,
                 CDProof* proof)
    : EnvObj(env), d_ideal(ideal), d_proof(proof)

{
  NodeManager* nm = nodeManager();

  for (auto cPoly : polys)
  {
    std::string poly = ostring(cPoly);
    Node polyRepr = nm->mkBoundVar(poly, nm->sExprType());
    Node membershipRepr = nm->mkNode(Kind::SEXPR, polyRepr, d_ideal);
    std::vector<Node> argsIdeal{polyRepr, d_ideal};
    Trace("ff::trace") << "..will create pf step " << ProofRule::FF_G << ": "
                       << membershipRepr << " " << argsIdeal << "\n";
    d_proof->addStep(membershipRepr, ProofRule::FF_G, {}, argsIdeal);
    d_polyToMembership.emplace(poly, membershipRepr);
  }
  Trace("ff::trace") << "..will create pf step " << ProofRule::FF_Z << " : "
                     << "0 " << d_ideal << std::endl;
  Node zeroConclusion = produceMembershipNode("0", nm);
  d_proof->addStep(zeroConclusion, ProofRule::FF_Z, {}, {d_ideal});
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
  d_membershipStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->membershipStart(p); });
  d_membershipStep =
      std::function([=](CoCoA::RingElem p) { t->membershipStep(p); });
  d_membershipEnd = std::function([=]() { t->membershipEnd(); });
  CoCoA::proofEnabled = true;
  CoCoA::sPolyProof = d_sPoly;
  CoCoA::reductionStartProof = d_reductionStart;
  CoCoA::reductionStepProof = d_reductionStep;
  CoCoA::reductionEndProof = d_reductionEnd;
  CoCoA::membershipStart = d_membershipStart;
  CoCoA::membershipStep = d_membershipStep;
  CoCoA::membershipEnd = d_membershipEnd;
}
Node GBProof::produceMembershipNode(std::string poly, NodeManager* nm)
{
  Node polyRepr = nm->mkBoundVar(poly, nm->sExprType());
  return nm->mkNode(Kind::SEXPR, polyRepr, d_ideal);
}

// Returns a stored proof por membership of poly
Node GBProof::getMembershipFact(CoCoA::ConstRefRingElem poly)
{
  std::string polyStrRepr = ostring(poly);
  Assert(d_polyToMembership.count(polyStrRepr));
  return d_polyToMembership[polyStrRepr];
}

// Register or returns a membership proof for a given polynomial
Node GBProof::proofIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal)
{
  std::string polyRepr = ostring(poly);
  if (d_polyToMembership.count(polyRepr)) return getMembershipFact(poly);
  Assert(CoCoA::HasGBasis(ideal));
  bool hasElem = CoCoA::IsElem(poly, ideal);
  Assert(hasElem);
  return d_polyToMembership[polyRepr];
}

void GBProof::sPoly(CoCoA::ConstRefRingElem p,
                    CoCoA::ConstRefRingElem q,
                    CoCoA::ConstRefRingElem s)
{
  std::string ss = ostring(s);
  Trace("ff::trace") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_polyToMembership.count(ss) == 0)
  {
    NodeManager* nm = nodeManager();
    Trace("ff::trace") << " keep" << std::endl;
    std::string sPoly = ostring(s);
    Node conclusion = produceMembershipNode(sPoly, nm);
    d_polyToMembership.emplace(sPoly, conclusion);
    Node pMNode = d_polyToMembership[ostring(p)];
    Node qMNode = d_polyToMembership[ostring(q)];
    std::vector<Node> premises{pMNode, qMNode};
    Trace("ff::trace") << "..will create pf step " << ProofRule::FF_S << ": "
                       << premises << " ---> " << conclusion << "\n";
    d_proof->addStep(conclusion, ProofRule::FF_S, premises, {}, true);
  }
  else
  {
    Trace("ff::trace") << " drop" << std::endl;
  }
}

void GBProof::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::trace") << "GBreduction proof start: " << p << std::endl;
  d_reductionSeq.push_back(ostring(p));
}

// q is the reducer, we then assert that q already has a membership proof.
void GBProof::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "GBreduction proof step: " << q << std::endl;
  Assert(d_polyToMembership.count(ostring(q)));
  d_reductionSeq.push_back(ostring(q));
}

void GBProof::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  NodeManager* nm = nodeManager();
  std::string rr = ostring(r);
  Trace("ff::trace") << "reduction proof end: " << r << d_polyToMembership.count(rr) << std::endl;
  if (d_polyToMembership.count(rr) == 0)
  {
    std::vector<Node> premises{};
    std::vector<Node> reductorsSeq{};
    std::unordered_set<std::string> uniquePolys;
    Trace("ff::trace") << " keep" << std::endl;
    Node rrPoly = nm->mkBoundVar(rr, nm->sExprType());
    Node conclusion = nm->mkNode(Kind::SEXPR, rrPoly, d_ideal);
    d_polyToMembership.emplace(rr, conclusion);
    for (std::string poly : d_reductionSeq)
    {
      uniquePolys.insert(poly);
      reductorsSeq.push_back(nm->mkBoundVar(poly, nm->sExprType()));
    }
    for (std::string poly : uniquePolys)
    {
      premises.push_back(d_polyToMembership[poly]);
    }
    d_proof->addStep(
        conclusion, ProofRule::FF_R_DOWN, premises, reductorsSeq, true);
    Trace("ff::trace") << ".. will create pf step: " << ProofRule::FF_R_DOWN
                       << premises << " ---> " << conclusion << std::endl;
  }
  else
  {
    if (TraceIsOn("ff::trace"))
    {
      Trace("ff::trace") << " drop" << std::endl;
    }
  }
  d_reductionSeq.clear();
}

void GBProof::membershipStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_membershipSeq.empty());
  d_reducingPoly = ostring(p);
}

void GBProof::membershipStep(CoCoA::RingElem red)
{
  d_membershipSeq.push_back(ostring(red));
}
void GBProof::membershipEnd()
{
  NodeManager* nm = nodeManager();
  Node conclusion = produceMembershipNode(d_reducingPoly, nm);
  std::vector<Node> reductorsSeq;
  std::unordered_set<std::string> uniquePolys;
  for (std::string p : d_membershipSeq)
  {
    reductorsSeq.push_back(nm->mkBoundVar(p, nm->sExprType()));
    uniquePolys.insert(p);
  }
  std::vector<Node> premises{};
  for (std::string p : uniquePolys)
  {
    premises.push_back(d_polyToMembership[p]);
  }
  premises.push_back(d_polyToMembership["0"]);
  d_proof->addStep(
      conclusion, ProofRule::FF_R_UP, premises, reductorsSeq, true);
  d_membershipSeq.clear();
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

//#endif /* CVC5_USE_COCOA */
