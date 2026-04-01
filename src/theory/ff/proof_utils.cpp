/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof utilities
 */
#include "theory/ff/proof_utils.h"

#include "proof/proof.h"
#include "util/finite_field_value.h"

// std includes

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {
Node polyNormEqNode(NodeManager* nm, Node l, Node r, Node c)
{
  return nm->mkNode(
      Kind::FINITE_FIELD_MULT,
      c,
      nm->mkNode(
          Kind::FINITE_FIELD_ADD, l, nm->mkNode(Kind::FINITE_FIELD_NEG, r)));
}
Node emptyVarPred(NodeManager* nm, Node ideal)
{
  Node variety = nm->mkNode(Kind::FINITE_FIELD_VARIETY, ideal);
  return nm->mkNode(Kind::SET_IS_EMPTY, variety);
}

void produceContradiction(
    NodeManager* nm,
    CDProof* cdp,
    const std::vector<Node>& fieldPolys,
    const std::unordered_map<Node, Node>& litToPolyEq,
    const std::unordered_map<Node, std::pair<Node, Node>>& litToMonic,
    const std::vector<Node>& gens,
    const std::vector<Node>& conflict)
{
  const Node unsatCore = nm->mkAnd(conflict);
  std::vector<Node> newGens{};
  std::vector<Node> litEquivs;
  for (const auto& lit : conflict)
  {
    Node litPolyEq = litToPolyEq.at(lit);
    Node litPoly = litPolyEq[0];
    const Integer size = litPoly.getType().getFfSize();
    Node zero = nm->mkConst(FiniteFieldValue(0, size));
    Node one = nm->mkConst(FiniteFieldValue(1, size));
    const auto res = litToMonic.find(lit);
    Assert(res != litToMonic.end());
    auto [mul, poly] = res->second;
    if (mul.getConst<FiniteFieldValue>().getValue() != 1)
    {
      Node m = polyNormEqNode(nm, litPoly, zero, mul);
      Node n = polyNormEqNode(nm, poly, zero, one);
      Node monicEqZ = nm->mkNode(Kind::EQUAL, poly, zero);
      Node convMonicEq = nm->mkNode(Kind::EQUAL, litPolyEq, monicEqZ);
      Node mnEq = nm->mkNode(Kind::EQUAL, m, n);
      cdp->addStep(mnEq, ProofRule::FF_POLY_NORM, {}, {mnEq});
      cdp->addStep(
          convMonicEq, ProofRule::FF_POLY_NORM_EQ, {mnEq}, {convMonicEq});
      cdp->addStep(monicEqZ, ProofRule::EQ_RESOLVE, {litPolyEq, convMonicEq}, {});
      Node litConvEq = nm->mkNode(Kind::EQUAL, lit, litPolyEq);
      Node litMonicEq = nm->mkNode(Kind::EQUAL, lit, monicEqZ);
      cdp->addStep(litMonicEq, ProofRule::TRANS, {litConvEq, convMonicEq}, {});
      litEquivs.push_back(litMonicEq);
      newGens.push_back(poly);
    }
    else
    {
      // Already have a proof of equivalence.
      Node eq = litToPolyEq.at(lit);
      Node convertedPoly = eq[0];
      Node litEquiv = nm->mkNode(Kind::EQUAL, lit, eq);
      litEquivs.push_back(litEquiv);
      newGens.push_back(convertedPoly);
    }
  }
  std::vector<Node> newLits;
  for (const auto& litEquiv : litEquivs)
  {
    Assert(litEquiv[1].getKind() == Kind::EQUAL);
    newLits.push_back(litEquiv[1]);
  }
  Node core = nm->mkAnd(newLits);
  Node coreEquiv = nm->mkNode(Kind::EQUAL, unsatCore, core);
  Node idealGens = nm->mkNode(Kind::FINITE_FIELD_IDEAL, newGens);
  if (core.getKind() == Kind::AND)
    cdp->addStep(coreEquiv, ProofRule::NARY_CONG, litEquivs, {unsatCore});
  cdp->addStep(core, ProofRule::EQ_RESOLVE, {unsatCore, coreEquiv}, {});
  Trace("ff::proof") << "Assumption: " << unsatCore << std::endl;
  Trace("ff:proof") << "Converting from " << core << std::endl;
  Node commonRoot = emptyVarPred(nm, idealGens).negate();
  Node satIffCRoot = nm->mkNode(Kind::EQUAL, core, commonRoot);
  cdp->addStep(
      satIffCRoot, ProofRule::FF_POLY_CONVERSION, {}, {core, commonRoot});
  cdp->addStep(commonRoot, ProofRule::EQ_RESOLVE, {core, satIffCRoot}, {});
  if (!fieldPolys.empty())
  {
    newGens.insert(newGens.end(), fieldPolys.begin(), fieldPolys.end());
    idealGens = nm->mkNode(Kind::FINITE_FIELD_IDEAL, newGens);
    Node commonRootFieldPolys = emptyVarPred(nm, idealGens).negate();
    cdp->addStep(commonRootFieldPolys,
                 ProofRule::FF_FIELD_POLYS,
                 {commonRoot},
                 {fieldPolys});
    commonRoot = commonRootFieldPolys;
  }
  Node falseNode = nm->mkConst<bool>(false);
  Node noCommonRoot = emptyVarPred(nm, idealGens);
  cdp->addStep(falseNode, ProofRule::CONTRA, {noCommonRoot, commonRoot}, {});
}

Node polyComb(NodeManager* nm, Node rs, Node ms)
{
  Assert(rs.getNumChildren() == ms.getNumChildren());
  Assert(rs.getNumChildren() != 0);
  std::vector<Node> monoms;
  for (size_t it = 0; it < rs.getNumChildren(); ++it)
  {
    Node monom = nm->mkNode(Kind::FINITE_FIELD_MULT, ms[it], rs[it]);
    monoms.push_back(monom);
  }
  if (monoms.size() == 1) return monoms[0];
  return nm->mkNode(Kind::FINITE_FIELD_ADD, monoms);
}

void registerDisequalityProof(
    NodeManager* nm, Node orig, Node conv, Node sk, CDProof* cdp)
{
  Node l = orig[0][0];
  Node r = orig[0][1];
  const Integer size = orig[0][0].getType().getFfSize();
  Node sub = nm->mkNode(
      Kind::FINITE_FIELD_ADD, l, nm->mkNode(Kind::FINITE_FIELD_NEG, r));
  Node one = nm->mkConst(FiniteFieldValue(1, size));
  Node minusOne = nm->mkConst(FiniteFieldValue(-1, size));
  Node zero = nm->mkConst(FiniteFieldValue(0, size));
  Node n = nm->mkNode(Kind::FINITE_FIELD_ADD,
                      nm->mkNode(Kind::FINITE_FIELD_MULT, sub, sk),
                      minusOne);
  Node nEq = nm->mkNode(Kind::EQUAL, n, zero);
  Node convEq = nm->mkNode(Kind::EQUAL, conv, zero);
  Node equiv = nm->mkNode(Kind::EQUAL, nEq, convEq);
  Node equivZ = nm->mkNode(Kind::EQUAL,
                           polyNormEqNode(nm, n, zero, one),
                           polyNormEqNode(nm, conv, zero, one));
  Node origNEquiv = nm->mkNode(Kind::EQUAL, orig, nEq);
  Node origConvEquiv = nm->mkNode(Kind::EQUAL, orig, convEq);
  cdp->addStep(origNEquiv, ProofRule::FF_DISEQ, {}, {l, r, sk});
  cdp->addStep(equivZ, ProofRule::FF_POLY_NORM, {}, {equivZ});
  cdp->addStep(equiv, ProofRule::FF_POLY_NORM_EQ, {equivZ}, {equiv});
  cdp->addStep(origConvEquiv, ProofRule::TRANS, {origNEquiv, equiv}, {});
  cdp->addStep(convEq, ProofRule::EQ_RESOLVE, {orig, origConvEquiv}, {});
}

void registerEqualityProof(NodeManager* nm, Node orig, Node conv, CDProof* cdp)
{
  Node l = orig[0];
  Node r = orig[1];
  const Integer size = orig[0].getType().getFfSize();
  Node zero = nm->mkConst(FiniteFieldValue(0, size));
  Node one = nm->mkConst(FiniteFieldValue(1, size));
  Node n = polyNormEqNode(nm, l, r, one);
  Node convEq = nm->mkNode(Kind::EQUAL, conv, zero);
  Node equivP = nm->mkNode(Kind::EQUAL, n, polyNormEqNode(nm, conv, zero, one));
  Node litConvEq = nm->mkNode(Kind::EQUAL, orig, convEq);
  cdp->addStep(equivP, ProofRule::FF_POLY_NORM, {}, {equivP});
  cdp->addStep(litConvEq, ProofRule::FF_POLY_NORM_EQ, {equivP}, {litConvEq});
  cdp->addStep(convEq, ProofRule::EQ_RESOLVE, {orig, litConvEq}, {});
}

ProofInfo::ProofInfo(ProofRule id,
                     std::vector<Node> children,
                     std::vector<Node> args)
    : d_id(id), d_children(children), d_args(args)
{
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
