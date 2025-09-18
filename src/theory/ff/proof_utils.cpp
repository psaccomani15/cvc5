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

// std includes

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {

Node emptyVarPred(NodeManager* nm, Node ideal)
{
  Node variety = nm->mkNode(Kind::FINITE_FIELD_VARIETY, ideal);
  return nm->mkNode(Kind::SET_IS_EMPTY, variety);
}

void produceContradiction(NodeManager *nm, CDProof *cdp, std::vector<Node>& fieldPolys,
                                     std::vector<Node> &gens, std::vector<Node> &conflict)
{
  Node idealGens = nm->mkNode(Kind::FINITE_FIELD_IDEAL, gens);
  const Node unsatCore = nm->mkAnd(conflict);
  cdp->addStep(unsatCore, ProofRule::ASSUME, {}, {unsatCore});
  Trace("ff::proof") << "Assumption: " << unsatCore << std::endl;
  Node commonRoot = emptyVarPred(nm, idealGens).negate();
  Node satIffCRoot = nm->mkNode(Kind::EQUAL, unsatCore, commonRoot);
  cdp->addStep(satIffCRoot, ProofRule::FF_POLY_CONVERSION, {}, {});
  cdp->addStep(
      commonRoot, ProofRule::EQ_RESOLVE, {unsatCore, satIffCRoot}, {});
  if (!fieldPolys.empty())
  {
    std::vector<Node> newGens = gens;
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
  cdp->addStep(
      falseNode, ProofRule::CONTRA, {commonRoot, noCommonRoot}, {});
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
