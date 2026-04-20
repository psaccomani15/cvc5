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
 *
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PROOF__UTIL_H
#define CVC5__THEORY__FF__PROOF__UTIL_H

// internal includes
#include "expr/node.h"
#include "proof/proof.h"
#include "util/finite_field_value.h"

#ifdef CVC5_USE_COCOA
#include "CoCoA/ring.H"
#endif

namespace cvc5::internal {
namespace theory {
namespace ff {
// Produce a statement that the ideal is non Empty
Node varietyIsEmpty(NodeManager* nm, Node ideal);

void produceContradiction(
    NodeManager* nm,
    CDProof* cdp,
    const std::vector<Node>& fieldPolys,
    const std::unordered_map<Node, Node>& litToPolyEq,
    const std::unordered_map<Node, std::pair<Node, Node>>& litToMonic,
    const std::vector<Node>& conflict);

Node polyComb(NodeManager* nm, Node rs, Node ms);

void registerDisequalityProof(
    NodeManager* nm, Node orig, Node conv, Node sk, CDProof* cdp);

void registerEqualityProof(NodeManager* nm, Node orig, Node conv, CDProof* cdp);

// Stores elements that will be inserted to a CDProof
class ProofInfo
{
 public:
  ProofInfo(ProofRule id, std::vector<Node> children, std::vector<Node> args);
  ProofRule d_id;
  std::vector<Node> d_children;
  std::vector<Node> d_args;
};

#ifdef CVC5_USE_COCOA
/**
 * Distinct-roots gcd witness for a univariate f over 𝔽_q.
 * Let r = (x^q mod f) - x. Then res = gcd(f, r) and
 * bezoutA * f + bezoutB * r = res.
 */
struct GcdInfo
{
  CoCoA::RingElem res;
  CoCoA::RingElem bezoutA;
  CoCoA::RingElem bezoutB;
  CoCoA::RingElem reducedFieldPoly;
};
#endif

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif 
