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
// external includes
#ifdef CVC5_USE_COCOA
#include <CoCoA/ring.H>
#endif /* CVC5_USE_COCOA */

// internal includes
#include "expr/node.h"
#include "proof/proof.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
// Produce a statement that the ideal is non Empty
Node emptyVarPred(NodeManager* nm, Node ideal);

void produceContradiction(NodeManager *nm, CDProof *cdp, std::vector<Node> &fieldPolys, std::vector<Node> &gens, std::vector<Node> &conflict);
// Stores elements that will be inserted to a CDProof
class ProofInfo
{
 public:
  ProofInfo(ProofRule id, std::vector<Node> children, std::vector<Node> args);
  ProofRule d_id;
  std::vector<Node> d_children;
  std::vector<Node> d_args;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif
