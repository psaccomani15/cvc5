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

ProofInfo::ProofInfo(ProofRule id,
                     std::vector<Node> children,
                     std::vector<Node> args)
    : d_id(id), d_children(children), d_args(args)
{
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
