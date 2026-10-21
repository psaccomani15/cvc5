/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification data for symmetry breaking lemmas.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__SYM_BREAK_PROOF_INFO_H
#define CVC5__PROOF__SYM_BREAK_PROOF_INFO_H

#include <memory>
#include <vector>

#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {

class ProofNode;

/**
 * Closed proof of (=> (and premises) (and conclusions)). If premises is empty,
 * the proof concludes (and conclusions) directly.
 */
struct SymBreakImplication
{
  std::shared_ptr<ProofNode> d_proof;
  std::vector<Node> d_premises;
  std::vector<Node> d_conclusions;
};

/**
 * One step D_{i-1} => D_i of a symmetry breaking chain, justified by the
 * witness swapping constants d_d and d_c. The obligation proves
 * F /\ D_{i-1} /\ ~D_i => (F /\ D_i)sigma, restricted to the formulas of F
 * moved by sigma: d_obligation.d_conclusions[j] is d_sources[j]sigma.
 */
struct SymBreakStep
{
  Node d_d;
  Node d_c;
  Node d_prevClause;
  Node d_clause;
  SymBreakImplication d_obligation;
  std::vector<Node> d_sources;
};

/**
 * A symmetry breaking lemma and its justification: d_start proves
 * (=> precondition D_0), then d_steps (in order i = 1..m) lead to d_lemma.
 * If d_start has no proof, the lemma could not be justified.
 */
struct SymBreakLemma
{
  Node d_lemma;
  SymBreakImplication d_start;
  std::vector<SymBreakStep> d_steps;
};

/** User-context dependent list of symmetry breaking lemmas, in send order. */
class SymBreakLemmaRegistry
{
 public:
  SymBreakLemmaRegistry(context::Context* c) : d_lemmas(c) {}
  void add(std::shared_ptr<SymBreakLemma> lem) { d_lemmas.push_back(lem); }
  const context::CDList<std::shared_ptr<SymBreakLemma>>& get() const
  {
    return d_lemmas;
  }
  bool empty() const { return d_lemmas.empty(); }

 private:
  context::CDList<std::shared_ptr<SymBreakLemma>> d_lemmas;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__SYM_BREAK_PROOF_INFO_H */
