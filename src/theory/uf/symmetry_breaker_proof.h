/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Builds the justification of UF symmetry breaking clauses.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__SYMMETRY_BREAKER_PROOF_H
#define CVC5__THEORY__UF__SYMMETRY_BREAKER_PROOF_H

#include <functional>
#include <memory>
#include <set>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "proof/sym_break_proof_info.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class CDProof;

namespace theory {
namespace uf {

/**
 * Builds the implicational obligations justifying a symmetry breaking clause
 * (OR_{c in cts, c != t} t = c), when the clause is emitted.
 */
class SymBreakProofBuilder : protected EnvObj
{
 public:
  /** Returns a formula of the input whose normal form is that of its argument,
   * or null if none. */
  using FindImage = std::function<Node(const Node&)>;

  SymBreakProofBuilder(Env& env);
  /**
   * @param lemma The clause as sent, the rewritten form of the disjunction.
   * @param t The term the clause constrains.
   * @param p The partition of interchangeable constants, ordered.
   * @param cts The constants of the clause.
   * @param ck The pivot constant added to cts for this clause.
   * @param phis The formulas the symmetry was computed on.
   * @param findImage Lookup of formulas in phis modulo normalization.
   * @return The justification; it has no start proof if none was found.
   */
  std::shared_ptr<SymBreakLemma> build(const Node& lemma,
                                       const Node& t,
                                       const std::vector<Node>& p,
                                       const std::set<Node>& cts,
                                       const Node& ck,
                                       const std::vector<Node>& phis,
                                       const FindImage& findImage);

 private:
  /** Closed implication from the free assumptions of pf to concs. */
  SymBreakImplication mkImplication(std::shared_ptr<ProofNode> pf,
                                    const std::vector<Node>& concs);
  /** Prove (=> pre start) where start weakens pre. */
  bool proveStart(const Node& pre, const Node& start, SymBreakImplication& imp);
  /** Build step prev => cur, witnessed by swapping d and c. */
  bool buildStep(const Node& prev,
                 const Node& cur,
                 const Node& d,
                 const Node& c,
                 const Node& litD,
                 const Node& litC,
                 const std::vector<Node>& phis,
                 const std::unordered_set<Node>& phiSet,
                 const FindImage& findImage,
                 SymBreakStep& step);
  /** Add to cdp a proof of tgt from src, equal modulo rewriting and ACI. */
  bool proveNormEquiv(CDProof& cdp, const Node& src, const Node& tgt);
  /** Prove the negations of the literals of clause from its negation. */
  std::vector<Node> negLits(CDProof& cdp, const Node& clause);
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__SYMMETRY_BREAKER_PROOF_H */
