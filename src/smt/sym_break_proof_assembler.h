/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Discharges symmetry breaking lemmas in a refutation.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SYM_BREAK_PROOF_ASSEMBLER_H
#define CVC5__SMT__SYM_BREAK_PROOF_ASSEMBLER_H

#include <map>
#include <memory>
#include <vector>

#include "cvc5/cvc5_proof_rule.h"
#include "expr/node.h"
#include "proof/sym_break_proof_info.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

namespace smt {

/**
 * Turns a refutation that assumes symmetry breaking lemmas into one that does
 * not, using the obligations recorded in a registry. Each step D_{i-1} => D_i
 * of a lemma is discharged either by instantiating the closed refutation with
 * the witness (SUBST_CLOSED), or by replaying it with ite witness terms.
 */
class SymBreakProofAssembler : protected EnvObj
{
  using PfPtr = std::shared_ptr<ProofNode>;

 public:
  SymBreakProofAssembler(Env& env, const SymBreakLemmaRegistry& reg);
  /**
   * Discharge the symmetry breaking lemmas that are free assumptions of pfn, a
   * proof of false, updating pfn in place.
   * @return true if pfn was updated.
   */
  bool process(PfPtr pfn);

 private:
  /** Discharge lem in the refutation r. */
  PfPtr discharge(PfPtr r, const SymBreakLemma& lem);
  /** Refutation from r and a proof pf of the free assumption fact of r. */
  PfPtr dischargeWith(PfPtr r, const Node& fact, PfPtr pf);
  /** Step D_{i-1} => D_i by SUBST_CLOSED; prevPf proves D_{i-1} if non-null. */
  PfPtr stepSubst(PfPtr r, const SymBreakStep& step, PfPtr prevPf);
  /** Step D_{i-1} => D_i by ite witness replay. */
  PfPtr stepIte(PfPtr r, const SymBreakStep& step, PfPtr prevPf);
  /** Proofs of the images of free assumptions under the step's witness. */
  std::map<Node, PfPtr> getImages(const SymBreakStep& step,
                                  PfPtr notClause,
                                  PfPtr prevPf);
  /** Proof of the image of w, or a trust step if unavailable. */
  PfPtr getImage(const std::map<Node, PfPtr>& images,
                 const Node& w,
                 const Node& ws);
  /** Proofs of the conclusions of imp, given proofs of some premises. */
  std::vector<PfPtr> instantiate(const SymBreakImplication& imp,
                                 const std::map<Node, PfPtr>& given);
  /** Proof of conc from proofs of it under cond and under (not cond). */
  PfPtr proveByCases(const Node& cond, PfPtr pos, PfPtr neg, const Node& conc);
  PfPtr mkAndIntro(const std::vector<PfPtr>& pfs);
  /**
   * Make a step concluding expected, checking it first. If the check fails,
   * a trust step with the same children is returned instead.
   */
  PfPtr mkCheckedStep(ProofRule r,
                      const std::vector<PfPtr>& children,
                      const std::vector<Node>& args,
                      const Node& expected);
  std::vector<Node> getFreeAssumptions(PfPtr pf);
  /**
   * Does a formula of pfs mention a skolem whose original form contains a
   * constant of cs? Swapping such constants is not a valid witness.
   */
  bool hasDependentSkolem(const std::vector<PfPtr>& pfs,
                          const std::vector<Node>& cs);
  /** The registry of lemmas */
  const SymBreakLemmaRegistry& d_reg;
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr);
    /** Lemmas discharged */
    IntStat d_lemmas;
    /** Lemmas discharged by a trust step */
    IntStat d_lemmasTrusted;
    /** Chain steps discharged */
    IntStat d_steps;
    /** Images of assumptions discharged by a trust step */
    IntStat d_obligationsTrusted;
    /** Replayed steps that failed to check */
    IntStat d_replayTrusted;
  };
  Statistics d_stats;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__SYM_BREAK_PROOF_ASSEMBLER_H */
