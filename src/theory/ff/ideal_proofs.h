/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields UNSAT trace construction
 */

#include "cvc5_private.h"

#if CVC5_USE_COCOA
#ifndef CVC5__THEORY__IDEAL__PROOF_H
#define CVC5__THEORY__IDEAL__PROOF_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>

#include <functional>
#include <unordered_map>
#include "context/cdlist_forward.h"
#include "smt/env_obj.h"

#include "proof/proof.h"


#include "smt/env_obj.h"
#include "theory/ff/membership_proofs.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * A non-incremental dependency graph for CoCoA polynomials in Groebner basis
 * computation.
 *
 * We represent polynomials as their strings.
 */
class IdealProof : protected EnvObj
{
 public:
  IdealProof(Env& env, size_t id,
             const std::vector<CoCoA::RingElem>& inputs,
             Node nonNullVarPred, CoCoA::ideal cocoaIdeal);
  // ~IdealProof();
  void setFunctionPointers();
  void enableProofHooks();
  void disableProofHooks();
  std::vector<IdealProof> registerRootBranch(
      CoCoA::RingElem poly,
      std::vector<CoCoA::RingElem> roots,
      std::vector<CoCoA::RingElem> basis);

  void registerBranchPolynomial(CoCoA::RingElem branchPoly);
  void registerRoots(std::vector<CoCoA::RingElem> roots);
  std::shared_ptr<IdealProof> registerConclusion(CoCoA::RingElem choicePoly, CoCoA::ideal newIdeal);

  void finishProof(bool rootBranching, CDProof* globalTheoryProofs);
  // p here represents the unit :p.
  Node oneInUnsat(CoCoA::RingElem p, CDProof* globalTheoryProofs);
  Node getUnsatFact();
  Node getSatFact();
 private:
  /**
   * A representation of the Ideal that we are currently proving membership
   * facts.
   */
  Node d_ideal;
  CoCoA::ideal d_cocoaIdeal;
  Node d_validFact;
  Node d_emptyVarFact;
  Node d_branchPolyProof;
  Node d_branchPoly;
  std::vector<Node> d_branchPolyRoots;
  std::vector<std::shared_ptr<IdealProof>> d_childrenProofs;
  /**
   * Maps string representation of polynomials to their corresponding Nodes.
   */
  std::unordered_map<std::string, Node> d_polyToVar;

  /**
   * The user-context-dependent proof object
   *
   */
  CDProof d_proof;
  size_t d_id;
  /*
   * Manager membership proofs for polynomials in this ideal.
   */
  GBProof* d_membershipProofs;

};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PROOF_H */

#endif /* CVC5_USE_COCOA */