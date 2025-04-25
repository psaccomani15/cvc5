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
 * Ideal Membership Proofs Engine
 */

#include "cvc5_private.h"

#if CVC5_USE_COCOA
#ifndef CVC5__THEORY__GB__PROOF_H
#define CVC5__THEORY__GB__PROOF_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>

#include <functional>
#include <unordered_map>

#include "expr/node.h"
#include "proof/proof.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
namespace cvc5::internal {

class CDProof;

namespace theory {
namespace ff {

/**
 * Tracks computations done by CoCoALib.
 * First, we collect all information needed for proof construction, to build the
 * proof later. The reason for this choice, is that we may need to restrict
 * ourselves to an Unsat Core.
 */
class GBProof : protected EnvObj
{
 public:
  GBProof(Env& env,
          std::vector<Node> polys,
          Node ideal,
          CocoaEncoder& enc,
          CDProof* proof);

  /**
   * Hooks into CoCoA. The functions are then called by CoCoA Groebner Basis
   * during Reduction and computation of SPolynomials
   */
  void setFunctionPointers();
  /**
   * Returns a membership proof for a given polynomial.
   * @param poly: The polynomial must be already registered in d_polyToVar.
   */
  Node getMembershipFact(CoCoA::ConstRefRingElem poly);

  /**
   * Produces/uses a membership fact for arbitrary polynomials in the ideal.
   * @param poly: The polynomial that we are proving membership: *must* be an
   * element of the ideal.
   * @param ideal: the cocoalib representantion for the ideal.
   */
  Node proofIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal);
  /**
   * Restrict oursevels to a subset of of the original ideal representation.
   * Used for Unsat Core Restriction.
   */
  void updateIdeal(Node ideal);
  void registerProofs();

 private:
  /**
   * Produces Nodes that represents ideal membership facts.
   */
  Node produceMembershipNode(Node poly);

  void storeProof(Node poly,
                  ProofRule id,
                  std::vector<Node> children,
                  std::vector<Node> args);

  /**
   * Call this when s = spoly(p, q);
   */
  void sPoly(CoCoA::ConstRefRingElem p,
             CoCoA::ConstRefRingElem q,
             CoCoA::ConstRefRingElem s);
  /**
   * Call this when we start reducing p.
   */
  void reductionStart(CoCoA::ConstRefRingElem p);
  /**
   * Call this when there is a reduction on q.
   */
  void reductionStep(CoCoA::ConstRefRingElem q);
  /**
   * Call this when we finish reducing with r.
   */
  void reductionEnd(CoCoA::ConstRefRingElem r);
  /**
   * Call this when len(gens) == 1 i.e GBasis(poly) = {monic(poly)}
   */
  void monicProof(CoCoA::ConstRefRingElem poly, CoCoA::ConstRefRingElem monic);

  void membershipStart(CoCoA::ConstRefRingElem p);

  void membershipStep(CoCoA::RingElem s);

  void membershipEnd();
  /**
   * For each poly string, its index in the input sequence.
   */
  std::unordered_map<std::string, size_t> d_inputNumbers;

  /**
   * The sequence of polynomials used for reduction during GBasis production.
   */
  std::vector<Node> d_reductionSeq{};

  /**
   * The sequence of polynomials in GBasis used in the reduction during
   * independent membership proof production.
   */
  std::vector<Node> d_membershipSeq{};

  /**
   * Hooks for:
   * Gbasis Proof Production: sPoly, reductionStart, reductionStep,
   * reductionEnd Arbitrary Poly Proof Production: membershipStart,
   * membershipStep and membershipEnd.
   */

  std::function<void(CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem)>
      d_sPoly{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStep{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionEnd{};
  std::function<void(CoCoA::ConstRefRingElem, CoCoA::ConstRefRingElem)>
      d_monicProof{};
  std::function<void(CoCoA::ConstRefRingElem)> d_membershipStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_membershipStep{};
  std::function<void(void)> d_membershipEnd{};

  /**
   * A representation of the Ideal that we are currently proving membership
   * facts from An sExpr of bound variables that represents the initial set of
   * generators.
   */
  Node d_ideal;
  std::unordered_map<Node, ProofInfo> d_factToProof;
  CocoaEncoder d_enc;
  /**
   * Maps polynomials to their ideal membership proofs
   */
  std::unordered_map<Node, Node> d_polyToMembership;
  /**
   * Used for arbitrary membership proofs.
   * Represents the polynomial that we are currently testing for membership
   */
  Node d_reducingPoly;
  /**
   * The user-context-dependent proof object
   */
  CDProof* d_proof;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PROOF_H */

#endif /* CVC5_USE_COCOA */
