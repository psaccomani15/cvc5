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
#ifndef CVC5__THEORY__GB__PROOF_H
#define CVC5__THEORY__GB__PROOF_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>
#include <CoCoA/ideal.H>
#include <functional>
#include <unordered_map>
#include "smt/env_obj.h"
#include "expr/node.h"


namespace cvc5::internal {

class CDProof;

namespace theory {
namespace ff {

/**
 * A non-incremental dependency graph for CoCoA polynomials in Groebner basis
 * computation.
 *
 * We represent polynomials as their strings.
 */
  class GBProof : protected EnvObj
  {
   public:
    GBProof(Env& env,
            const std::vector<CoCoA::RingElem> polys,
            Node ideal,
            CDProof* proof);

    /*
     * Hooks into CoCoA. The functions are then called by CoCoA Groebner Basis
     * during Reduction and computation of SPolynomials
     */
    void setFunctionPointers();
    /*
     * Returns a membership proof for a given polynomial.
     * The polynomial must be already registered in d_polyToVar.
     */
    Node getMembershipFact(CoCoA::ConstRefRingElem poly);

    /*
     * Produces/uses a membership fact for arbitrary polynomials in the ideal.
     * The argument "poly" *must* be an element of the ideal.
     */
    Node proofIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal);

   private:
    /**
     * Produces Nodes that represents ideal membership facts.
     */
    Node produceMembershipNode(std::string poly, NodeManager* nm);

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
    std::vector<std::string> d_reductionSeq{};

    /**
     * The sequence of polynomials in GBasis used in the reduction during
     * independent membership proof production.
     */
    std::vector<std::string> d_membershipSeq{};

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
    std::function<void(CoCoA::ConstRefRingElem, CoCoA::ConstRefRingElem)> d_monicProof{};
    std::function<void(CoCoA::ConstRefRingElem)> d_membershipStart{};
    std::function<void(CoCoA::ConstRefRingElem)> d_membershipStep{};
    std::function<void(void)> d_membershipEnd{};

    /**
     * A representation of the Ideal that we are currently proving membership
     * facts from An sExpr of bound variables that represents the initial set of
     * generators.
     */
    Node d_ideal;

    /**
     * Maps polynomials to their original ideal membership proofs
     */
    std::unordered_map<std::string, Node> d_polyToMembership;
    /**
     * Used for arbitrary membership proofs.
     * Represents the polynomial that we are currently testing for membership
     */
    std::string d_reducingPoly;
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
