/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility to convert between libpoly polynomials and CoCoALib polynomials
 * over a prime field.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__COCOA_CONVERTER_H
#define CVC5__THEORY__FF__COCOA_CONVERTER_H

#ifdef CVC5_POLY_IMP
#ifdef CVC5_USE_COCOA

#include <CoCoA/library.H>
#include <poly/polyxx.h>

#include <map>
#include <utility>

#include "base/output.h"
#include "theory/ff/proof_utils.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Converter between libpoly polynomials and CoCoA polynomials, both over a
 * prime field 𝔽ₚ.
 *
 * Coefficients are field elements. On the libpoly side they are represented
 * as poly::Integer values living in a modular IntegerRing (inside a
 * polynomial context); on the CoCoA side they are elements of CoCoA::RingFp.
 * Neither side uses rationals.
 *
 * For the CoCoA → libpoly direction the caller must first provide, via
 * setLibpolyContext, the libpoly polynomial context bound to the FF ring.
 * The converter does not take ownership of that context.
 */
class CoCoAConverter
{
 public:
  /** Set the libpoly polynomial context used for the CoCoA → libpoly path. */
  void setLibpolyContext(const lp_polynomial_context_t* ctx) { d_ffCtx = ctx; }

  /** Add mapping from libpoly variable to a CoCoA variable */
  void addVar(const poly::Variable& pv, const CoCoA::RingElem& cv)
  {
    d_varPC.emplace(pv, cv);
  }
  /**
   * Add mapping from a CoCoA variable, identified by its ring id and the
   * indet identifier, to a libpoly variable.
   */
  void addVar(const std::pair<long, size_t>& cv, const poly::Variable& pv)
  {
    d_varCP.emplace(cv, pv);
  }

  /**
   * Converts a libpoly integer to a CoCoA::BigInt.
   */
  CoCoA::BigInt operator()(const poly::Integer& i) const
  {
    return CoCoA::BigIntFromMPZ(poly::detail::cast_to_gmp(&i)->get_mpz_t());
  }
  /**
   * Converts a univariate libpoly polynomial p in variable var to a CoCoA
   * polynomial in the given CoCoA ring. The ring should be a polynomial
   * ring over 𝔽ₚ.
   */
  CoCoA::RingElem operator()(const poly::UPolynomial& p,
                             const poly::Variable& var,
                             const CoCoA::ring& ring) const;

  /**
   * Converts a libpoly polynomial q to a CoCoA polynomial in the given CoCoA
   * ring. The ring should be a polynomial ring over 𝔽ₚ.
   */
  CoCoA::RingElem operator()(const poly::Polynomial& q,
                             const CoCoA::ring& ring) const;

  /**
   * Converts a CoCoA polynomial (over 𝔽ₚ) to a libpoly polynomial (in the
   * FF context previously registered via setLibpolyContext).
   */
  poly::Polynomial operator()(const CoCoA::RingElem& p) const;

 private:

  /** Helper class for the conversion of a libpoly polynomial to CoCoA. */
  struct CoCoAPolyConstructor
  {
    const CoCoAConverter& d_state;
    const CoCoA::ring& d_ring;
    CoCoA::RingElem d_result;
  };

  /**
   * Maps libpoly variables to indets in CoCoA.
   */
  std::map<poly::Variable, CoCoA::RingElem> d_varPC;

  /**
   * Maps CoCoA variables (identified by ring id and indet id) to libpoly
   * variables.
   */
  std::map<std::pair<long, size_t>, poly::Variable> d_varCP;

  /** libpoly polynomial context over the target FF ring. */
  const lp_polynomial_context_t* d_ffCtx{nullptr};
};

/**
 * Compute gcd(f, r) with Bezout witness, where r = (x^q mod f) - x is the
 * reduced field polynomial. Equivalent to gcd(f, x^q - x) for distinct-roots
 * purposes, but avoids materializing anything of degree q. f must be
 * univariate over a prime field.
 */
GcdInfo distinctRootsGcd(const CoCoA::RingElem& f);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif
#endif
