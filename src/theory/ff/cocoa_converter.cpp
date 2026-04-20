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

#include "theory/ff/cocoa_converter.h"

#ifdef CVC5_POLY_IMP
#ifdef CVC5_USE_COCOA

#include <CoCoA/BigInt.H>
#include <CoCoA/BigIntOps.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/convert.H>

#include <sstream>

#include "base/check.h"
#include "theory/ff/uni_roots.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

CoCoA::RingElem CoCoAConverter::operator()(const poly::UPolynomial& p,
                                           const poly::Variable& var,
                                           const CoCoA::ring& ring) const
{
  std::vector<poly::Integer> coeffs = poly::coefficients(p);
  CoCoA::RingElem res(ring);
  CoCoA::RingElem v = CoCoA::indet(ring, 0);
  CoCoA::RingElem mult(ring, 1);
  for (const auto& c : coeffs)
  {
    if (!poly::is_zero(c))
    {
      res += CoCoA::RingElem(ring, (*this)(c)) * mult;
    }
    mult *= v;
  }
  Trace("ff::cocoa") << "Converted " << p << " to " << res << std::endl;
  return res;
}

CoCoA::RingElem CoCoAConverter::operator()(const poly::Polynomial& q,
                                           const CoCoA::ring& ring) const
{
  CoCoAPolyConstructor cmd{*this, ring, CoCoA::RingElem(ring)};
  lp_polynomial_traverse_f f =
      [](const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
        CoCoAPolyConstructor* d = static_cast<CoCoAPolyConstructor*>(data);
        CoCoA::BigInt coeff = (d->d_state)(*poly::detail::cast_from(&m->a));
        CoCoA::RingElem re(d->d_ring, coeff);
        for (size_t i = 0; i < m->n; ++i)
        {
          CoCoA::RingElem var = d->d_state.d_varPC.at(m->p[i].x);
          re *= CoCoA::power(var, m->p[i].d);
        }
        d->d_result += re;
      };
  lp_polynomial_traverse(q.get_internal(), f, &cmd);
  Trace("ff::cocoa") << "Converted " << q << " to " << cmd.d_result
                     << std::endl;
  return cmd.d_result;
}

poly::Polynomial CoCoAConverter::operator()(const CoCoA::RingElem& p) const
{
  Assert(d_ffCtx != nullptr)
      << "CoCoAConverter: libpoly FF context must be set via "
         "setLibpolyContext before converting from CoCoA";

  poly::Polynomial res(d_ffCtx);
  const lp_int_ring_t* K = d_ffCtx->K;
  const CoCoA::ring& owner = CoCoA::owner(p);

  for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(p); !CoCoA::IsEnded(it);
       ++it)
  {
    // Pull the 𝔽ₚ coefficient out as a BigInt in [0, p). CanonicalRepr maps
    // the Zp element into its underlying ZZ representative.
    CoCoA::BigInt coeffBi;
    bool isInt = CoCoA::IsInteger(coeffBi, CoCoA::CanonicalRepr(CoCoA::coeff(it)));
    AlwaysAssert(isInt) << "CoCoAConverter: 𝔽ₚ coefficient did not reduce to an "
                     "integer representative";

    // Stringify and rebuild as an lp_integer reduced into K.
    std::ostringstream os;
    os << coeffBi;

    lp_monomial_t m;
    lp_monomial_construct(d_ffCtx, &m);
    lp_integer_t cInt;
    lp_integer_construct_from_string(K, &cInt, os.str().c_str(), 10);
    lp_monomial_set_coefficient(d_ffCtx, &m, &cInt);
    lp_integer_destruct(&cInt);

    if (!CoCoA::IsOne(CoCoA::PP(it)))
    {
      std::vector<long> exps;
      CoCoA::exponents(exps, CoCoA::PP(it));
      for (size_t vid = 0; vid < exps.size(); ++vid)
      {
        if (exps[vid] == 0) continue;
        poly::Variable v =
            d_varCP.at(std::make_pair(CoCoA::RingID(owner), vid));
        lp_monomial_push(&m, v.get_internal(), exps[vid]);
      }
    }

    lp_polynomial_add_monomial(res.get_internal(), &m);
    lp_monomial_destruct(&m);
  }

  Trace("ff::cocoa") << "Converted " << p << " to " << res << std::endl;
  return res;
}

GcdInfo distinctRootsGcd(const CoCoA::RingElem& f)
{
  GcdInfo info;
  CoCoA::ring ring = CoCoA::owner(f);
  CoCoA::ring field = ring->myBaseRing();
  int idx = CoCoA::UnivariateIndetIndex(f);
  Assert(idx >= 0) << "distinctRootsGcd: f is not univariate";
  CoCoA::RingElem x = CoCoA::indet(ring, idx);

  CoCoA::BigInt q =
      CoCoA::power(CoCoA::characteristic(field), CoCoA::LogCardinality(field));
  CoCoA::RingElem reducedFieldPoly = powerMod(x, q, f) - x;

  CoCoA::BigInt p = CoCoA::characteristic(field);
  std::ostringstream pss;
  pss << p;
  poly::Integer pInt(pss.str().c_str(), 10);
  poly::IntegerRing K(pInt, /*is_prime=*/true);
  const poly::Context& defCtx = poly::Context::get_context();
  lp_polynomial_context_t* ffCtx = lp_polynomial_context_new(
      K.get_internal(),
      defCtx.get_variable_db(),
      defCtx.get_variable_order());
  poly::Variable var("__ffgcd_var");

  CoCoAConverter conv;
  conv.setLibpolyContext(ffCtx);
  conv.addVar(var, x);
  conv.addVar(std::make_pair(CoCoA::RingID(ring), static_cast<size_t>(idx)),
              var);

  poly::Polynomial fP = conv(f);
  poly::Polynomial gP = conv(reducedFieldPoly);
  poly::UPolynomial fU(lp_polynomial_to_univariate(fP.get_internal()));
  poly::UPolynomial gU(lp_polynomial_to_univariate(gP.get_internal()));

  poly::UPolynomial uU, vU;
  poly::UPolynomial dU = poly::extended_gcd(fU, gU, uU, vU);

  poly::Polynomial dP(lp_upolynomial_to_polynomial(
      dU.get_internal(), ffCtx, var.get_internal()));
  poly::Polynomial uP(lp_upolynomial_to_polynomial(
      uU.get_internal(), ffCtx, var.get_internal()));
  poly::Polynomial vP(lp_upolynomial_to_polynomial(
      vU.get_internal(), ffCtx, var.get_internal()));

  info.res = conv(dP, ring);
  info.bezoutA = conv(uP, ring);
  info.bezoutB = conv(vP, ring);
  info.reducedFieldPoly = reducedFieldPoly;

  lp_polynomial_context_detach(ffCtx);
  return info;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif
