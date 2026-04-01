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
 * encoding Nodes as cocoa ring elements.
 */

#include "theory/shared_terms_database.h"
#ifdef CVC5_USE_COCOA

#include "theory/ff/cocoa_encoder.h"

// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyRing.H>

// std includes
#include <sstream>

// internal includes
#include "expr/node_traversal.h"
#include "expr/node.h"
#include "theory/ff/cocoa_util.h"
#include "theory/ff/proof_utils.h"
#include "theory/theory.h"
#include "expr/skolem_manager.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

#define LETTER(c) (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))

// CoCoA symbols must start with a letter and contain only letters, numbers, and
// underscores.
//
// Our encoding is described within
CoCoA::symbol cocoaSym(const std::string& varName, std::optional<size_t> index)
{
  std::ostringstream o;
  for (const auto c : varName)
  {
    // letters and numbers as themselves
    uint8_t code = c;
    if (LETTER(c) || ('0' <= c && c <= '9'))
    {
      o << c;
    }
    // _ as __
    else if ('_' == c)
    {
      o << "__";
    }
    // other as _xXX (XX is hex)
    else
    {
      o << "_x"
        << "0123456789abcdef"[code & 0x0f]
        << "0123456789abcdef"[(code >> 4) & 0x0f];
    }
  }
  // if we're starting with something bad, prepend u__; note that the above
  // never produces __.
  std::string s = o.str();
  if (!LETTER(s[0]))
  {
    s.insert(0, "u__");
  }
  return index.has_value() ? CoCoA::symbol(s, *index) : CoCoA::symbol(s);
}

CocoaEncoder::CocoaEncoder(NodeManager* nm, CDProof *cdp, const FfSize& size)
    : FieldObj(nm, size), d_nm(nm), d_cdp(cdp)
{
}

CoCoA::symbol CocoaEncoder::freshSym(const std::string& varName,
                                     std::optional<size_t> index)
{
  Trace("ff::cocoa::sym") << "CoCoA sym for " << varName;
  if (index.has_value())
  {
    Trace("ff::cocoa::sym") << "[" << *index << "]";
  }
  Trace("ff::cocoa::sym") << std::endl;
  Assert(d_stage == Stage::Scan);
  std::optional<size_t> suffix = {};
  CoCoA::symbol sym("dummy");
  std::string symString;
  do
  {
    std::string n = suffix.has_value()
                        ? varName + "_" + std::to_string(suffix.value())
                        : varName;
    sym = cocoaSym(n, index);
    symString = extractStr(sym);
    if (suffix.has_value())
    {
      *suffix += 1;
    }
    else
    {
      suffix = std::make_optional(0);
    }
  } while (d_vars.count(symString));
  d_vars.insert(symString);
  d_syms.push_back(sym);
  return sym;
}

void CocoaEncoder::endScan()
{
  Assert(d_stage == Stage::Scan);
  d_stage = Stage::Encode;
  d_polyRing = CoCoA::NewPolyRing(coeffRing(), d_syms);
  for (size_t i = 0, n = d_syms.size(); i < n; ++i)
  {
    d_symPolys.insert({extractStr(d_syms[i]), CoCoA::indet(*d_polyRing, i)});
  }
}

 
void CocoaEncoder::addFact(const Node& fact)
{
  Assert(isFfFact(fact, size()));
  if (d_stage == Stage::Scan)
  {
    for (const auto& node :
         NodeDfsIterable(fact, VisitOrder::POSTORDER, [this](TNode nn) {
           return d_scanned.count(nn);
         }))
    {
      if (!d_scanned.insert(node).second)
      {
        continue;
      }
      if (isFfLeaf(node, size()) && !node.isConst())
      {
        Trace("ff::cocoa") << "CoCoA var sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym(node.getName());
        Assert(!d_varSyms.count(node));
        Assert(!d_symNodes.count(extractStr(sym)));
        d_varSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
      else if (node.getKind() == Kind::NOT && isFfFact(node, size()))
      {
        Trace("ff::cocoa") << "CoCoA != sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym("diseq", d_diseqSyms.size());
        Node newVar = d_nm->getSkolemManager()->mkSkolemFunction(SkolemId::FF_DISEQ, node);   
        d_diseqSyms.insert({node, sym});
        d_diseqNodes.insert({extractStr(sym), newVar});
        d_skolemVar.insert({node, newVar});
      }
      else if (node.getKind() == Kind::FINITE_FIELD_BITSUM)
      {
        Trace("ff::cocoa") << "CoCoA bitsum sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym("bitsum", d_bitsumSyms.size());
        d_bitsumSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
    }
  }
  else
  {
    Assert(d_stage == Stage::Encode);
    encodeFact(fact);
    d_polys.push_back(d_cache.at(fact));
  }
}

std::vector<Node> CocoaEncoder::bitsums() const
{
  std::vector<Node> bs;
  for (const auto& [b, _] : d_bitsumSyms)
  {
    bs.push_back(b);
  }
  return bs;
}

const Node& CocoaEncoder::symNode(CoCoA::symbol s) const
{
  Assert(d_symNodes.count(extractStr(s)));
  return d_symNodes.at(extractStr(s));
}

bool CocoaEncoder::hasNode(CoCoA::symbol s) const
{
  return d_symNodes.count(extractStr(s));
}

std::vector<std::pair<size_t, Node>> CocoaEncoder::nodeIndets() const
{
  std::vector<std::pair<size_t, Node>> out;
  for (size_t i = 0, end = d_syms.size(); i < end; ++i)
  {
    if (hasNode(d_syms[i]))
    {
      Node n = symNode(d_syms[i]);
      // skip indets for !=
      if (isFfLeaf(n, size()))
      {
        out.emplace_back(i, n);
      }
    }
  }
  return out;
}

FiniteFieldValue CocoaEncoder::cocoaFfToFfVal(const Scalar& elem)
{
  Assert(CoCoA::owner(elem) == coeffRing());
  return ff::cocoaFfToFfVal(elem, size());
}

const Node& CocoaEncoder::polyFact(const Poly& poly) const
{
  return d_polyFacts.at(extractStr(poly));
}

bool CocoaEncoder::polyHasFact(const Poly& poly) const
{
  return d_polyFacts.count(extractStr(poly));
}

const Poly& CocoaEncoder::symPoly(CoCoA::symbol s) const
{
  Assert(d_symPolys.count(extractStr(s)));
  return d_symPolys.at(extractStr(s));
}

void CocoaEncoder::encodeTerm(const Node& t)
{
  Assert(d_stage == Stage::Encode);

  // for all un-encoded descendents:
  for (const auto& node :
       NodeDfsIterable(t, VisitOrder::POSTORDER, [this](TNode nn) {
         return d_cache.count(nn);
       }))
  {
    // a rule must put the encoding here
    Poly elem;
    if (isFfFact(node, size()) || isFfTerm(node, size()))
    {
      Trace("ff::cocoa::enc") << "Encode " << node;
      // ff leaf
      if (isFfLeaf(node, size()) && !node.isConst())
      {
        elem = symPoly(d_varSyms.at(node));
      }
      // ff.add
      else if (node.getKind() == Kind::FINITE_FIELD_ADD)
      {
        elem = CoCoA::zero(*d_polyRing);
        for (const auto& c : node)
        {
          elem += d_cache[c];
        }
      }
      // ff.mul
      else if (node.getKind() == Kind::FINITE_FIELD_MULT)
      {
        elem = CoCoA::one(*d_polyRing);
        for (const auto& c : node)
        {
          elem *= d_cache[c];
        }
      }
      // ff.bitsum
      else if (node.getKind() == Kind::FINITE_FIELD_BITSUM)
      {
        Poly sum = CoCoA::zero(*d_polyRing);
        Poly two = CoCoA::one(*d_polyRing) * 2;
        Poly twoPow = CoCoA::one(*d_polyRing);
        for (const auto& c : node)
        {
          sum += twoPow * d_cache[c];
          twoPow *= two;
        }
        elem = symPoly(d_bitsumSyms.at(node));
        d_bitsumPolys.push_back(sum - elem);
      }
      // ff constant
      else if (node.getKind() == Kind::CONST_FINITE_FIELD)
      {
        elem = CoCoA::one(*d_polyRing)
               * intToCocoa(node.getConst<FiniteFieldValue>().getValue());
      }
      // !!
      else
      {
        Unimplemented() << node;
      }
    }
    // cache the encoding
    d_cache.insert({node, elem});
  }
}

void CocoaEncoder::encodeFact(const Node& f)
{
  Assert(d_stage == Stage::Encode);
  Assert(isFfFact(f, size()));
  Poly p;
  // ==
  if (f.getKind() == Kind::EQUAL)
  {
    encodeTerm(f[0]);
    encodeTerm(f[1]);
    p = d_cache.at(f[0]) - d_cache.at(f[1]);
    Node pNode = decode(p);
    if (d_cdp) registerEqualityProof(d_nm, f, pNode, d_cdp);
    d_factToConv.insert({f, d_nm->mkNode(Kind::EQUAL, pNode, zero())});
  }
  // !=
  else
  {
    encodeTerm(f[0][0]);
    encodeTerm(f[0][1]);
    Poly diff = d_cache.at(f[0][0]) - d_cache.at(f[0][1]);
    p = diff * symPoly(d_diseqSyms.at(f)) - 1;
    Node pNode = decode(p);
    Node sk = d_skolemVar.at(f);
    if (d_cdp) registerDisequalityProof(d_nm, f, pNode, sk, d_cdp);
    d_factToConv.insert({f, d_nm->mkNode(Kind::EQUAL, pNode, zero())});
  }
  if (!CoCoA::IsZero(p))
  {
    // normalize; if we don't do it, CoCoA will in GB input, confusing our
    // tracer.
    Poly mul = 1/CoCoA::LC(p);
    p = mul * p;
    d_extraMonic.insert({f, std::pair(decode(mul), decode(p))});
  }
  d_cache.insert({f, p});
  d_polyFacts.insert({extractStr(p), f});
}

Node CocoaEncoder::decode(CoCoA::ConstRefRingElem p)
{
  std::string strRep = extractStr(p);
  // If the term is already registered, we just return it.
  Trace("ff::cocoa::decode") << "Decoding " << strRep << std::endl;
  if (d_symNodes.count(strRep)) return d_symNodes.at(strRep);
  auto baseRing = CoCoA::owner(p);
  if (CoCoA::IsFiniteField(baseRing))
      return FieldObj::mkConst(cocoaFfToFfVal(p));
  std::vector<Node> monomials;
  std::vector<CoCoA::RingElem> indets = CoCoA::indets(CoCoA::owner(p));
  size_t indetsNum = indets.size();
  for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(p); !CoCoA::IsEnded(it);
       ++it)
  {
    auto pp = CoCoA::PP(it);
    std::vector<Node> terms{};
    terms.push_back(FieldObj::mkConst(cocoaFfToFfVal(CoCoA::coeff(it))));
    // Start by representing the coefficient as a constant term.
    // Find all indets in this pp and their exponent.
    for (size_t idx = 0; idx < indetsNum; ++idx)
    {
      auto exponent = CoCoA::exponent(pp, idx);
      if (exponent != 0)
      {
        Node indetSymbol;
        if (d_symNodes.count(extractStr(indets[idx])))
          indetSymbol = d_symNodes.at(extractStr(indets[idx]));
        else
        {
          Assert(d_diseqNodes.count(extractStr(indets[idx])));
          indetSymbol = d_diseqNodes.at(extractStr(indets[idx]));
        }
        terms.insert(terms.end(), exponent, indetSymbol);
      }
    }
    Node ppRepr;
    if (terms[0] == FieldObj::one() && terms.size() > 1)
      ppRepr = mkMul(std::vector<Node>(terms.begin() + 1, terms.end()));
    else
      ppRepr = mkMul(terms);
    monomials.push_back(ppRepr);
  }
  Node result = mkAdd(monomials);
  Trace("ff::cocoa::decode") << "\tResult: " << "p" << std::endl;
  return mkAdd(monomials);
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
