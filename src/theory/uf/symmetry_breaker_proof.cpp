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

#include "theory/uf/symmetry_breaker_proof.h"

#include <limits>

#include "expr/aci_norm.h"
#include "proof/method_id.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

namespace {

std::vector<Node> litsOf(const Node& clause)
{
  if (clause.getKind() == Kind::OR)
  {
    return std::vector<Node>(clause.begin(), clause.end());
  }
  return {clause};
}

}  // namespace

SymBreakProofBuilder::SymBreakProofBuilder(Env& env) : EnvObj(env) {}

std::shared_ptr<SymBreakLemma> SymBreakProofBuilder::build(
    const Node& lemma,
    const Node& t,
    const std::vector<Node>& p,
    const std::set<Node>& cts,
    const Node& ck,
    const std::vector<Node>& phis,
    const FindImage& findImage)
{
  NodeManager* nm = nodeManager();
  std::shared_ptr<SymBreakLemma> lem = std::make_shared<SymBreakLemma>();
  lem->d_lemma = lemma;
  // the literal (t = c) in rewritten form, for each constant c of p
  std::map<Node, Node> litOf;
  std::unordered_map<Node, Node> constOf;
  for (const Node& c : p)
  {
    if (c != t)
    {
      Node l = rewrite(t.eqNode(c));
      litOf[c] = l;
      constOf[l] = c;
    }
  }
  // only free constants can be swapped by a witness
  if (litOf.find(ck) == litOf.end() || ck.getKind() != Kind::VARIABLE)
  {
    return lem;
  }
  // find the precondition, a formula t in S0 with S0 a subset of p, with the
  // fewest constants outside cts
  Node pre;
  std::vector<Node> preConsts;
  size_t best = std::numeric_limits<size_t>::max();
  for (const Node& a : phis)
  {
    std::vector<Node> s0;
    bool ok = true;
    for (const Node& l : litsOf(rewrite(a)))
    {
      std::unordered_map<Node, Node>::iterator it = constOf.find(l);
      if (it == constOf.end())
      {
        ok = false;
        break;
      }
      s0.push_back(it->second);
    }
    if (!ok)
    {
      continue;
    }
    size_t extra = 0;
    for (const Node& c : s0)
    {
      extra += cts.find(c) == cts.end() ? 1 : 0;
    }
    if (extra < best)
    {
      best = extra;
      pre = a;
      preConsts = s0;
    }
  }
  if (pre.isNull())
  {
    Trace("ufsymm-pf") << "No precondition for " << lemma << std::endl;
    return lem;
  }
  Trace("ufsymm-pf") << "Precondition for " << lemma << " is " << pre
                     << std::endl;
  // the constants removed by the chain, in the order of p
  std::vector<Node> removed;
  for (const Node& c : p)
  {
    if (cts.find(c) == cts.end()
        && std::find(preConsts.begin(), preConsts.end(), c) != preConsts.end())
    {
      removed.push_back(c);
    }
  }
  for (const Node& d : removed)
  {
    if (d.getKind() != Kind::VARIABLE)
    {
      return lem;
    }
  }
  size_t m = removed.size();
  // clauses[i] is D_i; D_m is the lemma, D_{i-1} adds the literal of d_i
  std::vector<Node> clauses(m + 1);
  clauses[m] = lemma;
  for (size_t i = m; i > 0; --i)
  {
    std::vector<Node> lits = litsOf(clauses[i]);
    lits.push_back(litOf[removed[i - 1]]);
    clauses[i - 1] = nm->mkOr(lits);
  }
  SymBreakImplication start;
  if (!proveStart(pre, clauses[0], start))
  {
    Trace("ufsymm-pf") << "Failed to weaken precondition" << std::endl;
    return lem;
  }
  std::unordered_set<Node> phiSet(phis.begin(), phis.end());
  for (size_t i = 1; i <= m; i++)
  {
    SymBreakStep step;
    const Node& d = removed[i - 1];
    if (!buildStep(clauses[i - 1],
                   clauses[i],
                   d,
                   ck,
                   litOf[d],
                   litOf[ck],
                   phis,
                   phiSet,
                   findImage,
                   step))
    {
      Trace("ufsymm-pf") << "Failed to build step " << i << std::endl;
      lem->d_steps.clear();
      return lem;
    }
    lem->d_steps.push_back(step);
  }
  lem->d_start = start;
  return lem;
}

SymBreakImplication SymBreakProofBuilder::mkImplication(
    std::shared_ptr<ProofNode> pf, const std::vector<Node>& concs)
{
  SymBreakImplication imp;
  imp.d_conclusions = concs;
  expr::getFreeAssumptions(pf.get(), imp.d_premises);
  if (imp.d_premises.empty())
  {
    imp.d_proof = pf;
  }
  else
  {
    std::vector<Node> prem = imp.d_premises;
    imp.d_proof = d_env.getProofNodeManager()->mkScope(pf, prem, false);
  }
  return imp;
}

std::vector<Node> SymBreakProofBuilder::negLits(CDProof& cdp,
                                                const Node& clause)
{
  Node nc = clause.notNode();
  if (clause.getKind() != Kind::OR)
  {
    return {nc};
  }
  NodeManager* nm = nodeManager();
  std::vector<Node> res;
  for (size_t j = 0, n = clause.getNumChildren(); j < n; j++)
  {
    Node nl = clause[j].notNode();
    cdp.addStep(
        nl, ProofRule::NOT_OR_ELIM, {nc}, {nm->mkConstInt(Rational(j))});
    res.push_back(nl);
  }
  return res;
}

bool SymBreakProofBuilder::proveStart(const Node& pre,
                                      const Node& start,
                                      SymBreakImplication& imp)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  CDProof cdp(d_env);
  TheoryProofStepBuffer psb(pnm->getChecker());
  // pre is a sub-clause of start, up to rewriting
  Node prer = rewrite(pre);
  if (prer != pre && !psb.applyPredTransform(pre, prer, {}))
  {
    return false;
  }
  std::vector<Node> nl = negLits(cdp, start);
  Node ff = nodeManager()->mkConst(false);
  if (!psb.applyPredTransform(prer, ff, nl, MethodId::SB_LITERAL))
  {
    return false;
  }
  cdp.addSteps(psb);
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(ff);
  std::vector<Node> scope{start.notNode()};
  pf = pnm->mkScope(pf, scope, false);
  pf = pnm->mkNode(ProofRule::NOT_NOT_ELIM, {pf}, {});
  imp = mkImplication(pf, {start});
  return true;
}

bool SymBreakProofBuilder::buildStep(const Node& prev,
                                     const Node& cur,
                                     const Node& d,
                                     const Node& c,
                                     const Node& litD,
                                     const Node& litC,
                                     const std::vector<Node>& phis,
                                     const std::unordered_set<Node>& phiSet,
                                     const FindImage& findImage,
                                     SymBreakStep& step)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  step.d_d = d;
  step.d_c = c;
  step.d_prevClause = prev;
  step.d_clause = cur;
  std::vector<Node> vars{d, c};
  std::vector<Node> subs{c, d};
  CDProof cdp(d_env);
  std::vector<Node> concs;
  // images of the formulas moved by the swap
  std::unordered_set<Node> seen;
  for (const Node& a : phis)
  {
    if (!seen.insert(a).second)
    {
      continue;
    }
    Node as = a.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    if (as == a)
    {
      continue;
    }
    Node src = phiSet.find(as) != phiSet.end() ? as : findImage(as);
    if (src.isNull() || (src != as && !proveNormEquiv(cdp, src, as)))
    {
      Trace("ufsymm-pf") << "No image for " << a << std::endl;
      continue;
    }
    step.d_sources.push_back(a);
    concs.push_back(as);
  }
  // the image of cur: from prev and ~cur we get t = d, the image of t = c
  TheoryProofStepBuffer psb(pnm->getChecker());
  std::vector<Node> nl = negLits(cdp, cur);
  if (!psb.applyPredTransform(prev, litD, nl, MethodId::SB_LITERAL))
  {
    return false;
  }
  Node litCs =
      litC.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  if (litCs != litD && !psb.applyPredTransform(litD, litCs, {}))
  {
    return false;
  }
  Node curs =
      cur.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  if (curs != litCs && !psb.applyPredIntro(curs, {litCs}, MethodId::SB_LITERAL))
  {
    return false;
  }
  cdp.addSteps(psb);
  step.d_sources.push_back(cur);
  concs.push_back(curs);
  Node conj = nodeManager()->mkAnd(concs);
  if (concs.size() > 1)
  {
    cdp.addStep(conj, ProofRule::AND_INTRO, concs, {});
  }
  step.d_obligation = mkImplication(cdp.getProofFor(conj), concs);
  return true;
}

bool SymBreakProofBuilder::proveNormEquiv(CDProof& cdp,
                                          const Node& src,
                                          const Node& tgt)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  CDProof tmp(d_env);
  TheoryProofStepBuffer psb(pnm->getChecker());
  if (!psb.applyPredTransform(src, tgt, {}))
  {
    // equal modulo rewriting and ACI normalization
    Node rs = rewrite(src);
    Node rt = rewrite(tgt);
    if (rs != src && !psb.applyPredTransform(src, rs, {}))
    {
      return false;
    }
    Node eq = rs.eqNode(rt);
    if (expr::isACINorm(rs, rt))
    {
      tmp.addStep(eq, ProofRule::ACI_NORM, {}, {eq});
    }
    else if (!expr::proveEqualityWithRewriteSteps(d_env, tmp, rs, rt))
    {
      return false;
    }
    psb.addStep(ProofRule::EQ_RESOLVE, {rs, eq}, {}, rt);
    if (rt != tgt && !psb.applyPredTransform(rt, tgt, {}))
    {
      return false;
    }
  }
  tmp.addSteps(psb);
  cdp.addProof(tmp.getProofFor(tgt));
  return true;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
