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

#include "smt/sym_break_proof_assembler.h"

#include <unordered_set>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/uf_options.h"
#include "proof/method_id.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace smt {

SymBreakProofAssembler::Statistics::Statistics(StatisticsRegistry& sr)
    : d_lemmas(sr.registerInt("SymBreakProof::lemmas")),
      d_lemmasTrusted(sr.registerInt("SymBreakProof::lemmasTrusted")),
      d_steps(sr.registerInt("SymBreakProof::steps")),
      d_obligationsTrusted(sr.registerInt("SymBreakProof::obligationsTrusted")),
      d_replayTrusted(sr.registerInt("SymBreakProof::replayStepsTrusted"))
{
}

SymBreakProofAssembler::SymBreakProofAssembler(Env& env,
                                               const SymBreakLemmaRegistry& reg)
    : EnvObj(env), d_reg(reg), d_stats(statisticsRegistry())
{
}

bool SymBreakProofAssembler::process(PfPtr pfn)
{
  const context::CDList<std::shared_ptr<SymBreakLemma>>& lems = d_reg.get();
  std::vector<Node> fa = getFreeAssumptions(pfn);
  std::unordered_set<Node> faSet(fa.begin(), fa.end());
  bool any = false;
  for (const std::shared_ptr<SymBreakLemma>& lem : lems)
  {
    if (faSet.find(lem->d_lemma) != faSet.end())
    {
      any = true;
      break;
    }
  }
  if (!any)
  {
    return false;
  }
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  // A shallow copy of the root, so that the root can be updated in place to
  // a proof containing the original one.
  PfPtr r = pnm->mkNode(pfn->getRule(),
                        pfn->getChildren(),
                        pfn->getArguments(),
                        pfn->getResult());
  // discharge in reverse order of emission
  for (size_t k = lems.size(); k > 0; --k)
  {
    const SymBreakLemma& lem = *lems[k - 1];
    fa = getFreeAssumptions(r);
    if (std::find(fa.begin(), fa.end(), lem.d_lemma) == fa.end())
    {
      continue;
    }
    Trace("sb-proof") << "Discharge " << lem.d_lemma << std::endl;
    ++d_stats.d_lemmas;
    r = discharge(r, lem);
  }
  pnm->updateNode(pfn.get(), r.get());
  return true;
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::discharge(
    PfPtr r, const SymBreakLemma& lem)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  bool trusted = lem.d_start.d_proof == nullptr;
  if (!trusted && !lem.d_steps.empty())
  {
    std::vector<Node> cs{lem.d_steps[0].d_c};
    std::vector<PfPtr> pfs{r, lem.d_start.d_proof};
    for (const SymBreakStep& step : lem.d_steps)
    {
      cs.push_back(step.d_d);
      pfs.push_back(step.d_obligation.d_proof);
    }
    trusted = hasDependentSkolem(pfs, cs);
  }
  if (trusted)
  {
    ++d_stats.d_lemmasTrusted;
    PfPtr pf =
        pnm->mkTrustedNode(TrustId::SYMM_BREAK_OBLIGATION, {}, {}, lem.d_lemma);
    return dischargeWith(r, lem.d_lemma, pf);
  }
  PfPtr startPf = instantiate(lem.d_start, {})[0];
  if (lem.d_steps.empty())
  {
    return dischargeWith(r, lem.d_lemma, startPf);
  }
  bool ite = options().uf.ufSymmetryBreakerProofMode
             == options::SymmetryBreakerProofMode::ITE;
  for (size_t i = lem.d_steps.size(); i > 0; --i)
  {
    const SymBreakStep& step = lem.d_steps[i - 1];
    ++d_stats.d_steps;
    PfPtr prevPf = i == 1 ? startPf : nullptr;
    r = ite ? stepIte(r, step, prevPf) : stepSubst(r, step, prevPf);
  }
  return r;
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::dischargeWith(
    PfPtr r, const Node& fact, PfPtr pf)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  // (not fact), then false by contradiction
  PfPtr nf = pnm->mkNode(ProofRule::SCOPE, {r}, {fact});
  return pnm->mkNode(ProofRule::CONTRA, {pf, nf}, {});
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::stepSubst(
    PfPtr r, const SymBreakStep& step, PfPtr prevPf)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  const Node& cur = step.d_clause;
  std::vector<Node> vars{step.d_d, step.d_c};
  std::vector<Node> subs{step.d_c, step.d_d};
  // r with all its free assumptions discharged, and its image
  std::vector<Node> fa = getFreeAssumptions(r);
  PfPtr t = pnm->mkNode(ProofRule::SCOPE, {r}, fa);
  PfPtr s = pnm->mkSubstClosed(t, vars, subs);
  // refute the images of fa, assuming (not cur)
  Node ncur = cur.notNode();
  std::map<Node, PfPtr> images = getImages(step, pnm->mkAssume(ncur), prevPf);
  std::vector<PfPtr> imgs;
  for (const Node& w : fa)
  {
    Node ws = w.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    imgs.push_back(ws == w ? pnm->mkAssume(w) : getImage(images, w, ws));
  }
  PfPtr q = pnm->mkNode(ProofRule::CONTRA, {mkAndIntro(imgs), s}, {});
  // cur by contradiction
  PfPtr pd = pnm->mkNode(ProofRule::SCOPE, {q}, {ncur});
  pd = pnm->mkNode(ProofRule::NOT_NOT_ELIM, {pd}, {});
  // refute the original assumptions, proving cur
  std::vector<PfPtr> orig;
  for (const Node& w : fa)
  {
    orig.push_back(w == cur ? pd : pnm->mkAssume(w));
  }
  return pnm->mkNode(ProofRule::CONTRA, {mkAndIntro(orig), t}, {});
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::stepIte(
    PfPtr r, const SymBreakStep& step, PfPtr prevPf)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  NodeManager* nm = nodeManager();
  const Node& cond = step.d_clause;
  const Node& d = step.d_d;
  const Node& c = step.d_c;
  // witness: keep the constants if cond holds, swap them otherwise
  Node ited = nm->mkNode(Kind::ITE, cond, d, c);
  Node itec = nm->mkNode(Kind::ITE, cond, c, d);
  std::vector<Node> vars{d, c};
  std::vector<Node> wsubs{ited, itec};
  std::vector<Node> ssubs{c, d};
  size_t ntrusted = 0;
  PfPtr rp = expr::substituteProofNode(pnm, r, vars, wsubs, ntrusted);
  d_stats.d_replayTrusted += ntrusted;
  std::vector<Node> fa = getFreeAssumptions(r);
  std::vector<Node> fap;
  for (const Node& w : fa)
  {
    fap.push_back(
        w.substitute(vars.begin(), vars.end(), wsubs.begin(), wsubs.end()));
  }
  PfPtr tp = pnm->mkNode(ProofRule::SCOPE, {rp}, fap);
  // the witness terms evaluated in each case
  Node sbf = mkMethodId(nm, MethodId::SB_FORMULA);
  Node sbl = mkMethodId(nm, MethodId::SB_LITERAL);
  Node ncond = cond.notNode();
  PfPtr acond = pnm->mkAssume(cond);
  PfPtr ancond = pnm->mkAssume(ncond);
  std::vector<PfPtr> posEqs;
  std::vector<PfPtr> negEqs;
  for (size_t j = 0; j < 2; j++)
  {
    const Node& ite = j == 0 ? ited : itec;
    Node peq = ite.eqNode(j == 0 ? d : c);
    Node neq = ite.eqNode(j == 0 ? c : d);
    posEqs.push_back(mkCheckedStep(
        ProofRule::MACRO_SR_PRED_INTRO, {acond}, {peq, sbf}, peq));
    negEqs.push_back(mkCheckedStep(
        ProofRule::MACRO_SR_PRED_INTRO, {ancond}, {neq, sbl}, neq));
  }
  std::map<Node, PfPtr> images = getImages(step, ancond, prevPf);
  std::vector<PfPtr> pfs;
  for (size_t j = 0, n = fa.size(); j < n; j++)
  {
    const Node& w = fa[j];
    const Node& wp = fap[j];
    if (wp == w)
    {
      pfs.push_back(pnm->mkAssume(w));
      continue;
    }
    // if cond holds, wp is w
    std::vector<PfPtr> pc{w == cond ? acond : pnm->mkAssume(w)};
    pc.insert(pc.end(), posEqs.begin(), posEqs.end());
    PfPtr pos = mkCheckedStep(ProofRule::MACRO_SR_PRED_TRANSFORM, pc, {wp}, wp);
    // otherwise, wp is the image of w
    Node ws =
        w.substitute(vars.begin(), vars.end(), ssubs.begin(), ssubs.end());
    std::vector<PfPtr> nc{getImage(images, w, ws)};
    nc.insert(nc.end(), negEqs.begin(), negEqs.end());
    PfPtr neg = mkCheckedStep(ProofRule::MACRO_SR_PRED_TRANSFORM, nc, {wp}, wp);
    pfs.push_back(proveByCases(cond, pos, neg, wp));
  }
  return pnm->mkNode(ProofRule::CONTRA, {mkAndIntro(pfs), tp}, {});
}

std::map<Node, SymBreakProofAssembler::PfPtr> SymBreakProofAssembler::getImages(
    const SymBreakStep& step, PfPtr notClause, PfPtr prevPf)
{
  std::map<Node, PfPtr> given;
  given[step.d_clause.notNode()] = notClause;
  if (prevPf != nullptr)
  {
    given[step.d_prevClause] = prevPf;
  }
  std::vector<PfPtr> concs = instantiate(step.d_obligation, given);
  std::map<Node, PfPtr> images;
  for (size_t j = 0, n = concs.size(); j < n; j++)
  {
    images[step.d_sources[j]] = concs[j];
  }
  return images;
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::getImage(
    const std::map<Node, PfPtr>& images, const Node& w, const Node& ws)
{
  std::map<Node, PfPtr>::const_iterator it = images.find(w);
  if (it != images.end())
  {
    return it->second;
  }
  Trace("sb-proof") << "No image for " << w << std::endl;
  ++d_stats.d_obligationsTrusted;
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  return pnm->mkTrustedNode(
      TrustId::SYMM_BREAK_OBLIGATION, {pnm->mkAssume(w)}, {}, ws);
}

std::vector<SymBreakProofAssembler::PfPtr> SymBreakProofAssembler::instantiate(
    const SymBreakImplication& imp, const std::map<Node, PfPtr>& given)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  PfPtr conj = imp.d_proof;
  if (!imp.d_premises.empty())
  {
    std::vector<PfPtr> prems;
    for (const Node& p : imp.d_premises)
    {
      std::map<Node, PfPtr>::const_iterator it = given.find(p);
      prems.push_back(it != given.end() ? it->second : pnm->mkAssume(p));
    }
    conj = pnm->mkNode(
        ProofRule::MODUS_PONENS, {mkAndIntro(prems), imp.d_proof}, {});
  }
  std::vector<PfPtr> res;
  size_t n = imp.d_conclusions.size();
  if (n == 1)
  {
    res.push_back(conj);
    return res;
  }
  NodeManager* nm = nodeManager();
  for (size_t j = 0; j < n; j++)
  {
    res.push_back(pnm->mkNode(
        ProofRule::AND_ELIM, {conj}, {nm->mkConstInt(Rational(j))}));
  }
  return res;
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::proveByCases(
    const Node& cond, PfPtr pos, PfPtr neg, const Node& conc)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  Node ncond = cond.notNode();
  Node nconc = conc.notNode();
  // (=> cond conc) and (=> (not cond) conc)
  PfPtr ipos = pnm->mkNode(ProofRule::SCOPE, {pos}, {cond});
  PfPtr ineg = pnm->mkNode(ProofRule::SCOPE, {neg}, {ncond});
  // assuming (not conc), refute cond, then refute (not cond)
  PfPtr anconc = pnm->mkAssume(nconc);
  PfPtr x1 =
      pnm->mkNode(ProofRule::MODUS_PONENS, {pnm->mkAssume(cond), ipos}, {});
  PfPtr f1 = pnm->mkNode(ProofRule::CONTRA, {x1, anconc}, {});
  PfPtr nc = pnm->mkNode(ProofRule::SCOPE, {f1}, {cond});
  PfPtr x2 = pnm->mkNode(ProofRule::MODUS_PONENS, {nc, ineg}, {});
  PfPtr f2 = pnm->mkNode(ProofRule::CONTRA, {x2, anconc}, {});
  PfPtr nnc = pnm->mkNode(ProofRule::SCOPE, {f2}, {nconc});
  return pnm->mkNode(ProofRule::NOT_NOT_ELIM, {nnc}, {});
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::mkAndIntro(
    const std::vector<PfPtr>& pfs)
{
  if (pfs.size() == 1)
  {
    return pfs[0];
  }
  return d_env.getProofNodeManager()->mkNode(ProofRule::AND_INTRO, pfs, {});
}

SymBreakProofAssembler::PfPtr SymBreakProofAssembler::mkCheckedStep(
    ProofRule r,
    const std::vector<PfPtr>& children,
    const std::vector<Node>& args,
    const Node& expected)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  std::vector<Node> cres;
  for (const PfPtr& cp : children)
  {
    cres.push_back(cp->getResult());
  }
  Node res =
      pnm->getChecker()->checkDebug(r, cres, args, Node::null(), "sb-proof");
  if (res == expected)
  {
    return pnm->mkNode(r, children, args, expected);
  }
  Trace("sb-proof") << "Failed to check " << r << " proving " << expected
                    << std::endl;
  ++d_stats.d_obligationsTrusted;
  return pnm->mkTrustedNode(
      TrustId::SYMM_BREAK_OBLIGATION, children, {}, expected);
}

bool SymBreakProofAssembler::hasDependentSkolem(const std::vector<PfPtr>& pfs,
                                                const std::vector<Node>& cs)
{
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visitedTerms;
  std::unordered_set<const ProofNode*> visited;
  std::vector<const ProofNode*> visit;
  for (const PfPtr& pf : pfs)
  {
    visit.push_back(pf.get());
  }
  while (!visit.empty())
  {
    const ProofNode* cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    expr::getSymbols(cur->getResult(), syms, visitedTerms);
    for (const Node& a : cur->getArguments())
    {
      expr::getSymbols(a, syms, visitedTerms);
    }
    for (const PfPtr& c : cur->getChildren())
    {
      visit.push_back(c.get());
    }
  }
  for (const Node& k : syms)
  {
    if (k.getKind() != Kind::SKOLEM)
    {
      continue;
    }
    Node o = SkolemManager::getOriginalForm(k);
    if (o != k && expr::hasSubterm(o, cs))
    {
      Trace("sb-proof") << "Skolem " << k << " depends on " << cs << std::endl;
      return true;
    }
  }
  return false;
}

std::vector<Node> SymBreakProofAssembler::getFreeAssumptions(PfPtr pf)
{
  std::vector<Node> fa;
  expr::getFreeAssumptions(pf.get(), fa);
  return fa;
}

}  // namespace smt
}  // namespace cvc5::internal
