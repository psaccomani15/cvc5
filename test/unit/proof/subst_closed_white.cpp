/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box tests for the SUBST_CLOSED proof rule.
 */

#include <memory>
#include <vector>

#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "test_smt.h"

namespace cvc5::internal {
namespace test {

class TestProofWhiteSubstClosed : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-proofs", "true");
    d_slvEngine->finishInit();
    NodeManager* nm = d_nodeManager.get();
    d_u = nm->mkSort("U");
    d_c = nm->mkVar("c", d_u);
    d_d = nm->mkVar("d", d_u);
    d_p = nm->mkVar("P", nm->mkFunctionType(d_u, nm->booleanType()));
    d_pc = nm->mkNode(Kind::APPLY_UF, d_p, d_c);
    d_pd = nm->mkNode(Kind::APPLY_UF, d_p, d_d);
  }
  ProofNodeManager* pnm()
  {
    return d_slvEngine->getEnv().getProofNodeManager();
  }
  std::vector<Node> mkArgs(const std::vector<Node>& vs,
                           const std::vector<Node>& ss)
  {
    NodeManager* nm = d_nodeManager.get();
    return {nm->mkNode(Kind::SEXPR, vs), nm->mkNode(Kind::SEXPR, ss)};
  }
  TypeNode d_u;
  Node d_c;
  Node d_d;
  Node d_p;
  Node d_pc;
  Node d_pd;
};

TEST_F(TestProofWhiteSubstClosed, checker)
{
  ProofChecker* pc = pnm()->getChecker();
  NodeManager* nm = d_nodeManager.get();
  Node imp = nm->mkNode(Kind::IMPLIES, d_pc, d_pc);
  Node res = pc->checkDebug(
      ProofRule::SUBST_CLOSED, {imp}, mkArgs({d_c}, {d_d}), Node::null(), "");
  ASSERT_EQ(res, nm->mkNode(Kind::IMPLIES, d_pd, d_pd));
  // simultaneous swap
  Node eq = d_c.eqNode(d_d);
  res = pc->checkDebug(ProofRule::SUBST_CLOSED,
                       {eq},
                       mkArgs({d_c, d_d}, {d_d, d_c}),
                       Node::null(),
                       "");
  ASSERT_EQ(res, d_d.eqNode(d_c));
  // malformed: arity mismatch, non-constant, type mismatch, duplicate
  std::vector<Node> vars;
  std::vector<Node> subs;
  ASSERT_FALSE(expr::getSubstClosedArgs(mkArgs({d_c, d_d}, {d_d}), vars, subs));
  ASSERT_FALSE(expr::getSubstClosedArgs(mkArgs({d_pc}, {d_pd}), vars, subs));
  Node x = nm->mkVar("x", nm->integerType());
  ASSERT_FALSE(expr::getSubstClosedArgs(mkArgs({d_c}, {x}), vars, subs));
  ASSERT_FALSE(
      expr::getSubstClosedArgs(mkArgs({d_c, d_c}, {d_d, d_d}), vars, subs));
}

TEST_F(TestProofWhiteSubstClosed, closed)
{
  // SCOPE(ASSUME(P c)) proves (=> (P c) (P c)), closed w.r.t. c
  std::shared_ptr<ProofNode> a = pnm()->mkAssume(d_pc);
  std::vector<Node> assumps{d_pc};
  std::shared_ptr<ProofNode> s = pnm()->mkScope(a, assumps);
  std::shared_ptr<ProofNode> sc = pnm()->mkSubstClosed(s, {d_c}, {d_d});
  NodeManager* nm = d_nodeManager.get();
  ASSERT_EQ(sc->getResult(), nm->mkNode(Kind::IMPLIES, d_pd, d_pd));
  ASSERT_TRUE(sc->isClosed());
}

TEST_F(TestProofWhiteSubstClosed, notClosed)
{
  // ASSUME(P c) is open and mentions c
  std::shared_ptr<ProofNode> a = pnm()->mkAssume(d_pc);
  ASSERT_DEATH(pnm()->mkSubstClosed(a, {d_c}, {d_d}), "substituted constant");
  // the traversal rejects it too, even when built without the guard
  std::shared_ptr<ProofNode> bad =
      pnm()->mkNode(ProofRule::SUBST_CLOSED, {a}, mkArgs({d_c}, {d_d}));
  std::vector<Node> fa;
  ASSERT_DEATH(expr::getFreeAssumptions(bad.get(), fa), "substituted constant");
  // open assumptions not mentioning the constants are allowed
  std::shared_ptr<ProofNode> b = pnm()->mkAssume(d_pd);
  std::shared_ptr<ProofNode> ok = pnm()->mkSubstClosed(b, {d_c}, {d_d});
  expr::getFreeAssumptions(ok.get(), fa);
  ASSERT_EQ(fa, std::vector<Node>{d_pd});
}

}  // namespace test
}  // namespace cvc5::internal
