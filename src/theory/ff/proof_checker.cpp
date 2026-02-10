#include "theory/ff/proof_checker.h"

#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/theory_arith.h"
namespace cvc5::internal {
namespace theory {
namespace ff {

FfProofRuleChecker::FfProofRuleChecker(NodeManager* nm) : ProofRuleChecker(nm)
{
}
void FfProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::FF_POLY_NORM, this);
  pc->registerChecker(ProofRule::FF_POLY_NORM_EQ, this);
}

Node FfProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == ProofRule::FF_POLY_NORM)
  {
    // return args[0];
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL
        || !args[0][0].getType().isFiniteField())
    {
      return Node::null();
    }
    if (!arith::PolyNorm::isArithPolyNorm(args[0][0], args[0][1]))
    {
      Assert(false) << "args do not normalize to the same term";
      return Node::null();
    }
    return args[0];
  }
  if (id == ProofRule::FF_POLY_NORM_EQ)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Kind k = args[0][0].getKind();
    if (k != Kind::EQUAL)
    {
      return Node::null();
    }
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Node l = children[0][0];
    Node r = children[0][1];
    if (l.getKind() != Kind::FINITE_FIELD_MULT
        || r.getKind() != Kind::FINITE_FIELD_MULT)
    {
      return Node::null();
    }
    Node cx = l[0];
    Node lr = l[1];
    Node cy = r[0];
    Node rr = r[1];
    if (lr.getKind() != Kind::FINITE_FIELD_ADD
        || rr.getKind() != Kind::FINITE_FIELD_ADD)
    {
      return Node::null();
    }
    if (cx.getKind() != Kind::CONST_FINITE_FIELD
        && cy.getKind() != Kind::CONST_FINITE_FIELD)
    {
      return Node::null();
    }
    Node x1 = lr[0];
    Node x2 = lr[1][0];
    Node y1 = rr[0];
    Node y2 = rr[1][0];
    NodeManager* nm = nodeManager();
    Node ret = nm->mkNode(k, x1, x2).eqNode(nm->mkNode(k, y1, y2));
    if (ret != args[0])
    {
      Assert(false) << "res ne args[0]" << ret << " " << args[0] << std::endl;
      return Node::null();
    }
    return ret;
  }
  return Node::null();
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
