#include "theory/ff/proof_checker.h"

#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/theory_arith.h"
#include "theory/ff/proof_utils.h"
namespace cvc5::internal {
namespace theory {
namespace ff {

FfProofRuleChecker::FfProofRuleChecker(NodeManager* nm) : ProofRuleChecker(nm)
{
}
void FfProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::FF_EXHAUST_BRANCH, this);
  pc->registerChecker(ProofRule::FF_ROOT_BRANCH, this);
  pc->registerChecker(ProofRule::FF_FIELD_POLYS, this);
  pc->registerChecker(ProofRule::FF_IDEAL_GENERATOR, this);
  pc->registerChecker(ProofRule::FF_IDEAL_ZERO, this);
  pc->registerChecker(ProofRule::FF_IDEAL_MONIC, this);
  pc->registerChecker(ProofRule::FF_IDEAL_REDUCE_ZERO, this);
  pc->registerChecker(ProofRule::FF_IDEAL_REDUCE, this);
  pc->registerChecker(ProofRule::FF_IDEAL_SPOLY, this);
  pc->registerChecker(ProofRule::FF_POLY_CONVERSION, this);
  pc->registerChecker(ProofRule::FF_ONE_UNSAT, this);
  pc->registerChecker(ProofRule::FF_POLY_NORM, this);
  pc->registerChecker(ProofRule::FF_POLY_NORM_EQ, this);
}

Node FfProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == ProofRule::FF_EXHAUST_BRANCH)
  {
    Assert(args.size() >= 1);
    Assert(children.size() >= 2);
    std::vector<Node> generators;
    for (size_t it = 1; it < children.size(); ++it)
    {
      Assert(children[it].getKind() == Kind::SET_MEMBER);
      generators.push_back(children[it][0]);
    }
    std::vector<Node> disjuncts;
    TypeNode field = generators[0].getType();
    Assert(field.isFiniteField());
    Integer maxValue = field.getFfSize();
    FfSize fieldCard(maxValue);
    for (const auto& var : args[0])
    {
      for (Integer it = 0; it < maxValue; it += 1)
      {
        Node assignmentPoly = var;
        if (it > 0)
          assignmentPoly =
              nodeManager()->mkNode(Kind::FINITE_FIELD_ADD,
                                    var,
                                    nodeManager()->mkConst(FiniteFieldValue(
                                        maxValue - it, fieldCard)));
        generators.push_back(assignmentPoly);
        Node newIdeal =
            nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, generators);
        disjuncts.push_back(emptyVarPred(nodeManager(), newIdeal).negate());
      }
    }
    return nodeManager()->mkOr(disjuncts);
  }
  if (id == ProofRule::FF_ROOT_BRANCH)
  {
    Assert(args.size() >= 1);
    Assert(children.size() >= 2);
    std::vector<Node> generators;
    for (size_t it = 1; it < children.size() - 1; ++it)
    {
      Assert(children[it].getKind() == Kind::SET_MEMBER);
      generators.push_back(children[it][0]);
    }
    std::vector<Node> disjuncts;
    TypeNode field = generators[0].getType();
    Assert(field.isFiniteField());
    Integer maxValue = field.getFfSize();
    FfSize fieldCard(maxValue);
    Node branchVariable = args[1];
    bool isNonAssigned = true;
    for (const auto& nonAssigned : args[0])
    {
      if (nonAssigned == branchVariable)
      {
        isNonAssigned = false;
        break;
      }
    }
    Assert(!isNonAssigned);
    if (isNonAssigned) return Node::null();
    for (const auto& root : args[2])
    {
      Integer rootValue = root.getConst<FiniteFieldValue>().getValue();
      Node branchValue = nodeManager()->mkConst(
          FiniteFieldValue(maxValue - rootValue, fieldCard));
      generators.push_back(nodeManager()->mkNode(
          Kind::FINITE_FIELD_ADD, branchVariable, branchValue));
      Node newIdeal =
          nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, generators);
      disjuncts.push_back(emptyVarPred(nodeManager(), newIdeal).negate());
      generators.pop_back();
    }
    return nodeManager()->mkOr(disjuncts);
  }
  if (id == ProofRule::FF_IDEAL_GENERATOR)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Assert(args[1].getKind() == Kind::FINITE_FIELD_IDEAL);
    for (const auto& poly : args[1])
    {
      if (args[0] == poly)
        return d_nm->mkNode(Kind::SET_MEMBER, args[0], args[1]);
    }
  }
  if (id == ProofRule::FF_IDEAL_ZERO)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Assert(args[1].getKind() == Kind::FINITE_FIELD_IDEAL);
    return d_nm->mkNode(Kind::SET_MEMBER, args[0], args[1]);
  }
  if (id == ProofRule::FF_IDEAL_SPOLY)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 3);
    // Both children are proofs of membership to the *same* ideal
    Assert(children[0].getKind() == children[1].getKind()
           && children[0].getKind() == Kind::SET_MEMBER);
    Assert(children[0][1] == children[1][1]);
    Node ideal = children[0][1];
    return d_nm->mkNode(Kind::SET_MEMBER, args[0], children[0][1]);
  }
  if (id == ProofRule::FF_IDEAL_REDUCE || id == ProofRule::FF_IDEAL_REDUCE_ZERO)
  {
    Assert(args.size() == 3);
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Node ideal = children[0][1];
    // All children must be proofs of membership for the *same* ideal
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    for (const auto& child : children)
    {
      Assert(child.getKind() == Kind::SET_MEMBER);
      Assert(ideal == child[1]);
      if (ideal != child[1] || child.getKind() != Kind::SET_MEMBER)
        return Node::null();
    }
    return d_nm->mkNode(Kind::SET_MEMBER, args[0], ideal);
  }
  if (id == ProofRule::FF_IDEAL_MONIC)
  {
    Assert(args.size() == 1);
    Assert(children.size() == 1);
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Node ideal = children[0][1];
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    return d_nm->mkNode(Kind::SET_MEMBER, args[0], ideal);
  }
  if (id == ProofRule::FF_POLY_CONVERSION)
  {
    Assert(children.size() == 0);
    Assert(args.size() == 2) << args.size();
    return d_nm->mkNode(Kind::EQUAL, args[0], args[1]);
  }
  if (id == ProofRule::FF_FIELD_POLYS)
  {
    Assert(children.size() == 1);
    Assert(args.size() >= 1);
    Assert(children[0].getKind() == Kind::NOT
           && children[0][0].getKind() == Kind::SET_IS_EMPTY);
    Assert(children[0][0][0].getKind() == Kind::FINITE_FIELD_VARIETY);
    Node ideal = children[0][0][0][0];
    std::vector<Node> gens(ideal.begin(), ideal.end());
    gens.insert(gens.end(), args.begin(), args.end());
    Node newIdeal = d_nm->mkNode(Kind::FINITE_FIELD_IDEAL, gens);
    return emptyVarPred(nodeManager(), newIdeal).negate();
  }
  if (id == ProofRule::FF_ONE_UNSAT)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Assert(children[0][1].getKind() == Kind::FINITE_FIELD_IDEAL)
        << children[0][1].getKind();
    return emptyVarPred(nodeManager(), children[0][1]);
  }
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
