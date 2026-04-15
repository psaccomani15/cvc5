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
  pc->registerChecker(ProofRule::FF_POLY_CONVERSION, this);
  pc->registerChecker(ProofRule::FF_ONE_UNSAT, this);
  pc->registerChecker(ProofRule::FF_POLY_NORM, this);
  pc->registerChecker(ProofRule::FF_POLY_NORM_EQ, this);
  pc->registerChecker(ProofRule::MACRO_FF_POLY_COMBINATION, this);
  pc->registerChecker(ProofRule::FF_POLY_COMBINATION, this);
  pc->registerChecker(ProofRule::FF_DISEQ, this);
}

Node FfProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  // Todo: Add a proper checker and change arguments.
  if (id == ProofRule::FF_DISEQ)
  {
    Assert(args.size() == 3);
    Node l = args[0];
    Node r = args[1];
    Node sk = args[2];
    const Integer size = l.getType().getFfSize();
    Node sub = nodeManager()->mkNode(
        Kind::FINITE_FIELD_ADD, l, nodeManager()->mkNode(Kind::FINITE_FIELD_NEG, r));
    Node minusOne = nodeManager()->mkConst(FiniteFieldValue(-1, size));
    Node zero = nodeManager()->mkConst(FiniteFieldValue(0, size));
    Node n = nodeManager()->mkNode(Kind::FINITE_FIELD_ADD,
                        nodeManager()->mkNode(Kind::FINITE_FIELD_MULT, sub, sk),
                        minusOne);
    Node nEq = nodeManager()->mkNode(Kind::EQUAL, n, zero);
    Node lrEq = nodeManager()->mkNode(Kind::NOT,
                                      nodeManager()->mkNode(Kind::EQUAL, l, r));
    return nodeManager()->mkNode(Kind::EQUAL, lrEq, nEq);
  }
  if (id == ProofRule::FF_EXHAUST_BRANCH)
  {
    Assert(args.size() == 2);
    Assert(children.size() == 1);
    std::vector<Node> generators;
    Node ideal = args[1];
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    for (const auto gen : ideal) generators.push_back(gen);
    std::vector<Node> disjuncts;
    TypeNode field = generators[0].getType();
    Assert(field.isFiniteField());
    Integer maxValue = field.getFfSize();
    FfSize fieldCard(maxValue);

    for (Integer it = 0; it < maxValue; it += 1)
      for (const auto& var : args[0])
      {
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
          disjuncts.push_back(varietyIsEmpty(nodeManager(), newIdeal).negate());
          generators.pop_back();
        }
      }
    return nodeManager()->mkOr(disjuncts);
  }
  if (id == ProofRule::FF_ROOT_BRANCH)
  {
    Assert(args.size() == 6);
    Assert(children.size() == 2);
    Node ideal = args[1];
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    std::vector<Node> generators;
    for (const auto gen : ideal) generators.push_back(gen);
    std::vector<Node> disjuncts;
    Node branchVariable = args[2];
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

    for (const auto& root : args[3])
    {
      const FiniteFieldValue rootValue = root.getConst<FiniteFieldValue>();
      Node branchValue = nodeManager()->mkConst(-rootValue);
      generators.push_back(nodeManager()->mkNode(
          Kind::FINITE_FIELD_ADD, branchVariable, branchValue));
      Node newIdeal =
          nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, generators);
      disjuncts.push_back(varietyIsEmpty(nodeManager(), newIdeal).negate());
      generators.pop_back();
    }
    return nodeManager()->mkOr(disjuncts);
  }
  if (id == ProofRule::FF_POLY_COMBINATION)
  {
    Assert(!children.empty());
    Assert(args.size() == 3);
    Assert(args[0].getNumChildren() == args[1].getNumChildren());
    Node res = args[2];
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Node ideal = children[0][1];
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    return nodeManager()->mkNode(Kind::SET_MEMBER, res, ideal);
  }
  if (id == ProofRule::MACRO_FF_POLY_COMBINATION)
  {
    Assert(!children.empty());
    Assert(args.size() == 3);
    Assert(args[0].getNumChildren() == args[1].getNumChildren());
    Node res = args[2];
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Node ideal = children[0][1];
    Assert(ideal.getKind() == Kind::FINITE_FIELD_IDEAL);
    return nodeManager()->mkNode(Kind::SET_MEMBER, res, ideal);
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
  if (id == ProofRule::FF_POLY_CONVERSION)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 2);
    return args[1];
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
    return varietyIsEmpty(nodeManager(), newIdeal).negate();
  }
  if (id == ProofRule::FF_ONE_UNSAT)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Assert(children[0].getKind() == Kind::SET_MEMBER);
    Assert(children[0][1].getKind() == Kind::FINITE_FIELD_IDEAL)
        << children[0][1].getKind();
    return varietyIsEmpty(nodeManager(), children[0][1]);
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
