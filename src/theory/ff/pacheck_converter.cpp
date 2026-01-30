#include "theory/ff/pacheck_converter.h"

#include <sstream>
#include <string>

#include "cvc5_private.h"
#include "expr/algorithm/flatten.h"
#include "theory/ff/pacheck_rules.h"
namespace cvc5::internal {

namespace theory {

namespace ff {

PacheckPolynomial::PacheckPolynomial(std::string poly, size_t id, size_t branch)
    : d_polyRepr(poly), d_id(id), d_branch(branch)
{
}

PacheckProofPrinter::PacheckProofPrinter(Env& env,
                                         const FfSize& size,
                                         CDProof& cdp)
    : EnvObj(env), d_size(size), d_maxId(1), d_proof(&cdp)
{
}

std::string convertConst(Node ffConst)
{
  return ffConst.getConst<FiniteFieldValue>().getValue().toString();
}

std::string PacheckProofPrinter::convertVar(Node var)
{
  if (d_varToPacheckVar.count(var)) return d_varToPacheckVar.at(var);
  std::string varName = var.getName();
  d_varToPacheckVar[var] = varName;
  return varName;
}

std::string PacheckProofPrinter::convertPP(Node pp)
{
  pp = expr::algorithm::flatten(nodeManager(), pp, Kind::FINITE_FIELD_MULT);
  if (pp.getKind() == Kind::FINITE_FIELD_MULT)
  {
    std::stringstream ss;
    for (size_t it = 0; it < pp.getNumChildren(); ++it)
    {
      if (it > 0) ss << " * ";
      if (pp[it].getKind() == Kind::CONST_FINITE_FIELD)
      {
        ss << convertConst(pp[it]);
        continue;
      }
      Node currVar = pp[it];
      size_t exp = 1;
      while (it + 1 < pp.getNumChildren() && pp[it + 1] == currVar)
      {
        exp += 1;
        it += 1;
      }
      ss << convertVar(currVar);
      if (exp > 1) ss << "^" << exp;
    }
    return ss.str();
  }
  if (pp.getKind() == Kind::CONST_FINITE_FIELD) return convertConst(pp);
  return convertVar(pp);
}
PacheckPolynomial PacheckProofPrinter::nodeToPoly(Node poly, size_t branch)
{
  Node flattened = expr::algorithm::flatten(nodeManager(), poly, Kind::FINITE_FIELD_ADD);
  if (d_nodeToPacheckPoly.count(flattened))
  {
    auto res = d_nodeToPacheckPoly.at(flattened);
    if (res.getBranch() == 1 || res.getBranch() == branch) return res;
    PacheckPolynomial newRes(res.getRepr(), d_maxId++, branch);
    d_nodeToPacheckPoly.emplace(poly, newRes);
    return newRes;
  }
  std::vector<std::string> summands;
  if (flattened.getKind() == Kind::FINITE_FIELD_ADD)
  {
    std::stringstream ss;
    size_t count = 0;
    for (const auto& child : flattened)
    {
      ss << convertPP(child);
      count += 1;
      if (count < flattened.getNumChildren()) ss << " + ";
    }
    auto result = PacheckPolynomial(ss.str(), d_maxId++, branch);
    d_nodeToPacheckPoly.emplace(flattened, result);
    return result;
  }
  auto result = PacheckPolynomial(convertPP(poly), d_maxId++, branch);
  d_nodeToPacheckPoly.emplace(flattened, result);
  return result;
}

void PacheckProofPrinter::printInternal(std::ostream& out,
                                        std::shared_ptr<ProofNode> pfn,
                                        size_t branchId)
{
  auto children = pfn.get()->getChildren();
  auto rule = pfn.get()->getRule();
  auto args = pfn.get()->getArguments();
  if (rule == ProofRule::CHAIN_RESOLUTION)
  {
    auto branchStep = children[0].get();
    auto branchStepChildren = branchStep->getChildren();
    printInternal(out, branchStepChildren[0], branchId);
    if (branchStep->getRule() == ProofRule::FF_ROOT_BRANCH)
    {
      auto branchPoly = branchStepChildren[branchStepChildren.size() - 1]
                            .get()
                            ->getResult()[0];
      if (!d_nodeToPacheckPoly.count(branchPoly))
        printInternal(
            out, branchStepChildren[branchStepChildren.size() - 1], branchId);
      
      Node branchVar = branchStep->getArguments()[1];
      Node roots = branchStep->getArguments()[2];
      Node branchingPoly = branchStep->getArguments()[3];
      out << nodeToPoly(branchingPoly, branchId).getId() << " " << PacheckRule::Root
          << " " << convertVar(branchVar);
      for (const auto& root : roots)
      {
        out << " " << convertConst(root);
      }
      out << ";";
      out << std::endl;
      size_t branchIt = 1;
      for (int it = roots.getNumChildren() - 1; it >= 0; --it)
      {
        out << PacheckRule::Branch << " " << branchVar << " "
            << convertConst(roots[it]) << std::endl;
        printInternal(out, children[branchIt], branchId + branchIt);
        branchIt += 1;
      }
      return;
    }
    size_t branchIt = 1;
    for (Integer val = 0; val < d_size.d_val; val += 1)
    {
      for (const auto var : args[0])
      {
        out << PacheckRule::Branch << " " << var << " " << val << std::endl;
        printInternal(out, children[branchIt], branchId + branchIt);
        branchIt += 1;
      }
    }
    return;
  }

  if (rule == ProofRule::CONTRA)
  {
    printInternal(out, children[1], branchId);
    printInternal(out, children[0], branchId);
    return;
  }

  for (const auto& child : children)
  {
    printInternal(out, child, branchId);
  }
  switch (rule)
  {
    case ProofRule::FF_POLY_CONVERSION:
    {
      auto ideal = args[1][0][0][0];
      for (const auto& poly : ideal)
      {
        PacheckPolynomial pacheckPoly = nodeToPoly(poly, branchId);
        out << pacheckPoly.getId() << " " << PacheckRule::Axiom << " "
            << pacheckPoly.getRepr() << std::endl;
      }
      break;
    }
    case ProofRule::FF_FIELD_POLYS:
    {
      for (const auto& poly : args)
      {
        PacheckPolynomial pacheckPoly = nodeToPoly(poly, branchId);
        out << pacheckPoly.getId() << " " << PacheckRule::Axiom << " "
            << pacheckPoly.getRepr() << std::endl;
      }
      break;
    }
    case ProofRule::FF_IDEAL_REDUCE:
    {
      auto reductors = args[1];
      auto multipliers = args[2];
      size_t mulIdx = 0;
      auto initial = nodeToPoly(reductors[0], branchId);
      auto result = nodeToPoly(pfn.get()->getResult()[0], branchId);
      out << result.getId() << " " << PacheckRule::LinComp << " "
          << initial.getId() << "* (1)";
      for (size_t it = 1; it < reductors.getNumChildren(); ++it)
      {
        auto reductor = nodeToPoly(reductors[it], branchId);
        auto multiplier = nodeToPoly(multipliers[mulIdx], branchId);
        out << " + " << reductor.getId() << " * (" << multiplier.getRepr()
            << ")";
        mulIdx += 1;
      }
      out << ", " << result.getRepr() << std::endl;
      break;
    }
    case ProofRule::FF_IDEAL_SPOLY:
    {
      auto result = nodeToPoly(args[0], branchId);
      auto p = nodeToPoly(children[0].get()->getResult()[0], branchId);
      auto q = nodeToPoly(children[1].get()->getResult()[0], branchId);
      auto pMul = nodeToPoly(args[1], branchId);
      auto qMul = nodeToPoly(args[2], branchId);
      out << result.getId() << " " << PacheckRule::LinComp << " " << p.getId()
          << " * (" << pMul.getRepr() << ") +" << q.getId() << "* ("
          << qMul.getRepr() << "), " << result.getRepr() << std::endl;
      break;
    }
    case ProofRule::FF_IDEAL_MONIC:
    {
      auto result = nodeToPoly(args[0], branchId);
      auto pNode = children[0].get()->getResult()[0];
      auto p = nodeToPoly(pNode, branchId);
      auto pLeadingCoeff = pNode;
      if (pLeadingCoeff.getKind() == Kind::FINITE_FIELD_ADD)
        pLeadingCoeff = pLeadingCoeff[0][0];
      else if (pLeadingCoeff.getKind() == Kind::FINITE_FIELD_MULT)
        pLeadingCoeff = pLeadingCoeff[0];
      Assert(pLeadingCoeff.getKind() == Kind::CONST_FINITE_FIELD) << pLeadingCoeff;
      auto inverse = pLeadingCoeff.getConst<FiniteFieldValue>().recip().getValue();
      out << result.getId() << " " << PacheckRule::LinComp << " " << p.getId()
          << " * (" << inverse << "), " << result.getRepr() << std::endl;
      break;  
    }
    case ProofRule::FF_ROOT_BRANCH:
    {
      auto branchPoly = children[children.size() - 1]
                            .get()
                            ->getResult()[0];
      if (!d_nodeToPacheckPoly.count(branchPoly))
        printInternal(out,
                      children[children.size() - 1],
                      branchId);
      Node branchVar = args[1];
      Node roots = args[2];
      Node branchingPoly = args[3];
      out << nodeToPoly(branchingPoly, branchId).getId() << " " << PacheckRule::Root
          << " " << convertVar(branchVar) << std::endl;
      break;
    }
    default: return;
  }
}
void PacheckProofPrinter::print(std::ostream& out,
                                std::shared_ptr<ProofNode> pfn)
{
  out << PacheckRule::Modulus << " " << d_size.d_val << ";\n";
  printInternal(out, pfn, 1);
  return;
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
