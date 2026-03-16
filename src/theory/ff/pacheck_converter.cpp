#include "theory/ff/pacheck_converter.h"

#include <sstream>
#include <string>

#include "cvc5_private.h"
#include "expr/algorithm/flatten.h"
#include "theory/ff/pacheck_rules.h"
#include "util/finite_field_value.h"
#include "util/integer.h"

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
    : EnvObj(env), d_size(size), d_maxId(1), d_varId(1), d_proof(&cdp)
{
}

std::string convertConst(Node ffConst)
{
  return ffConst.getConst<FiniteFieldValue>().getValue().toString();
}

std::string PacheckProofPrinter::convertVar(TNode var)
{
  if (d_varToPacheckVar.count(var)) return d_varToPacheckVar.at(var);
  std::stringstream varName;
  varName << "v" << d_varId++;
  d_varToPacheckVar[var] = varName.str();
  return varName.str();
}

Node PacheckProofPrinter::cachedFlatten(Node poly, Kind kind)
{
  auto it = d_flattenCache.find(poly);
  if (it != d_flattenCache.end()) return it->second;
  Node flattened = expr::algorithm::flatten(nodeManager(), poly, kind);
  d_flattenCache.emplace(poly, flattened);
  return flattened;
}

std::string PacheckProofPrinter::convertPP(Node pp)
{
  pp = cachedFlatten(pp, Kind::FINITE_FIELD_MULT);
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

void PacheckProofPrinter::writePP(std::ostream& out, Node pp)
{
  pp = cachedFlatten(pp, Kind::FINITE_FIELD_MULT);
  if (pp.getKind() == Kind::FINITE_FIELD_MULT)
  {
    for (size_t it = 0; it < pp.getNumChildren(); ++it)
    {
      if (it > 0) out << " * ";
      if (pp[it].getKind() == Kind::CONST_FINITE_FIELD)
      {
        out << convertConst(pp[it]);
        continue;
      }
      Node currVar = pp[it];
      size_t exp = 1;
      while (it + 1 < pp.getNumChildren() && pp[it + 1] == currVar)
      {
        exp += 1;
        it += 1;
      }
      out << convertVar(currVar);
      if (exp > 1) out << "^" << exp;
    }
    return;
  }
  if (pp.getKind() == Kind::CONST_FINITE_FIELD)
  {
    out << convertConst(pp);
    return;
  }
  out << convertVar(pp);
}

void PacheckProofPrinter::writePolyRepr(std::ostream& out, Node poly)
{
  Node flattened = cachedFlatten(poly, Kind::FINITE_FIELD_ADD);
  if (flattened.getKind() == Kind::FINITE_FIELD_ADD)
  {
    size_t count = 0;
    for (const auto& child : flattened)
    {
      writePP(out, child);
      count += 1;
      if (count < flattened.getNumChildren()) out << " + ";
    }
    return;
  }
  writePP(out, flattened);
}

PacheckPolynomial PacheckProofPrinter::nodeToPoly(Node poly, size_t branch)
{
  Node flattened = cachedFlatten(poly, Kind::FINITE_FIELD_ADD);
  if (d_nodeToPacheckPoly.count(flattened))
  {
    auto res = d_nodeToPacheckPoly.at(flattened);
    if (res.getBranch() == 1 || res.getBranch() == branch) return res;
    PacheckPolynomial newRes(res.getRepr(), d_maxId++, branch);
    d_nodeToPacheckPoly.insert_or_assign(flattened, newRes);
    return newRes;
  }
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
  PacheckPolynomial result(convertPP(flattened), d_maxId++, branch);
  d_nodeToPacheckPoly.emplace(flattened, result);
  return result;
}

bool PacheckProofPrinter::containsProof(Node poly, size_t branch)
{
  Node flattened = cachedFlatten(poly, Kind::FINITE_FIELD_ADD);
  if (!d_nodeToPacheckPoly.count(flattened)) return false;
  auto res = d_nodeToPacheckPoly.at(flattened);
  return res.getBranch() == 1 || res.getBranch() == branch;
}
void PacheckProofPrinter::printInternal(std::ostream& out,
                                        std::shared_ptr<ProofNode> pfn,
                                        size_t branchId)
{
  if (!d_visited.insert(pfn.get()).second) return;
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
      out << PacheckRule::Root << " "
          << nodeToPoly(branchingPoly, branchId).getId() << " "
          << convertVar(branchVar);
      for (size_t it = 0; it < roots.getNumChildren(); ++it)
      {
        out << " " << convertConst(roots[it]);
      }
      out << ";" << std::endl;
      size_t branchIt = 1;
      for (int it = roots.getNumChildren() - 1; it >= 0; --it)
      {
        const auto root = roots[it].getConst<FiniteFieldValue>();
        Node assignmentPoly;
        if (root.getValue() == 0)
          assignmentPoly = branchVar;
        else
          assignmentPoly = nodeManager()->mkNode(
              Kind::FINITE_FIELD_ADD, branchVar, nodeManager()->mkConst(-root));
        const auto assignmentPacheckPoly = nodeToPoly(assignmentPoly, branchId);
        out << PacheckRule::Branch << " " << assignmentPacheckPoly.getId()
            << " " << convertVar(branchVar) << " " << convertConst(roots[it])
            << ";" << std::endl;
        printInternal(out, children[branchIt], branchId + branchIt);
        branchIt += 1;
      }
      return;
    }
    AlwaysAssert(branchStep->getRule() == ProofRule::FF_EXHAUST_BRANCH);
    out << PacheckRule::Exhaust << " "
        << convertVar(branchStep->getArguments()[0][0]);
    for (size_t it = 1; it < branchStep->getArguments()[0].getNumChildren();
         ++it)
    {
      out << ", " << convertVar(branchStep->getArguments()[0][it]);
    }
    out << ";" << std::endl;
    size_t branchIt = 1;
    for (Integer val = 0; val < d_size.d_val; val += 1)
    {
      for (const auto& var : branchStep->getArguments()[0])
      {
        Node assignmentPoly;
        if (val == 0)
          assignmentPoly = var;
        else
          assignmentPoly = nodeManager()->mkNode(
              Kind::FINITE_FIELD_ADD,
              var,
              nodeManager()->mkConst(FiniteFieldValue(-val, d_size)));
        const auto assignmentPacheckPoly = nodeToPoly(assignmentPoly, branchId);
        out << PacheckRule::Branch << " " << assignmentPacheckPoly.getId()
            << " " << convertVar(var) << " " << val << ";" << std::endl;
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
        out << PacheckRule::Axiom << " " << pacheckPoly.getId() << " "
            << pacheckPoly.getRepr() << ";" << std::endl;
      }
      break;
    }
    case ProofRule::FF_FIELD_POLYS:
    {
      for (const auto& poly : args)
      {
        if (containsProof(poly, branchId)) continue;
        PacheckPolynomial pacheckPoly = nodeToPoly(poly, branchId);
        out << PacheckRule::Axiom << " " << pacheckPoly.getId() << " "
            << pacheckPoly.getRepr() << ";" << std::endl;
      }
      break;
    }
    case ProofRule::FF_IDEAL_REDUCE:
    {
      if (containsProof(pfn.get()->getResult()[0], branchId)) break;
      auto reductors = args[1];
      auto multipliers = args[2];
      size_t mulIdx = 0;
      auto initial = nodeToPoly(reductors[0], branchId);
      auto result = nodeToPoly(pfn.get()->getResult()[0], branchId);
      out << PacheckRule::LinComp << " " << result.getId() << " "
          << initial.getId() << "* (1)";
      for (size_t it = 1; it < reductors.getNumChildren(); ++it)
      {
        auto reductor = nodeToPoly(reductors[it], branchId);
        out << " + " << reductor.getId() << " * (";
        writePolyRepr(out, multipliers[mulIdx]);
        out << ")";
        mulIdx += 1;
      }
      out << ", " << result.getRepr() << ";" << std::endl;
      break;
    }
    case ProofRule::FF_IDEAL_REDUCE_ZERO:
    {
      if (containsProof(pfn.get()->getResult()[0], branchId)) break;
      auto reductors = args[1];
      auto multipliers = args[2];
      auto result = nodeToPoly(pfn.get()->getResult()[0], branchId);
      auto firstReductor = nodeToPoly(reductors[0], branchId);
      out << PacheckRule::LinComp << " " << result.getId() << " "
          << firstReductor.getId() << " * (";
      writePolyRepr(out, multipliers[0]);
      out << ")";
      for (size_t it = 1; it < reductors.getNumChildren(); ++it)
      {
        auto reductor = nodeToPoly(reductors[it], branchId);
        out << " + " << reductor.getId() << " * (";
        writePolyRepr(out, multipliers[it]);
        out << ")";
      }
      out << ", " << result.getRepr() << ";" << std::endl;
      break;
    }
    case ProofRule::FF_IDEAL_SPOLY:
    {
      if (containsProof(args[0], branchId)) break;
      auto result = nodeToPoly(args[0], branchId);
      auto p = nodeToPoly(children[0].get()->getResult()[0], branchId);
      auto q = nodeToPoly(children[1].get()->getResult()[0], branchId);
      out << PacheckRule::LinComp << " " << result.getId() << " " << p.getId()
          << " * (";
      writePolyRepr(out, args[1]);
      out << ") +" << q.getId() << "* (";
      writePolyRepr(out, args[2]);
      out << "), " << result.getRepr() << ";" << std::endl;
      break;
    }
    case ProofRule::FF_IDEAL_MONIC:
    {
      if (containsProof(args[0], branchId)) break;
      auto result = nodeToPoly(args[0], branchId);
      auto p = nodeToPoly(children[0].get()->getResult()[0], branchId);
      out << PacheckRule::LinComp << " " << result.getId() << " " << p.getId()
          << " * (";
      writePolyRepr(out, args[1]);
      out << "), " << result.getRepr() << ";" << std::endl;
      break;
    }
    case ProofRule::FF_ROOT_BRANCH:
    {
      auto branchPoly = children[children.size() - 1].get()->getResult()[0];
      if (!containsProof(branchPoly, branchId))
        printInternal(out, children[children.size() - 1], branchId);
      Node branchVar = args[1];
      Node roots = args[2];
      Node branchingPoly = args[3];
      out << PacheckRule::Root << " "
          << nodeToPoly(branchingPoly, branchId).getId() << " "
          << convertVar(branchVar) << ";" << std::endl;
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
