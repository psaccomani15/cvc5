/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A field-specific theory.
 * That is, the sub-theory for GF(p) for some fixed p.
 * Implements Figure 2, "DecisionProcedure" from [OKTB23].
 *
 * [OKTB23]: https://doi.org/10.1007/978-3-031-37703-7_8
 */

#include "theory/shared_terms_database.h"
#ifdef CVC5_USE_COCOA
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/core.h"
#include "theory/ff/ideal_proofs.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "theory/ff/sub_theory.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
namespace cvc5::internal {
namespace theory {
namespace ff {

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}
  
Node unsatCoreProofRec(NodeManager* nm,
                       CDProof* pm,
                       Node newIdeal,
                       Node nonNullVarFact,
                       std::shared_ptr<ProofNode> currProof)
{
  ProofRule currRule = currProof->getRule();
  if (currRule == ProofRule::FF_ONE_UNSAT)
  {
    Node nullVarFact = nm->mkNode(Kind::NOT, nonNullVarFact);
    auto oneMembershipProof = currProof->getChildren()[0];
    Node oneMembershipFact =
        unsatCoreProofRec(nm, pm, newIdeal, nonNullVarFact, oneMembershipProof);
    pm->addStep(nullVarFact, currRule, {oneMembershipFact}, {}, true);
    return nullVarFact;
  }
  if (currRule == ProofRule::FF_R_DOWN || currRule == ProofRule::FF_S
      || currRule == ProofRule::FF_MONIC)
  {
    Node fact = currProof->getResult();
    Node poly = fact[0];
    Trace("ff::proof::processing")
        << "fact is: " << fact << " extracted poly is: " << poly << std::endl;
    auto premisesProofs = currProof->getChildren();
    std::vector<Node> premises{};
    for (auto p : premisesProofs)
    {
      premises.push_back(
          unsatCoreProofRec(nm, pm, newIdeal, nonNullVarFact, p));
    }
    Node conclusion = nm->mkNode(Kind::FINITE_FIELD_IDEAL_MEMBERSHIP, poly, newIdeal);
    pm->addStep(
        conclusion, currRule, premises, currProof->getArguments(), true);
    return conclusion;
  }
  if (currRule == ProofRule::FF_G)
  {
    Node fact = currProof->getResult();
    Node poly = fact[0];
    Trace("ff::proof::processing")
        << "fact G is: " << fact << " extracted poly is: " << poly << std::endl;

    Node conclusion = nm->mkNode(Kind::FINITE_FIELD_IDEAL_MEMBERSHIP, poly, newIdeal);
    std::vector<Node> argsIdeal{poly, newIdeal};
    pm->addStep(conclusion, currRule, {}, argsIdeal, true);
    return conclusion;
  }
  Unreachable() << "In this scenario the proof step " << currRule
                << " is not valid!";
}
/*
 * Transforms proofs into the unsat core expected format.
 * The unsatProof argument must be a proofNode with a CONTRA rule.
 */
void unsatCoreProof(NodeManager* nm,
                    CDProof* pm,
                    std::vector<Node> conflictLits,
                    std::vector<Node> allPolys,
                    std::vector<Node> fieldPolys,
                    std::vector<size_t> coreIndices,
                    size_t nNonFieldPolyGens)
{
  Node falseNode = nm->mkConst<bool>(false);
  std::shared_ptr<ProofNode> unsatProof = pm->getProofFor(falseNode);
  Assert(unsatProof->getRule() == ProofRule::CONTRA);
  std::vector<Node> conflictPolys{};
  for (size_t idx : coreIndices)
  {
    if (idx < nNonFieldPolyGens) conflictPolys.push_back(allPolys[idx]);
  }
  Node conflictLitsSAT = nm->mkAnd(conflictLits);
  Node unsatCoreIdealTerm = nm->mkNode(Kind::FINITE_FIELD_IDEAL, conflictPolys);
  Node unsatCoreNonNullVar = IdealProof::produceNonNullVarPred(nm, unsatCoreIdealTerm);
  Node equivPred =
      nm->mkNode(Kind::EQUAL, conflictLitsSAT, unsatCoreNonNullVar);
  // pm->addStep(conflictLitsSAT, ProofRule::ASSUME, {}, {});
  pm->addStep(equivPred, ProofRule::FF_FIELD_SPLIT, {}, {}, true);
  pm->addStep(unsatCoreNonNullVar,
              ProofRule::EQ_RESOLVE,
              {conflictLitsSAT, equivPred},
              {}, true);

  if (!fieldPolys.empty())
  {
    conflictPolys.insert(
        conflictPolys.end(), fieldPolys.begin(), fieldPolys.end());
    Node oldUnsatCoreNonNullVar = unsatCoreNonNullVar;
    unsatCoreIdealTerm = nm->mkNode(Kind::FINITE_FIELD_IDEAL, conflictPolys);
    unsatCoreNonNullVar = IdealProof::produceNonNullVarPred(nm, unsatCoreIdealTerm);
    pm->addStep(unsatCoreNonNullVar,
                ProofRule::FF_FIELD_POLYS,
                {oldUnsatCoreNonNullVar},
                {fieldPolys},
                true);
  }

  std::shared_ptr<ProofNode> nullVarProof = unsatProof->getChildren()[1];
  Trace("ff::proof") << "Extracted Unsat Node: "
                     << nullVarProof.get()->getResult() << std::endl;
  Node unsatCoreNullVar = unsatCoreProofRec(
					    nm, pm, unsatCoreIdealTerm, unsatCoreNonNullVar, nullVarProof);
  Trace("ff::proof") << "Result Unsat Node: " << unsatCoreNullVar << std::endl;
  pm->addStep(falseNode,
              ProofRule::CONTRA,
              {unsatCoreNonNullVar, unsatCoreNullVar},
              {},
              true,
              CDPOverwrite::ALWAYS);
}

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env), FieldObj(modulus), d_facts(context()), d_stats(stats)
{
  // Currently, we support only non-split GB solving.
  d_proofEnabled = options().ff.ffProof
                   && options().ff.ffSolver == options::FfSolver::GB
                   && d_env.isTheoryProofProducing();
  if (d_proofEnabled) d_proof = new CDProof(env, nullptr, "GlobalFFProofs");
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

void SubTheory::notifyFact(TNode fact) { d_facts.emplace_back(fact); }

Result SubTheory::postCheck(Theory::Effort e)
{
  d_conflict.clear();
  d_model.clear();
  if (e == Theory::EFFORT_FULL)
  {
    if (d_facts.empty()) return Result::SAT;
    if (options().ff.ffSolver == options::FfSolver::SPLIT_GB)
    {
      std::vector<Node> facts{};
      std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(facts));
      auto result = split(facts, size());
      if (result.has_value())
      {
        const auto nm = nodeManager();
        for (const auto& [var, val] : result.value())
        {
          d_model.insert({var, nm->mkConst<FiniteFieldValue>(val)});
        }
        return Result::SAT;
      }
      std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
      return Result::UNSAT;
    }
    else if (options().ff.ffSolver == options::FfSolver::GB)
    {
      const auto nm = nodeManager();
      std::vector<Node> literals{};
      CocoaEncoder enc(size());

      // collect leaves
      for (const Node& node : d_facts)
      {
        literals.push_back(node);
        enc.addFact(node);
      }
      enc.endScan();
      // assert facts
      for (const Node& node : d_facts)
      {
        enc.addFact(node);
      }
      Node literalSATPred = nm->mkAnd(literals);
      Trace("ff::proof") << "Literals conjunction " << literalSATPred
                         << std::endl;
      d_proof->addStep(literalSATPred, ProofRule::ASSUME, {}, {literalSATPred}, true);
      Trace("ff::proof") << "..will create pf step: " << ProofRule::ASSUME
                         << literalSATPred << std::endl;
      // compute a GB
      std::vector<CoCoA::RingElem> generators;
      generators.insert(
          generators.end(), enc.polys().begin(), enc.polys().end());
      generators.insert(
          generators.end(), enc.bitsumPolys().begin(), enc.bitsumPolys().end());
      std::vector<Node> polys{};
      for (auto& poly : generators)
      {
        polys.push_back(enc.encodeBack(poly));
      }
      Node idealTerm = nm->mkNode(Kind::FINITE_FIELD_IDEAL, polys);
      Node nonNullVarPred = IdealProof::produceNonNullVarPred(nm, idealTerm);
      Node equivPred = nm->mkNode(Kind::EQUAL, literalSATPred, nonNullVarPred);
      d_proof->addStep(equivPred, ProofRule::FF_FIELD_SPLIT, {}, {}, true);
      Trace("ff::proof") << ".. will create pf step: "
                         << ProofRule::FF_FIELD_SPLIT << equivPred << std::endl;
      d_proof->addStep(nonNullVarPred,
                      ProofRule::EQ_RESOLVE,
                      {literalSATPred, equivPred},
		       {}, true);
      Trace("ff::proof") << ".. will create pf step: " << ProofRule::EQ_RESOLVE
                         << literalSATPred << ", " << equivPred << " ---> "
                         << nonNullVarPred << std::endl;
      Node trueNonNullVarPred;
      size_t nNonFieldPolyGens = generators.size();
      std::vector<Node> fieldPolys{};
      if (options().ff.ffFieldPolys)
      {
        for (const auto& var : CoCoA::indets(enc.polyRing()))
        {
          CoCoA::BigInt characteristic = CoCoA::characteristic(coeffRing());
          long power = CoCoA::LogCardinality(coeffRing());
          CoCoA::BigInt size = CoCoA::power(characteristic, power);
          auto poly = CoCoA::power(var, size) - var;
          Node polyTerm = enc.encodeBack(poly);
          fieldPolys.push_back(polyTerm);
          polys.push_back(polyTerm);
          generators.push_back(poly);
        }
        Node newIdealTerm = nm->mkNode(Kind::FINITE_FIELD_IDEAL, polys);
        trueNonNullVarPred = IdealProof::produceNonNullVarPred(nm, newIdealTerm);
        d_proof->addStep(trueNonNullVarPred,
                        ProofRule::FF_FIELD_POLYS,
                        {nonNullVarPred},
			 {fieldPolys}, true);
        Trace("ff::proof") << ".. will create pf step: "
                           << ProofRule::FF_FIELD_POLYS << nonNullVarPred
                           << " ---> " << trueNonNullVarPred
                           << " args: " << fieldPolys << std::endl;
      }
      else
      {
        trueNonNullVarPred = nonNullVarPred;
      }
      Tracer tracer(generators);

      if (options().ff.ffTraceGb) tracer.setFunctionPointers();

      CoCoA::ideal ideal = CoCoA::ideal(generators);
      std::shared_ptr<IdealProof> idealProofs;
      if (d_proofEnabled)
      {
        idealProofs = std::shared_ptr<IdealProof>(new IdealProof(
            d_env, 0, generators, trueNonNullVarPred, enc, ideal));
        idealProofs->setFunctionPointers();
        idealProofs->enableProofHooks();
      }
      const auto basis = CoCoA::GBasis(ideal);
      if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();
      // if it is trivial, create a conflict
      bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
      if (is_trivial)
      {
        Node unsatVar = idealProofs->oneInUnsat(basis.front(), d_proof);
        Node falseNode = nm->mkConst<bool>(false);
        d_proof->addStep(
            falseNode, ProofRule::CONTRA, {trueNonNullVarPred, unsatVar}, {});
        // d_proof.addStep(d_emptyVarFact, ProofRule::SCOPE, {falseNode},
        // {d_validFact});
        std::shared_ptr<ProofNode> pf = d_proof->getProofFor(unsatVar);
        std::ostringstream s;
        ProofNode* pff = pf.get();
        pff->printDebug(s, true);
        Trace("ff::proof") << "Finish unsat proof production with element "
                           << basis.front() << "\nproof: " << s.str()
                           << std::endl;
        Trace("ff::gb") << "Trivial GB" << std::endl;
        if (options().ff.ffTraceGb)
        {
          std::vector<size_t> coreIndices = tracer.trace(basis.front());
          Assert(d_conflict.empty());
          for (size_t i : coreIndices)
          {
            // omit field polys from core: Fix this. This is wrong.
            if (i < nNonFieldPolyGens)
            {
	      Unreachable();
              Trace("ff::core") << "Core: " << d_facts[i] << std::endl;
              d_conflict.push_back(d_facts[i]);
            }
          }
          // I.e the unsat core is a proper subset of the generators
          if (nNonFieldPolyGens != literals.size())
          {
            unsatCoreProof(nm,
                           d_proof,
                           d_conflict,
                           polys,
                           fieldPolys,
                           coreIndices,
                           nNonFieldPolyGens);
            Trace("ff::proof") << "Restriction on unsat core" << std::endl;
            Node notConflict = nm->mkAnd(d_conflict).notNode();
            // d_proof.addStep(literalSATPred.notNode(),
            // ProofRule::FF_NO_ROOTS_UNSAT, {falseNode}, {});
          }
        }
        else
        {
          setTrivialConflict();
        }
      }
      else
      {
        Trace("ff::gb") << "Non-trivial GB" << std::endl;

        // common root (vec of CoCoA base ring elements)
        std::vector<CoCoA::RingElem> root =
            findZero(ideal, idealProofs, nodeManager(), d_proof);
        if (root.empty())
        {
          Node satFact = idealProofs->getSatFact();
          Node unsatFact = idealProofs->getUnsatFact();
          Node falseNode = nm->mkConst<bool>(false);
          d_proof->addStep(
			   falseNode, ProofRule::CONTRA, {satFact, unsatFact}, {}, true);
          std::shared_ptr<ProofNode> pf = d_proof->getProofFor(falseNode);
          std::ostringstream s;
          ProofNode* pff = pf.get();
          pff->printDebug(s, true);
          Trace("ff::proof") << "Finish unsat proof production with proof;"
                             << "\nproof: " << s.str() << std::endl;
          // UNSAT
          setTrivialConflict();
        }
        else
        {
          // SAT: populate d_model from the root
          Assert(d_model.empty());
          for (const auto& [idx, node] : enc.nodeIndets())
          {
            if (isFfLeaf(node))
            {
              Node value = nm->mkConst(enc.cocoaFfToFfVal(root[idx]));
              Trace("ff::model")
                  << "Model: " << node << " = " << value << std::endl;
              d_model.emplace(node, value);
            }
          }
        }
      }
    }
    else
    {
      Unreachable() << options().ff.ffSolver << std::endl;
    }
    AlwaysAssert((!d_conflict.empty() ^ !d_model.empty()) || d_facts.empty());
    return d_facts.empty() || d_conflict.empty() ? Result::SAT : Result::UNSAT;
  }
  return {Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK, ""};
}

void SubTheory::setTrivialConflict()
{
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}

bool SubTheory::inConflict() const { return !d_conflict.empty(); }

const std::vector<Node>& SubTheory::conflict() const { return d_conflict; }

const std::unordered_map<Node, Node>& SubTheory::model() const
{
  return d_model;
}

std::shared_ptr<ProofNode> SubTheory::getProof()
{
  const auto nm = nodeManager();
  Node falseNode = nm->mkConst<bool>(false);
  Assert(d_proof->hasStep(falseNode));
  return d_proof->getProof(falseNode);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
