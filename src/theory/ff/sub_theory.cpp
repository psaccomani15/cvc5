/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include <CoCoA/CpuTimeLimit.H>
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
#include "theory/ff/util.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "util/resource_manager.h"
namespace cvc5::internal {
namespace theory {
namespace ff {

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env),
      FieldObj(nodeManager(), modulus),
      d_facts(context()),
      d_stats(stats)
{
  // Currently, we support only non-split GB solving.
  d_proofEnabled = options().ff.ffProof
                   && options().ff.ffSolver == options::FfSolver::GB
                   && d_env.isTheoryProofProducing();
  // if (d_proofEnabled) d_proof = new CDProof(env, nullptr, "GlobalFFProofs");
  if (d_proofEnabled) d_proof = new CDProof(env, context(), "GlobalFFProofs");
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
    try
    {
      if (d_facts.empty()) return Result::SAT;
      if (options().ff.ffSolver == options::FfSolver::SPLIT_GB)
      {
        std::vector<Node> facts{};
        std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(facts));
        auto result = split(facts, size(), d_env);
        if (result.has_value())
        {
          const auto nm = nodeManager();
          for (const auto& [var, val] : result.value())
          {
            d_model.insert({var, nm->mkConst<FiniteFieldValue>(val)});
          }
          return Result::SAT;
        }
        std::copy(
            d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
        return Result::UNSAT;
      }
      else if (options().ff.ffSolver == options::FfSolver::GB)
      {
        CocoaEncoder enc(nodeManager(), size());
        for (const Node& node : d_facts)
        {
          enc.addFact(node);
        }
        enc.endScan();
        // assert facts
        for (const Node& node : d_facts)
        {
          enc.addFact(node);
        }
        // compute a GB
        std::vector<CoCoA::RingElem> generators;
        generators.insert(
            generators.end(), enc.polys().begin(), enc.polys().end());
        generators.insert(generators.end(),
                          enc.bitsumPolys().begin(),
                          enc.bitsumPolys().end());
        std::vector<Node> gens{};
        for (auto& poly : generators)
        {
          gens.push_back(enc.encodeBack(poly));
        }
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
            generators.push_back(poly);
          }
        }
        Tracer tracer(generators);

        if (options().ff.ffTraceGb) tracer.setFunctionPointers();

        CoCoA::ideal ideal = CoCoA::ideal(generators);
        std::shared_ptr<IdealProof> idealProofs;
        if (d_proofEnabled)
        {
          idealProofs = std::shared_ptr<IdealProof>(
              new IdealProof(d_env, 0, generators, enc, ideal));
          idealProofs->setFunctionPointers();
          idealProofs->enableProofHooks();
        }
        const auto basis = CoCoA::GBasis(ideal);
        if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();
        // if it is trivial, create a conflict
        bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
        if (is_trivial)
        {
          std::vector<Node> corePolys{};
          if (options().ff.ffTraceGb)
          {
            std::vector<size_t> coreIndices = tracer.trace(basis.front());
            Assert(d_conflict.empty());
            for (size_t i = 0, n = d_facts.size(); i < n; ++i)
            {
              Trace("ff::core")
                  << "In " << i << " : " << d_facts[i] << std::endl;
            }
            for (size_t i : coreIndices)
            {
              // omit (field polys, bitsum polys, ...) from core
              if (enc.polyHasFact(generators[i]))
              {
                Trace("ff::core")
                    << "Core: " << i << " : " << d_facts[i] << std::endl;
                d_conflict.push_back(enc.polyFact(generators[i]));
                corePolys.push_back(enc.encodeBack(generators[i]));
              }
            }
            if (d_conflict.size() != enc.polys().size())
            {
              std::vector<Node> coreGenerators = corePolys;
              coreGenerators.insert(
                  coreGenerators.end(), fieldPolys.begin(), fieldPolys.end());
              idealProofs->updateIdeal(coreGenerators);
              Trace("ff::proof") << "Restriction on unsat core" << std::endl;
            }
          }
          else
          {
            corePolys = gens;
            setTrivialConflict();
          }
          Node unsatVar = idealProofs->oneInUnsat(basis.front(), d_proof);
          produceContradiction(fieldPolys, corePolys);
        }
        else
        {
          Trace("ff::gb") << "Non-trivial GB" << std::endl;

          // common root (vec of CoCoA base ring elements)
          std::vector<CoCoA::RingElem> root =
              findZero(ideal, idealProofs, nodeManager(), d_proof, d_env);
          if (root.empty())
          {
            // UNSAT
            setTrivialConflict();
            produceContradiction(fieldPolys, gens);
          }
          else
          {
            // SAT: populate d_model from the root
            Assert(d_model.empty());
            const auto nm = nodeManager();
            Trace("ff::model") << "Model GF(" << size() << "):" << std::endl;
            for (const auto& [idx, node] : enc.nodeIndets())
            {
              if (isFfLeaf(node))
              {
                Node value = nm->mkConst(enc.cocoaFfToFfVal(root[idx]));
                Trace("ff::model")
                    << " " << node << " = " << value << std::endl;
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
      return d_facts.empty() || d_conflict.empty() ? Result::SAT
                                                   : Result::UNSAT;
    }
    catch (FfTimeoutException& exc)
    {
      return {Result::UNKNOWN, UnknownExplanation::TIMEOUT, exc.getMessage()};
    }
  }
  return {Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK, ""};
}

void SubTheory::setTrivialConflict()
{
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}
void SubTheory::produceContradiction(std::vector<Node>& fieldPolys,
                                     std::vector<Node>& gens)
{
  Node idealGens = nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, gens);
  const Node unsatCore = nodeManager()->mkAnd(d_conflict);
  d_proof->addStep(unsatCore, ProofRule::ASSUME, {}, {unsatCore});
  Trace("ff::proof") << "Assumption: " << unsatCore << std::endl;
  Node commonRoot = IdealProof::nonEmptyVarPred(nodeManager(), idealGens);
  Node satIffCRoot = nodeManager()->mkNode(Kind::EQUAL, unsatCore, commonRoot);
  d_proof->addStep(satIffCRoot, ProofRule::FF_FIELD_SPLIT, {}, {});
  d_proof->addStep(
      commonRoot, ProofRule::EQ_RESOLVE, {unsatCore, satIffCRoot}, {});
  if (!fieldPolys.empty())
  {
    std::vector<Node> newGens = gens;
    newGens.insert(newGens.end(), fieldPolys.begin(), fieldPolys.end());
    Node idealNewGens =
        nodeManager()->mkNode(Kind::FINITE_FIELD_IDEAL, newGens);
    Node commonRootFieldPolys =
        IdealProof::nonEmptyVarPred(nodeManager(), idealNewGens);
    d_proof->addStep(commonRootFieldPolys,
                     ProofRule::FF_FIELD_POLYS,
                     {commonRoot},
                     {fieldPolys});
    commonRoot = commonRootFieldPolys;
  }
  Node falseNode = nodeManager()->mkConst<bool>(false);
  Node noCommonRoot = nodeManager()->mkNode(Kind::NOT, commonRoot);
  d_proof->addStep(
      falseNode, ProofRule::CONTRA, {commonRoot, noCommonRoot}, {});
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
