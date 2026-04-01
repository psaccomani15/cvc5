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
#include "theory/ff/ideal_proof_manager.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/proof_utils.h"
#include "theory/ff/split_gb.h"
#include "theory/ff/sub_theory.h"
#include "theory/ff/util.h"
#include "theory/ff/cocoa_util.h"
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
  if (env.isProofProducing()) d_proof = new CDProof(env, context(), "GlobalFFProofs");
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

void SubTheory::notifyFact(TNode fact) { d_facts.emplace_back(fact); }

Result SubTheory::postCheck(Theory::Effort e)
{
  d_conflict.clear();
  d_model.clear();
  std::vector<CoCoA::RingElem> root;
  Result result = {
      Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON, "internal"};
  if (e == Theory::EFFORT_FULL)
  {
    try
    {
      if (d_facts.empty()) return Result::SAT;
      if (options().ff.ffSolver == options::FfSolver::SPLIT_GB)
      {
        std::vector<Node> facts{};
        std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(facts));
        const auto optModel = split(facts, size(), d_env);
        if (optModel.has_value())
        {
          const auto nm = nodeManager();
          for (const auto& [var, val] : optModel.value())
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
        CocoaEncoder enc(nodeManager(), d_proof, size());
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
        if (d_env.isProofProducing()) Assert(enc.bitsumPolys().empty()) << "Currently Unsupported!" << std::endl;
        std::vector<Node> gens{};
        for (auto& poly : generators)
        {
          gens.push_back(enc.decode(poly));
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
            Node polyTerm = enc.decode(poly);
            fieldPolys.push_back(polyTerm);
            generators.push_back(poly);
          }
        }
        Tracer tracer(generators);

        if (options().ff.ffTraceGb) tracer.setFunctionPointers();

        CoCoA::ideal ideal = CoCoA::ideal(generators);
        std::shared_ptr<IdealProofManager> idealProofs = nullptr;
        if (d_env.isProofProducing())
        {
          idealProofs = std::shared_ptr<IdealProofManager>(
              new IdealProofManager(d_env, d_proof,0, generators, enc, ideal));
          idealProofs->setFunctionPointers();
          idealProofs->enableProofHooks();
        }
        const auto basis = GBasisTimeout(ideal, d_env.getResourceManager());
        if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();
        if (d_env.isProofProducing()) idealProofs->disableProofHooks();
        // if it is trivial, create a conflict
        bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
        if (is_trivial)
        {
          Trace("ff::gb") << "Trivial GB" << std::endl;
          result = Result::UNSAT;
          std::vector<Node> corePolys{};
          if (options().ff.ffTraceGb)
          {
            std::vector<size_t> coreIndices = tracer.trace(basis.front());
            Assert(d_conflict.empty());
            for (size_t i = 0, n = d_facts.size(); i < n; ++i)
            {
              Trace("ff::core")
                  << "In" << i << " : " << d_facts[i] << std::endl;
           }
            for (size_t i : coreIndices)
            {
              // omit (field polys, bitsum polys, ...) from core
              if (enc.polyHasFact(generators[i]))
              {
                Trace("ff::core")
                    << "Core: " << i << " : " << d_facts[i] << std::endl;
                d_conflict.push_back(enc.polyFact(generators[i]));
              if (d_env.isTheoryProofProducing())
                corePolys.push_back(enc.decode(generators[i])); 
              }
            }
          }
          else
          {
            setTrivialConflict();
          }
          if (d_conflict.size() != enc.polys().size())
          {
            std::vector<Node> coreGenerators = corePolys;
            coreGenerators.insert(
                coreGenerators.end(), fieldPolys.begin(), fieldPolys.end());
            if (d_env.isTheoryProofProducing()) idealProofs->updateIdeal(coreGenerators);
            Trace("ff::proof") << "Restriction on unsat core" << std::endl;
          }
          if (d_env.isTheoryProofProducing())
          {
            Node unsatVariety = idealProofs->oneRefutation(basis.front());
            produceContradiction(nodeManager(),
                                 d_proof,
                                 fieldPolys,
                                 enc.getTranslation(),
                                 enc.getMonicMapping(),
                                 corePolys, d_conflict);
          }
        }
        else
        {
          Trace("ff::gb") << "Non-trivial GB" << std::endl;

          // common root (vec of CoCoA base ring elements)
          root = findZero(ideal, d_env, idealProofs);
          if (root.empty())
          {
            // UNSAT
            result = Result::UNSAT;
            setTrivialConflict();
            if (d_env.isTheoryProofProducing())
              produceContradiction(nodeManager(),
                                   d_proof,
                                   fieldPolys,
                                   enc.getTranslation(),
                                   enc.getMonicMapping(),
                                   gens,
                                   d_conflict);
          }
          else
          {
            // SAT: populate d_model from the
            result = Result::SAT;
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
      AlwaysAssert(result.getStatus() != Result::UNKNOWN) << root;
      return result;
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
  return d_proof->getProof(falseNode);
}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5_USE_COCOA */
