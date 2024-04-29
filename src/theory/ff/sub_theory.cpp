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

#ifdef CVC5_USE_COCOA
#define proofProducing true
#include "theory/ff/sub_theory.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/core.h"
#include "theory/ff/ideal_proofs.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "proof/proof_node.h"
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

Node produceNonNullVarPred(NodeManager* nm, Node ideal)
{
  TypeNode typeOfIdealB = ideal.getType();
  TypeNode pType = nm->mkFunctionType(typeOfIdealB, nm->booleanType());
  Node nonNullVarietySymb = nm->mkRawSymbol("nonNullVariety", pType);
  Node nonNullVarietyPred =
      nm->mkNode(Kind::APPLY_UF, nonNullVarietySymb, ideal);
  return nonNullVarietyPred;
}

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env),
      FieldObj(modulus),
      d_facts(context()),
      d_proof(env, nullptr, "ffProofManager"),
      d_stats(stats)
{
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
      d_proof.addStep(literalSATPred, ProofRule::ASSUME, {}, {});
      Trace("ff::trace") << "..will create pf step: " << ProofRule::ASSUME
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
        polys.push_back(nm->mkBoundVar(ostring(poly), nm->sExprType()));
      }
      Node idealRepr = nm->mkNode(Kind::SEXPR, polys);
      Node nonNullVarPred = produceNonNullVarPred(nm, idealRepr);
      Node equivPred = nm->mkNode(Kind::EQUAL, literalSATPred, nonNullVarPred);
      d_proof.addStep(equivPred, ProofRule::FF_FIELD_SPLIT, {}, {});
      Trace("ff::trace") << ".. will create pf step: "
                         << ProofRule::FF_FIELD_SPLIT << equivPred << std::endl;
      d_proof.addStep(nonNullVarPred,
                      ProofRule::EQ_RESOLVE,
                      {literalSATPred, equivPred},
                      {});
      Trace("ff::trace") << ".. will create pf step: " << ProofRule::EQ_RESOLVE
                         << literalSATPred << ", " << equivPred << " ---> "
                         << nonNullVarPred << std::endl;
      Node trueNonNullVarPred;
      size_t nNonFieldPolyGens = generators.size();
      if (options().ff.ffFieldPolys)
      {
        std::vector<Node> fieldPolys{};
        for (const auto& var : CoCoA::indets(enc.polyRing()))
        {
          CoCoA::BigInt characteristic = CoCoA::characteristic(coeffRing());
          long power = CoCoA::LogCardinality(coeffRing());
          CoCoA::BigInt size = CoCoA::power(characteristic, power);
          auto poly = CoCoA::power(var, size) - var;
          Node polyRepr = nm->mkBoundVar(ostring(poly), nm->sExprType());
          fieldPolys.push_back(polyRepr);
          polys.push_back(polyRepr);
          generators.push_back(poly);
        }
        Node newIdealRepr = nm->mkNode(Kind::SEXPR, polys);
        trueNonNullVarPred = produceNonNullVarPred(nm, newIdealRepr);
        d_proof.addStep(trueNonNullVarPred,
                        ProofRule::FF_FIELD_POLYS,
                        {nonNullVarPred},
                        {fieldPolys});
        Trace("ff::trace") << ".. will create pf step: "
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
      IdealProof idealProofs =
          IdealProof(d_env, generators, trueNonNullVarPred, &d_proof);
      const auto basis = CoCoA::GBasis(ideal);
      if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();

      // if it is trivial, create a conflict
      bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
      if (is_trivial)
      {
        Node unsatPolys = idealProofs.oneInUnsat(basis.front());
	Node falseNode = nm->mkConst<bool>(false); 
        d_proof.addStep(falseNode,
                        ProofRule::CONTRA,
                        {trueNonNullVarPred, unsatPolys},
                        {});
	std::shared_ptr<ProofNode> pf = d_proof.getProofFor(falseNode);
	std::ostringstream s;
	ProofNode *pff = pf.get();
	pff->printDebug(s);
        Trace("ff::trace") << "Finish unsat proof production with element" << basis.front() << "\nproof: " << s.str() << std::endl;
        Trace("ff::gb") << "Trivial GB" << std::endl;
        if (options().ff.ffTraceGb)
        {
          std::vector<size_t> coreIndices = tracer.trace(basis.front());
          Assert(d_conflict.empty());
          for (size_t i : coreIndices)
          {
            // omit field polys from core
            if (i < nNonFieldPolyGens)
            {
              Trace("ff::core") << "Core: " << d_facts[i] << std::endl;
              d_conflict.push_back(d_facts[i]);
            }
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
        std::vector<CoCoA::RingElem> root = findZero(ideal);

        if (root.empty())
        {
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

Node SubTheory::getUnsatProof() { return unsatProofNode; }
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
