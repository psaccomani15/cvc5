/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * TODO(alanctprado)
 */

#include "theory/bv/pb/pb_proof_manager.h"
#include "proof/proof.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb{

PbProofManager::PbProofManager(Env& env, PbBlastProofGenerator* pbbpg)
    : EnvObj(env),
      d_pbbpg(pbbpg),
      d_cdp(new CDProof(env)),
      d_pbpr(new PbProofRules(env, d_cdp))
{}

void PbProofManager::addPbProof(std::vector<std::string> proofLines)
{
  NodeManager* nm = nodeManager();

  if (proofLines[0] == "pseudo-Boolean proof version 1.0" ||
      proofLines[0] == "pseudo-Boolean proof version 2.0")
  {
    proofLines.erase(proofLines.begin());
    std::vector<Node> proof_steps = parseProofLines(proofLines);
  }
  else
  {
    Unreachable() << "\nPbProofManager::addPbProof: cvc5 currently supports"
                  <<  " only pseudo-Boolean proof versions 1.0 and 2.0";
  }

  Node expected = nm->mkConst(false);
  std::vector<Node> children;

  // d_proof->addStep(expected,
  //                  ProofRule::CUTTING_PLANES_REFUTATION,
  //                  children,
  //                  cutting_plane_steps);

  // The step above generates the following error:
  //
  // Fatal failure within cvc5::internal::ProofNodeManager* cvc5::internal::CDProof::getManager() const at /home/alan/logic/cvc5/src/proof/proof.cpp:454
  // Check failure

  // pnm != nullptr
}

void debugPbProofLine(const std::string& line, const std::vector<Node>& steps, bool foo = true)
{
  if (foo)
  {
    Trace("bv-pb-proof") << "Proof step: " << line << "\n";
    Trace("bv-pb-proof") << "Result: " << steps.back() << "\n";
    return;
  }
  if (line[0] == 'c')
  {
    Trace("bv-pb-proof-c") << "Proof step: " << line << "\n";
    Trace("bv-pb-proof-c") << "Result: " << steps.back() << "\n";
  }
  else if (line[0] == 'l')
  {
    Trace("bv-pb-proof-l") << "Proof step: " << line << "\n";
    Trace("bv-pb-proof-l") << "Result: " << steps.back() << "\n";
  }
  else if (line[0] == 'p')
  {
    Trace("bv-pb-proof-p") << "Proof step: " << line << "\n";
    Trace("bv-pb-proof-p") << "Result: " << steps.back() << "\n";
  }
  else if (line[0] == 'u')
  {
    Trace("bv-pb-proof-u") << "Proof step: " << line << "\n";
    Trace("bv-pb-proof-u") << "Result: " << steps.back() << "\n";
  }
}

std::vector<Node> PbProofManager::parseProofLines(std::vector<std::string> proofLines)
{
  std::vector<Node> cutting_plane_steps;
  for (auto& line : proofLines)
  {
    cutting_plane_steps.push_back(d_pbpr->parseLine(line));
    debugPbProofLine(line, cutting_plane_steps);
  }
  return cutting_plane_steps;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
