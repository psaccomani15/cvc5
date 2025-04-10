/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter for the theory of strings and sequences.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__SEQUENCES_REWRITER_H
#define CVC5__THEORY__STRINGS__SEQUENCES_REWRITER_H

#include <vector>

#include "expr/node.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/rewrites.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/strings_entail.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class SequencesRewriter : public TheoryRewriter
{
 public:
  SequencesRewriter(NodeManager* nm,
                    ArithEntail& ae,
                    StringsEntail& se,
                    HistogramStat<Rewrite>* statistics);
  /** The underlying entailment utilities */
  ArithEntail& getArithEntail();
  StringsEntail& getStringsEntail();

  /**
   * Rewrite n based on the proof rewrite rule id.
   * @param id The rewrite rule.
   * @param n The node to rewrite.
   * @return The rewritten version of n based on id, or Node::null() if n
   * cannot be rewritten.
   */
  Node rewriteViaRule(ProofRewriteRule id, const Node& n) override;

 protected:
  /** rewrite regular expression all
   *
   * This is the entry point for post-rewriting applications of re.all.
   * Returns the rewritten form of node.
   */
  Node rewriteAllRegExp(TNode node);
  /** rewrite regular expression concatenation
   *
   * This is the entry point for post-rewriting applications of re.++.
   * Returns the rewritten form of node.
   */
  Node rewriteConcatRegExp(TNode node);
  /** rewrite regular expression star
   *
   * This is the entry point for post-rewriting applications of re.*.
   * Returns the rewritten form of node.
   */
  Node rewriteStarRegExp(TNode node);
  /** rewrite regular expression intersection/union
   *
   * This is the entry point for post-rewriting applications of re.inter and
   * re.union. Returns the rewritten form of node.
   */
  Node rewriteAndOrRegExp(TNode node);
  /** rewrite regular expression loop
   *
   * This is the entry point for post-rewriting applications of re.loop.
   * Returns the rewritten form of node.
   */
  Node rewriteLoopRegExp(TNode node);
  /** rewrite regular expression repeat
   *
   * This is the entry point for post-rewriting applications of re.repeat.
   * Returns the rewritten form of node.
   */
  Node rewriteRepeatRegExp(TNode node);
  /** rewrite regular expression option
   *
   * This is the entry point for post-rewriting applications of re.opt.
   * Returns the rewritten form of node.
   */
  Node rewriteOptionRegExp(TNode node);
  /** rewrite regular expression plus
   *
   * This is the entry point for post-rewriting applications of re.+.
   * Returns the rewritten form of node.
   */
  Node rewritePlusRegExp(TNode node);
  /** rewrite regular expression difference
   *
   * This is the entry point for post-rewriting applications of re.diff.
   * Returns the rewritten form of node.
   */
  Node rewriteDifferenceRegExp(TNode node);
  /** rewrite regular expression range
   *
   * This is the entry point for post-rewriting applications of re.range.
   * Returns the rewritten form of node.
   */
  Node rewriteRangeRegExp(TNode node);

  /** rewrite regular expression membership
   *
   * This is the entry point for post-rewriting applications of str.in.re
   * Returns the rewritten form of node.
   */
  Node rewriteMembership(TNode node);

  /** rewrite string equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two strings s = t, given by node. It is called by rewriteEqualityExt.
   */
  Node rewriteStrEqualityExt(Node node);
  /** rewrite arithmetic equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two arithmetic string terms s = t, given by node. t is called by
   * rewriteEqualityExt.
   */
  Node rewriteArithEqualityExt(Node node);
  /**
   * Called when node rewrites to ret.
   *
   * The rewrite r indicates the justification for the rewrite, which is printed
   * by this function for debugging.
   */
  Node returnRewrite(Node node, Node ret, Rewrite r);
  //-------------------- ProofRewriteRule
  /** Rewrite based on STR_EQ_LEN_UNIFY_PREFIX */
  Node rewriteViaStrEqLenUnifyPrefix(const Node& n);
  /** Rewrite based on STR_EQ_LEN_UNIFY */
  Node rewriteViaStrEqLenUnify(const Node& n, Rewrite& rule);
  /** Rewrite based on RE_LOOP_ELIM */
  Node rewriteViaReLoopElim(const Node& n);
  /** Rewrite based on MACRO_RE_INTER_UNION_INCLUSION */
  Node rewriteViaMacroReInterUnionInclusion(const Node& n);
  /**
   * Rewrite based on RE_INTER_INCLUSION, or RE_UNION_INCLUSION.
   */
  Node rewriteViaReInterUnionInclusion(ProofRewriteRule id, const Node& n);
  /** Rewrite based on STR_IN_RE_EVAL */
  Node rewriteViaStrInReEval(const Node& n);
  /** Rewrite based on STR_IN_RE_CONSUME */
  Node rewriteViaStrInReConsume(const Node& n);
  /** Rewrite based on STR_IN_RE_CONCAT_STAR_CHAR */
  Node rewriteViaStrInReConcatStarChar(const Node& n);
  /** Rewrite based on STR_IN_RE_SIGMA */
  Node rewriteViaStrInReSigma(const Node& n);
  /** Rewrite based on STR_IN_RE_SIGMA_STAR */
  Node rewriteViaStrInReSigmaStar(const Node& n);
  /** Rewrite based on MACRO_SUBSTR_STRIP_SYM_LENGTH */
  Node rewriteViaMacroSubstrStripSymLength(const Node& n,
                                           Rewrite& rule,
                                           StringsEntail& sent);
  /** Rewrite based on STR_INDEXOF_RE_EVAL */
  Node rewriteViaStrIndexofReEval(const Node& n);
  /** Rewrite based on STR_REPLACE_RE_EVAL */
  Node rewriteViaStrReplaceReEval(const Node& n);
  /** Rewrite based on STR_REPLACE_RE_ALL_EVAL */
  Node rewriteViaStrReplaceReAllEval(const Node& n);
  /** Rewrite based on one of the STR_OVERLAP_* rules */
  Node rewriteViaOverlap(ProofRewriteRule id, const Node& n);

 public:
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override;

  /** rewrite equality
   *
   * This method returns a formula that is equivalent to the equality between
   * two strings s = t, given by node. The result of rewrite is one of
   * { s = t, t = s, true, false }.
   */
  Node rewriteEquality(Node node);
  /** rewrite equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two terms s = t, given by node, where s and t are terms in the signature
   * of the theory of strings. Notice that s and t may be of string type or
   * of Int type.
   *
   * Specifically, this function performs rewrites whose conclusion is not
   * necessarily one of { s = t, t = s, true, false }.
   */
  Node rewriteEqualityExt(Node node) override;
  /** rewrite string length
   * This is the entry point for post-rewriting terms node of the form
   *   str.len( t )
   * Returns the rewritten form of node.
   */
  Node rewriteLength(Node node);
  /** rewrite concat
   * This is the entry point for post-rewriting terms node of the form
   *   str.++( t1, .., tn )
   * Returns the rewritten form of node.
   */
  Node rewriteConcat(Node node);
  /** rewrite character at
   * This is the entry point for post-rewriting terms node of the form
   *   str.charat( s, i1 )
   * Returns the rewritten form of node.
   */
  Node rewriteCharAt(Node node);
  /** rewrite substr
   * This is the entry point for post-rewriting terms node of the form
   *   str.substr( s, i1, i2 )
   * Returns the rewritten form of node.
   */
  Node rewriteSubstr(Node node);
  /** rewrite update
   * This is the entry point for post-rewriting terms node of the form
   *   str.update( s, i1, i2 )
   * Returns the rewritten form of node.
   */
  Node rewriteUpdate(Node node);
  /** rewrite contains
   * This is the entry point for post-rewriting terms node of the form
   *   str.contains( t, s )
   * Returns the rewritten form of node.
   *
   * For details on some of the basic rewrites done in this function, see Figure
   * 7 of Reynolds et al "Scaling Up DPLL(T) String Solvers Using
   * Context-Dependent Rewriting", CAV 2017.
   */
  Node rewriteContains(Node node);
  /** rewrite indexof
   * This is the entry point for post-rewriting terms n of the form
   *   str.indexof( s, t, n )
   * Returns the rewritten form of node.
   */
  Node rewriteIndexof(Node node);
  /** rewrite indexof regular expression match
   * This is the entry point for post-rewriting terms n of the form
   *   str.indexof_re( s, r, n )
   * Returns the rewritten form of node.
   */
  Node rewriteIndexofRe(Node node);
  /** rewrite replace
   * This is the entry point for post-rewriting terms n of the form
   *   str.replace( s, t, r )
   * Returns the rewritten form of node.
   */
  Node rewriteReplace(Node node);
  /** rewrite replace all
   * This is the entry point for post-rewriting terms n of the form
   *   str.replaceall( s, t, r )
   * Returns the rewritten form of node.
   */
  Node rewriteReplaceAll(Node node);
  /** rewrite replace internal
   *
   * This method implements rewrite rules that apply to both str.replace and
   * str.replaceall. If it returns a non-null ret, then node rewrites to ret.
   */
  Node rewriteReplaceInternal(Node node);
  /** rewrite regular expression replace
   *
   * This method implements rewrite rules that apply to terms of the form
   * str.replace_re(s, r, t).
   *
   * @param node The node to rewrite
   * @return The rewritten node
   */
  Node rewriteReplaceRe(Node node);
  /** rewrite regular expression replace
   *
   * This method implements rewrite rules that apply to terms of the form
   * str.replace_re_all(s, r, t).
   *
   * @param node The node to rewrite
   * @return The rewritten node
   */
  Node rewriteReplaceReAll(Node node);
  /**
   * Returns the first, shortest sequence in n that matches r.
   *
   * @param n The constant string or sequence to search in.
   * @param r The regular expression to search for.
   * @return A pair holding the start position and the end position of the
   *         match or a pair of string::npos if r does not appear in n.
   */
  std::pair<size_t, size_t> firstMatch(Node n, Node r);
  /** rewrite string reverse
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.rev( s )
   * Returns the rewritten form of node.
   */
  Node rewriteStrReverse(Node node);
  /** rewrite prefix/suffix
   * This is the entry point for post-rewriting terms n of the form
   *   str.prefixof( s, t ) / str.suffixof( s, t )
   * Returns the rewritten form of node.
   */
  Node rewritePrefixSuffix(Node node);

  /** rewrite str.to_code
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_code( t )
   * Returns the rewritten form of node.
   */
  Node rewriteStringToCode(Node node);
  /** rewrite seq.unit
   * This is the entry point for post-rewriting terms n of the form
   *   seq.unit( t )
   * Returns the rewritten form of node.
   */
  Node rewriteSeqUnit(Node node);

  /** rewrite seq.nth
   * This is the entry point for post-rewriting terms n of the form
   *   seq.nth(s, i)
   * Returns the rewritten form of node.
   */
  Node rewriteSeqNth(Node node);

  /** length preserving rewrite
   *
   * Given input n, this returns a string n' whose length is equivalent to n.
   * We apply certain normalizations to n', such as replacing all constants
   * that are not relevant to length by "A".
   */
  Node lengthPreserveRewrite(Node n);

  /**
   * Given a symbolic length n, returns the canonical string (of type stype)
   * for that length. For example if n is constant, this function returns a
   * string consisting of "A" repeated n times. Returns the null node if no such
   * string exists.
   */
  Node canonicalStrForSymbolicLength(Node n, TypeNode stype) const;

  /**
   * post-process rewrite
   *
   * If node is not an equality and ret is an equality,
   * this method applies an additional rewrite step (rewriteEqualityExt) that
   * performs additional rewrites on ret, after which we return the result of
   * this call. Otherwise, this method simply returns ret.
   */
  Node postProcessRewrite(Node node, Node ret);
  /** Reference to the rewriter statistics. */
  HistogramStat<Rewrite>* d_statistics;
  /** The arithmetic entailment module */
  ArithEntail& d_arithEntail;
  /** Instance of the entailment checker for strings. */
  StringsEntail& d_stringsEntail;
  /** Common constants */
  Node d_sigmaStar;
  Node d_true;
  Node d_false;
}; /* class SequencesRewriter */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__SEQUENCES_REWRITER_H */
