/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term database sygus class.
 */

#include "theory/quantifiers/sygus/term_database_sygus.h"

#include <sstream>

#include "base/check.h"
#include "expr/bound_var_manager.h"
#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** An attribute for mapping sygus variables to builtin variables */
struct SygusBuiltinFreeVarAttributeId
{
};
using SygusBuiltinFreeVarAttribute =
    expr::Attribute<SygusBuiltinFreeVarAttributeId, Node>;

std::ostream& operator<<(std::ostream& os, EnumeratorRole r)
{
  switch (r)
  {
    case ROLE_ENUM_POOL: os << "POOL"; break;
    case ROLE_ENUM_SINGLE_SOLUTION: os << "SINGLE_SOLUTION"; break;
    case ROLE_ENUM_MULTI_SOLUTION: os << "MULTI_SOLUTION"; break;
    case ROLE_ENUM_CONSTRAINED: os << "CONSTRAINED"; break;
    default: os << "enum_" << static_cast<unsigned>(r); break;
  }
  return os;
}

TermDbSygus::TermDbSygus(Env& env, QuantifiersState& qs)
    : EnvObj(env),
      d_qstate(qs),
      d_syexp(new SygusExplain(env, this)),
      d_funDefEval(new FunDefEvaluator(env)),
      d_eval_unfold(new SygusEvalUnfold(env, this)),
      d_ochecker(env.getOracleChecker())
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

void TermDbSygus::finishInit(QuantifiersInferenceManager* qim) { d_qim = qim; }

bool TermDbSygus::reset( Theory::Effort e ) { 
  return true;  
}

TNode TermDbSygus::getFreeVar(const TypeNode& tn, size_t i)
{
  return d_fv.getFreeVar(tn, i);
}

TNode TermDbSygus::getFreeVarInc(const TypeNode& tn,
                                 std::map<TypeNode, size_t>& var_count)
{
  return d_fv.getFreeVarInc(tn, var_count);
}

Node TermDbSygus::getProxyVariable(TypeNode tn, Node c)
{
  Assert(tn.isDatatype());
  Assert(tn.getDType().isSygus());
  Assert(tn.getDType().getSygusType() == c.getType());

  std::map<Node, Node>::iterator it = d_proxy_vars[tn].find(c);
  if (it == d_proxy_vars[tn].end())
  {
    SygusTypeInfo& ti = getTypeInfo(tn);
    int anyC = ti.getAnyConstantConsNum();
    NodeManager* nm = nodeManager();
    Node k;
    if (anyC == -1)
    {
      k = NodeManager::mkDummySkolem("sy", tn, "sygus proxy");
      SygusPrintProxyAttribute spa;
      k.setAttribute(spa, c);
    }
    else
    {
      const DType& dt = tn.getDType();
      k = nm->mkNode(Kind::APPLY_CONSTRUCTOR, dt[anyC].getConstructor(), c);
    }
    d_proxy_vars[tn][c] = k;
    return k;
  }
  return it->second;
}

Node TermDbSygus::mkGeneric(const DType& dt,
                            unsigned c,
                            std::map<TypeNode, size_t>& var_count,
                            std::map<int, Node>& pre,
                            bool doBetaRed)
{
  Assert(c < dt.getNumConstructors());
  Assert(dt.isSygus());
  Assert(!dt[c].getSygusOp().isNull());
  std::vector< Node > children;
  Trace("sygus-db-debug") << "mkGeneric " << dt.getName() << " " << c << "..."
                          << std::endl;
  for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
  {
    Node a;
    std::map< int, Node >::iterator it = pre.find( i );
    if( it!=pre.end() ){
      a = it->second;
      Trace("sygus-db-debug") << "From pre: " << a << std::endl;
    }else{
      TypeNode tna = dt[c].getArgType(i);
      a = getFreeVarInc(tna, var_count);
      if (tna.isSygusDatatype())
      {
        a = getBuiltinFreeVarFor(a);
      }
    }
    Trace("sygus-db-debug")
        << "  child " << i << " : " << a << " : " << a.getType() << std::endl;
    Assert(!a.isNull());
    children.push_back( a );
  }
  Node ret = datatypes::utils::mkSygusTerm(dt, c, children, doBetaRed);
  Trace("sygus-db-debug") << "mkGeneric returns " << ret << std::endl;
  return ret;
}

Node TermDbSygus::mkGeneric(const DType& dt,
                            int c,
                            std::map<int, Node>& pre,
                            bool doBetaRed)
{
  std::map<TypeNode, size_t> var_count;
  return mkGeneric(dt, c, var_count, pre, doBetaRed);
}

Node TermDbSygus::mkGeneric(const DType& dt, int c, bool doBetaRed)
{
  std::map<int, Node> pre;
  return mkGeneric(dt, c, pre, doBetaRed);
}

struct CanonizeBuiltinAttributeId
{
};
using CanonizeBuiltinAttribute =
    expr::Attribute<CanonizeBuiltinAttributeId, Node>;

Node TermDbSygus::canonizeBuiltin(Node n)
{
  std::map<TypeNode, size_t> var_count;
  return canonizeBuiltin(n, var_count);
}

Node TermDbSygus::canonizeBuiltin(Node n, std::map<TypeNode, size_t>& var_count)
{
  // has it already been computed?
  if (var_count.empty() && n.hasAttribute(CanonizeBuiltinAttribute()))
  {
    Node ret = n.getAttribute(CanonizeBuiltinAttribute());
    Trace("sygus-db-canon") << "cached " << n << " : " << ret << "\n";
    return ret;
  }
  Trace("sygus-db-canon") << "  CanonizeBuiltin : compute for " << n << "\n";
  Node ret = n;
  // it is symbolic if it represents "any constant"
  if (n.getKind() == Kind::APPLY_SELECTOR)
  {
    TypeNode tn = n[0].getType();
    ret = getFreeVarInc(tn, var_count);
    if (tn.isSygusDatatype())
    {
      ret = getBuiltinFreeVarFor(ret);
    }
  }
  else if (n.getKind() != Kind::APPLY_CONSTRUCTOR)
  {
    ret = n;
  }
  else
  {
    Assert(n.getKind() == Kind::APPLY_CONSTRUCTOR);
    bool childChanged = false;
    std::vector<Node> children;
    children.push_back(n.getOperator());
    for (unsigned j = 0, size = n.getNumChildren(); j < size; ++j)
    {
      Node child = canonizeBuiltin(n[j], var_count);
      children.push_back(child);
      childChanged = childChanged || child != n[j];
    }
    if (childChanged)
    {
      ret = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, children);
    }
  }
  // cache if we had a fresh variable count
  if (var_count.empty())
  {
    n.setAttribute(CanonizeBuiltinAttribute(), ret);
  }
  Trace("sygus-db-canon") << "  ...normalized " << n << " --> " << ret
                          << std::endl;
  Assert(ret.getType() == n.getType());
  return ret;
}

struct SygusToBuiltinAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinAttributeId, Node>
    SygusToBuiltinAttribute;

Node TermDbSygus::sygusToBuiltin(Node n, TypeNode tn)
{
  if (n.isConst())
  {
    // if its a constant, we use the datatype utility version
    return datatypes::utils::sygusToBuiltin(n);
  }
  Assert(n.getType() == tn);
  if (!tn.isDatatype())
  {
    return n;
  }
  // has it already been computed?
  if (n.hasAttribute(SygusToBuiltinAttribute()))
  {
    return n.getAttribute(SygusToBuiltinAttribute());
  }
  Trace("sygus-db-debug") << "SygusToBuiltin : compute for " << n
                          << ", type = " << tn << std::endl;
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    return n;
  }
  if (n.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    unsigned i = datatypes::utils::indexOf(n.getOperator());
    Assert(n.getNumChildren() == dt[i].getNumArgs());
    std::map<int, Node> pre;
    for (unsigned j = 0, size = n.getNumChildren(); j < size; j++)
    {
      pre[j] = sygusToBuiltin(n[j], dt[i].getArgType(j));
      Trace("sygus-db-debug")
          << "sygus to builtin " << n[j] << " is " << pre[j] << std::endl;
    }
    Node ret = mkGeneric(dt, i, pre);
    Trace("sygus-db-debug")
        << "SygusToBuiltin : Generic is " << ret << std::endl;
    // cache
    n.setAttribute(SygusToBuiltinAttribute(), ret);
    return ret;
  }
  if (n.hasAttribute(SygusPrintProxyAttribute()))
  {
    // this variable was associated by an attribute to a builtin node
    return n.getAttribute(SygusPrintProxyAttribute());
  }
  // It should be a free variable allocated by this class.
  Assert(d_fv.isFreeVar(n));
  Node ret = getBuiltinFreeVarFor(n);
  Trace("sygus-db-debug") << "SygusToBuiltin: variable for " << n << " is "
                          << ret << std::endl;
  return ret;
}

Node TermDbSygus::getBuiltinFreeVarFor(const Node& v)
{
  Assert(d_fv.isFreeVar(v));
  const TypeNode& tn = v.getType();
  Assert(tn.isSygusDatatype());
  const TypeNode& vtn = tn.getDType().getSygusType();
  BoundVarManager* bvm = nodeManager()->getBoundVarManager();
  return bvm->mkBoundVar<SygusBuiltinFreeVarAttribute>(v, vtn);
}

bool TermDbSygus::registerSygusType(TypeNode tn)
{
  std::map<TypeNode, bool>::iterator it = d_registerStatus.find(tn);
  if (it != d_registerStatus.end())
  {
    // already registered
    return it->second;
  }
  d_registerStatus[tn] = false;
  // it must be a sygus datatype
  if (!tn.isDatatype())
  {
    return false;
  }
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    return false;
  }
  d_registerStatus[tn] = true;
  SygusTypeInfo& sti = d_tinfo[tn];
  sti.initialize(this, tn);
  return true;
}

void TermDbSygus::registerEnumerator(Node e,
                                     Node f,
                                     SynthConjecture* conj,
                                     EnumeratorRole erole)
{
  if (d_enum_to_conjecture.find(e) != d_enum_to_conjecture.end())
  {
    // already registered
    return;
  }
  Trace("sygus-db") << "Register enumerator : " << e << std::endl;
  // register its type
  TypeNode et = e.getType();
  registerSygusType(et);
  d_enum_to_conjecture[e] = conj;
  d_enum_to_synth_fun[e] = f;
  NodeManager* nm = nodeManager();

  Trace("sygus-db") << "  registering symmetry breaking clauses..."
                    << std::endl;
  // depending on if we are using symbolic constructors, introduce symmetry
  // breaking lemma templates for each relevant subfield type of the grammar
  SygusTypeInfo& eti = getTypeInfo(et);
  std::vector<TypeNode> sf_types;
  eti.getSubfieldTypes(sf_types);
  bool sharedSel = options().datatypes.dtSharedSelectors;
  // whether this enumerator relies on any-constant constructors
  bool usingAnyConst = false;
  // for each type of subfield type of this enumerator
  for (unsigned i = 0, ntypes = sf_types.size(); i < ntypes; i++)
  {
    std::vector<unsigned> rm_indices;
    TypeNode stn = sf_types[i];
    Assert(stn.isDatatype());
    SygusTypeInfo& sti = getTypeInfo(stn);
    const DType& dt = stn.getDType();
    int anyC = sti.getAnyConstantConsNum();
    if (anyC != -1)
    {
      usingAnyConst = true;
      for (unsigned j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        bool isAnyC = static_cast<int>(j) == anyC;
        if (!isAnyC)
        {
          // if we are using the any constant constructor, do not use any
          // concrete constant
          Node c_op = sti.getConsNumConst(j);
          if (!c_op.isNull())
          {
            rm_indices.push_back(j);
          }
        }
      }
    }
    for (unsigned& rindex : rm_indices)
    {
      // make the apply-constructor corresponding to an application of the
      // constant or "any constant" constructor
      // we call getInstCons since in the case of any constant constructors, it
      // is necessary to generate a term of the form any_constant( x.0 ) for a
      // fresh variable x.0.
      Node fv = getFreeVar(stn, 0);
      Node exc_val = datatypes::utils::getInstCons(fv, dt, rindex, sharedSel);
      // should not include the constuctor in any subterm
      Node x = getFreeVar(stn, 0);
      Trace("sygus-db") << "Construct symmetry breaking lemma from " << x
                        << " == " << exc_val << std::endl;
      Node lem = getExplain()->getExplanationForEquality(x, exc_val);
      lem = lem.negate();
      Trace("cegqi-lemma")
          << "Cegqi::Lemma : exclude symbolic cons lemma (template) : " << lem
          << std::endl;
      // the size of the subterm we are blocking is the weight of the
      // constructor (usually zero)
      registerSymBreakLemma(e, lem, stn, dt[rindex].getWeight());
    }
  }
  Trace("sygus-db") << "  ...finished" << std::endl;

  // determine if we are actively-generated
  bool isActiveGen = false;
  if (options().quantifiers.sygusEnumMode != options::SygusEnumMode::SMART)
  {
    if (erole == ROLE_ENUM_MULTI_SOLUTION || erole == ROLE_ENUM_CONSTRAINED)
    {
      // If the enumerator is a solution for a conjecture with multiple
      // functions, we do not use active generation. If we did, we would have to
      // generate a "product" of two actively-generated enumerators. That is,
      // given a conjecture with two functions-to-synthesize with enumerators
      // e_f and e_g, and if these enumerators generated:
      // e_f -> t1, ..., tn
      // e_g -> s1, ..., sm
      // The sygus module in charge of this conjecture would expect
      // constructCandidates calls of the form
      //   (e_f,e_g) -> (ti, sj)
      // for each i,j. We instead use passive enumeration in this case.
      //
      // If the enumerator is constrained, it cannot be actively generated.
    }
    else if (erole == ROLE_ENUM_POOL)
    {
      // If the enumerator is used for generating a pool of values, we always
      // use active generation.
      isActiveGen = true;
    }
    else if (erole == ROLE_ENUM_SINGLE_SOLUTION)
    {
      // If the enumerator is the single function-to-synthesize, if auto is
      // enabled, we infer whether it is better to enable active generation.
      if (options().quantifiers.sygusEnumMode == options::SygusEnumMode::AUTO)
      {
        // We use active generation if the grammar of the enumerator does not
        // have ITE and does not have Boolean connectives. Experimentally, it
        // is better to use passive generation for these cases since it enables
        // useful search space pruning techniques, e.g. evaluation unfolding,
        // conjecture-specific symmetry breaking. Also, if sygus-stream is
        // enabled, we always use active generation, since the use cases of
        // sygus stream are to find many solutions to an easy problem, where
        // the bottleneck often becomes the large number of "exclude the current
        // solution" clauses.
        if (options().quantifiers.sygusStream
            || (!eti.hasIte() && !eti.hasBoolConnective()))
        {
          isActiveGen = true;
        }
      }
      else
      {
        isActiveGen = true;
      }
    }
    else
    {
      Unreachable() << "Unknown enumerator mode in registerEnumerator";
    }
  }
  Trace("sygus-db") << "isActiveGen for " << e << ", role = " << erole
                    << " returned " << isActiveGen << std::endl;
  // Currently, actively-generated enumerators are either basic or variable
  // agnostic.
  bool isVarAgnostic = isActiveGen
                       && options().quantifiers.sygusEnumMode
                              == options::SygusEnumMode::VAR_AGNOSTIC;
  d_enum_var_agnostic[e] = isVarAgnostic;
  if (isVarAgnostic)
  {
    // requires variable subclasses
    eti.initializeVarSubclasses();
    // If no subclass has more than one variable, do not use variable agnostic
    // enumeration
    bool useVarAgnostic = !eti.isSubclassVarTrivial();
    if (!useVarAgnostic)
    {
      Trace("sygus-db")
          << "...disabling variable agnostic for " << e
          << " since it has no subclass with more than one variable."
          << std::endl;
      d_enum_var_agnostic[e] = false;
      isActiveGen = false;
    }
  }
  // When we are using smart enumeration, we often do not consider model
  // values for arguments of any-constant constructors (in sygus_explain.cpp),
  // hence those blocking lemmas are refutation unsound. For simplicity, we
  // mark unsound once and for all at the beginning, meaning we do not
  // answer "infeasible" when using smart enumeration + any-constant
  // constructors. Using --sygus-repair-const on the other hand avoids this
  // incompleteness, which is checked here.
  if (!isActiveGen && usingAnyConst && !options().quantifiers.sygusRepairConst)
  {
    Assert(d_qim != nullptr);
    d_qim->setRefutationUnsound(
        IncompleteId::QUANTIFIERS_SYGUS_SMART_BLOCK_ANY_CONSTANT);
    Warning()
        << "Warning: The SyGuS solver is incomplete when symbolic constants "
           "are used in grammars and --sygus-repair-const is disabled."
        << std::endl;
  }
  d_enum_active_gen[e] = isActiveGen;
  d_enum_basic[e] = isActiveGen && !isVarAgnostic;
  // We make an active guard if we will be explicitly blocking solutions for
  // the enumerator. This is the case if the role of the enumerator is to
  // populate a pool of terms, or (some cases) of when it is actively generated.
  if (isActiveGen || erole == ROLE_ENUM_POOL)
  {
    // make the guard
    Node ag = NodeManager::mkDummySkolem("eG", nm->booleanType());
    // must ensure it is a literal immediately here
    ag = d_qstate.getValuation().ensureLiteral(ag);
    // must ensure that it is asserted as a literal before we begin solving
    Node lem = nm->mkNode(Kind::OR, ag, ag.negate());
    d_qim->preferPhase(ag, true);
    d_qim->lemma(lem, InferenceId::QUANTIFIERS_SYGUS_ENUM_ACTIVE_GUARD_SPLIT);
    d_enum_to_active_guard[e] = ag;
  }
  // for debugging
  if (d_env.isOutputOn(OutputTag::SYGUS_ENUMERATOR))
  {
    d_env.output(OutputTag::SYGUS_ENUMERATOR) << "(sygus-enumerator";
    if (!f.isNull())
    {
      Assert(f.getInternalSkolemId()
             == InternalSkolemId::QUANTIFIERS_SYNTH_FUN_EMBED);
      std::vector<Node> ski = f.getSkolemIndices();
      // get the argument, which is stored after the internal identifier
      Assert(ski.size() == 2);
      d_env.output(OutputTag::SYGUS_ENUMERATOR) << " :synth-fun " << ski[1];
    }
    d_env.output(OutputTag::SYGUS_ENUMERATOR) << " :role " << erole;
    std::stringstream ss;
    if (isActiveGen)
    {
      ss << (d_enum_var_agnostic[e] ? "VAR_AGNOSTIC" : "FAST");
    }
    else
    {
      ss << "SMART";
    }
    d_env.output(OutputTag::SYGUS_ENUMERATOR) << " :type " << ss.str();
    d_env.output(OutputTag::SYGUS_ENUMERATOR) << ")" << std::endl;
  }
}

bool TermDbSygus::isEnumerator(Node e) const
{
  return d_enum_to_conjecture.find(e) != d_enum_to_conjecture.end();
}

SynthConjecture* TermDbSygus::getConjectureForEnumerator(Node e) const
{
  std::map<Node, SynthConjecture*>::const_iterator itm =
      d_enum_to_conjecture.find(e);
  if (itm != d_enum_to_conjecture.end()) {
    return itm->second;
  }
  return nullptr;
}

Node TermDbSygus::getSynthFunForEnumerator(Node e) const
{
  std::map<Node, Node>::const_iterator itsf = d_enum_to_synth_fun.find(e);
  if (itsf != d_enum_to_synth_fun.end())
  {
    return itsf->second;
  }
  return Node::null();
}

Node TermDbSygus::getActiveGuardForEnumerator(Node e) const
{
  std::map<Node, Node>::const_iterator itag = d_enum_to_active_guard.find(e);
  if (itag != d_enum_to_active_guard.end()) {
    return itag->second;
  }
  return Node::null();
}

bool TermDbSygus::usingSymbolicConsForEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_to_using_sym_cons.find(e);
  if (itus != d_enum_to_using_sym_cons.end())
  {
    return itus->second;
  }
  return false;
}

bool TermDbSygus::isVariableAgnosticEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_var_agnostic.find(e);
  if (itus != d_enum_var_agnostic.end())
  {
    return itus->second;
  }
  return false;
}

bool TermDbSygus::isBasicEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_basic.find(e);
  if (itus != d_enum_basic.end())
  {
    return itus->second;
  }
  return false;
}

bool TermDbSygus::isPassiveEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_active_gen.find(e);
  if (itus != d_enum_active_gen.end())
  {
    return !itus->second;
  }
  return true;
}

void TermDbSygus::getEnumerators(std::vector<Node>& mts)
{
  for (std::map<Node, SynthConjecture*>::iterator itm =
           d_enum_to_conjecture.begin();
       itm != d_enum_to_conjecture.end();
       ++itm)
  {
    mts.push_back( itm->first );
  }
}

void TermDbSygus::registerSymBreakLemma(
    Node e, Node lem, TypeNode tn, unsigned sz, bool isTempl)
{
  d_enum_to_sb_lemmas[e].push_back(lem);
  d_sb_lemma_to_type[lem] = tn;
  d_sb_lemma_to_size[lem] = sz;
  d_sb_lemma_to_isTempl[lem] = isTempl;
}

bool TermDbSygus::hasSymBreakLemmas(std::vector<Node>& enums) const
{
  if (!d_enum_to_sb_lemmas.empty())
  {
    for (std::pair<const Node, std::vector<Node> > sb : d_enum_to_sb_lemmas)
    {
      enums.push_back(sb.first);
    }
    return true;
  }
  return false;
}

void TermDbSygus::getSymBreakLemmas(Node e, std::vector<Node>& lemmas) const
{
  std::map<Node, std::vector<Node> >::const_iterator itsb =
      d_enum_to_sb_lemmas.find(e);
  if (itsb != d_enum_to_sb_lemmas.end())
  {
    lemmas.insert(lemmas.end(), itsb->second.begin(), itsb->second.end());
  }
}

TypeNode TermDbSygus::getTypeForSymBreakLemma(Node lem) const
{
  std::map<Node, TypeNode>::const_iterator it = d_sb_lemma_to_type.find(lem);
  Assert(it != d_sb_lemma_to_type.end());
  return it->second;
}
unsigned TermDbSygus::getSizeForSymBreakLemma(Node lem) const
{
  std::map<Node, unsigned>::const_iterator it = d_sb_lemma_to_size.find(lem);
  Assert(it != d_sb_lemma_to_size.end());
  return it->second;
}

bool TermDbSygus::isSymBreakLemmaTemplate(Node lem) const
{
  std::map<Node, bool>::const_iterator it = d_sb_lemma_to_isTempl.find(lem);
  Assert(it != d_sb_lemma_to_isTempl.end());
  return it->second;
}

void TermDbSygus::clearSymBreakLemmas(Node e) { d_enum_to_sb_lemmas.erase(e); }

bool TermDbSygus::isRegistered(TypeNode tn) const
{
  return d_tinfo.find(tn) != d_tinfo.end();
}

TypeNode TermDbSygus::sygusToBuiltinType( TypeNode tn ) {
  std::map<TypeNode, SygusTypeInfo>::iterator it = d_tinfo.find(tn);
  Assert(it != d_tinfo.end());
  return it->second.getBuiltinType();
}

void TermDbSygus::toStreamSygus(const char* c, Node n)
{
  if (TraceIsOn(c))
  {
    std::stringstream ss;
    toStreamSygus(ss, n);
    Trace(c) << ss.str();
  }
}

void TermDbSygus::toStreamSygus(std::ostream& out, Node n)
{
  if (n.isNull())
  {
    out << n;
    return;
  }
  // use external conversion
  out << datatypes::utils::sygusToBuiltin(n, true);
}

SygusTypeInfo& TermDbSygus::getTypeInfo(TypeNode tn)
{
  AlwaysAssert(d_tinfo.find(tn) != d_tinfo.end());
  return d_tinfo[tn];
}

Node TermDbSygus::rewriteNode(Node n) const
{
  Trace("sygus-rewrite") << "Rewrite node: " << n << std::endl;
  Node res;
  if (options().datatypes.sygusRewriter == options::SygusRewriterMode::EXTENDED)
  {
    res = extendedRewrite(n);
  }
  else
  {
    res = rewrite(n);
  }
  Trace("sygus-rewrite") << "Rewrite node post-rewrite: " << res << std::endl;
  if (res.isConst())
  {
    // constant, we are done
    return res;
  }
  if (options().quantifiers.sygusRecFun)
  {
    if (d_funDefEval->hasDefinitions())
    {
      // If recursive functions are enabled, then we use the recursive function
      // evaluation utility.
      Node fres = d_funDefEval->evaluateDefinitions(res);
      if (!fres.isNull())
      {
        res = fres;
      }
      // It may have failed, in which case there are undefined symbols in res or
      // we reached the limit of evaluations. In this case, we revert to the
      // result of rewriting in the return statement below.
    }
    Trace("sygus-rewrite") << "Rewrite node post-rec-fun: " << res << std::endl;
  }
  if (d_ochecker != nullptr)
  {
    // evaluate oracles
    res = d_ochecker->evaluate(res);
    Trace("sygus-rewrite") << "Rewrite node post-oracles: " << res << std::endl;
  }
  return res;
}

unsigned TermDbSygus::getSelectorWeight(TypeNode tn, Node sel)
{
  std::map<TypeNode, std::map<Node, unsigned> >::iterator itsw =
      d_sel_weight.find(tn);
  if (itsw == d_sel_weight.end())
  {
    d_sel_weight[tn].clear();
    itsw = d_sel_weight.find(tn);
    const DType& dt = tn.getDType();
    Trace("sygus-db") << "Compute selector weights for " << dt.getName()
                      << std::endl;
    bool sharedSel = options().datatypes.dtSharedSelectors;
    for (unsigned i = 0, size = dt.getNumConstructors(); i < size; i++)
    {
      unsigned cw = dt[i].getWeight();
      for (size_t j = 0, size2 = dt[i].getNumArgs(); j < size2; j++)
      {
        Node csel = datatypes::utils::getSelector(tn, dt[i], j, sharedSel);
        std::map<Node, unsigned>::iterator its = itsw->second.find(csel);
        if (its == itsw->second.end() || cw < its->second)
        {
          d_sel_weight[tn][csel] = cw;
          Trace("sygus-db") << "  w(" << csel << ") <= " << cw << std::endl;
        }
      }
    }
  }
  Assert(itsw->second.find(sel) != itsw->second.end());
  return itsw->second[sel];
}

TypeNode TermDbSygus::getArgType(const DTypeConstructor& c, unsigned i) const
{
  Assert(i < c.getNumArgs());
  return c.getArgType(i);
}

bool TermDbSygus::isTypeMatch(const DTypeConstructor& c1,
                              const DTypeConstructor& c2)
{
  if( c1.getNumArgs()!=c2.getNumArgs() ){
    return false;
  }else{
    for( unsigned i=0; i<c1.getNumArgs(); i++ ){
      if( getArgType( c1, i )!=getArgType( c2, i ) ){
        return false;
      }
    }
    return true;
  }
}

bool TermDbSygus::isSymbolicConsApp(Node n) const
{
  if (n.getKind() != Kind::APPLY_CONSTRUCTOR)
  {
    return false;
  }
  TypeNode tn = n.getType();
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  unsigned cindex = datatypes::utils::indexOf(n.getOperator());
  // it is symbolic if it represents "any constant"
  return dt[cindex].isSygusAnyConstant();
}

bool TermDbSygus::canConstructKind(TypeNode tn,
                                   Kind k,
                                   std::vector<TypeNode>& argts,
                                   bool aggr)
{
  Assert(isRegistered(tn));
  SygusTypeInfo& ti = getTypeInfo(tn);
  int c = ti.getKindConsNum(k);
  const DType& dt = tn.getDType();
  if (c != -1)
  {
    for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
    {
      argts.push_back(dt[c].getArgType(i));
    }
    return true;
  }
  if (options().datatypes.sygusSimpleSymBreak
      != options::SygusSimpleSymBreakMode::AGG)
  {
    return false;
  }
  if (sygusToBuiltinType(tn).isBoolean())
  {
    if (k == Kind::ITE)
    {
      // ite( b1, b2, b3 ) <---- and( or( ~b1, b2 ), or( b1, b3 ) )
      std::vector<TypeNode> conj_types;
      if (canConstructKind(tn, Kind::AND, conj_types, true)
          && conj_types.size() == 2)
      {
        bool success = true;
        std::vector<TypeNode> disj_types[2];
        for (unsigned cc = 0; cc < 2; cc++)
        {
          if (!canConstructKind(conj_types[cc], Kind::OR, disj_types[cc], true)
              || disj_types[cc].size() != 2)
          {
            success = false;
            break;
          }
        }
        if (success)
        {
          for (unsigned r = 0; r < 2; r++)
          {
            for (unsigned d = 0, size = disj_types[r].size(); d < size; d++)
            {
              TypeNode dtn = disj_types[r][d];
              // must have negation that occurs in the other conjunct
              std::vector<TypeNode> ntypes;
              if (canConstructKind(dtn, Kind::NOT, ntypes)
                  && ntypes.size() == 1)
              {
                TypeNode ntn = ntypes[0];
                for (unsigned dd = 0, inner_size = disj_types[1 - r].size();
                     dd < inner_size;
                     dd++)
                {
                  if (disj_types[1 - r][dd] == ntn)
                  {
                    argts.push_back(ntn);
                    argts.push_back(disj_types[r][d]);
                    argts.push_back(disj_types[1 - r][1 - dd]);
                    if (TraceIsOn("sygus-cons-kind"))
                    {
                      Trace("sygus-cons-kind")
                          << "Can construct kind " << k << " in " << tn
                          << " via child types:" << std::endl;
                      for (unsigned i = 0; i < 3; i++)
                      {
                        Trace("sygus-cons-kind")
                            << "  " << argts[i] << std::endl;
                      }
                    }
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  // could try aggressive inferences here, such as
  // (and b1 b2) <---- (not (or (not b1) (not b2)))
  // (or b1 b2)  <---- (not (and (not b1) (not b2)))
  return false;
}

Node TermDbSygus::getAnchor( Node n ) {
  if (n.getKind() == Kind::APPLY_SELECTOR)
  {
    return getAnchor( n[0] );
  }
  else
  {
    return n;
  }
}

unsigned TermDbSygus::getAnchorDepth( Node n ) {
  if (n.getKind() == Kind::APPLY_SELECTOR)
  {
    return 1+getAnchorDepth( n[0] );
  }
  else
  {
    return 0;
  }
}

Node TermDbSygus::evaluateBuiltin(TypeNode tn,
                                  Node bn,
                                  const std::vector<Node>& args,
                                  bool tryEval)
{
  if (args.empty())
  {
    return rewrite(bn);
  }
  Assert(isRegistered(tn));
  SygusTypeInfo& ti = getTypeInfo(tn);
  const std::vector<Node>& varlist = ti.getVarList();
  Assert(varlist.size() == args.size());

  Node res;
  if (tryEval)
  {
    // Try evaluating, which is much faster than substitution+rewriting.
    // This may fail if there is a subterm of bn under the
    // substitution that is not constant, or if an operator in bn is not
    // supported by the evaluator
    res = evaluate(bn, varlist, args);
  }
  if (res.isNull())
  {
    // must do substitution
    res =
        bn.substitute(varlist.begin(), varlist.end(), args.begin(), args.end());
  }
  // Call the rewrite node function, which may involve recursive function
  // evaluation.
  return rewriteNode(res);
}

bool TermDbSygus::isEvaluationPoint(Node n) const
{
  if (n.getKind() != Kind::DT_SYGUS_EVAL)
  {
    return false;
  }
  if (!n[0].isVar())
  {
    return false;
  }
  for (unsigned i = 1, nchild = n.getNumChildren(); i < nchild; i++)
  {
    if (!n[i].isConst())
    {
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
