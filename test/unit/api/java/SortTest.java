/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the Java API functions.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static io.github.cvc5.SortKind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SortTest
{
  private TermManager d_tm;

  @BeforeEach
  void setUp()
  {
    d_tm = new TermManager();
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  Sort create_datatype_sort() throws CVC5ApiException
  {
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    cons.addSelectorSelf("tail");
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    return d_tm.mkDatatypeSort(dtypeSpec);
  }

  Sort create_param_datatype_sort() throws CVC5ApiException
  {
    Sort sort = d_tm.mkParamSort("T");
    DatatypeDecl paramDtypeSpec = d_tm.mkDatatypeDecl("paramlist", new Sort[] {sort});
    DatatypeConstructorDecl paramCons = d_tm.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil = d_tm.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramDtypeSpec.addConstructor(paramCons);
    paramDtypeSpec.addConstructor(paramNil);
    return d_tm.mkDatatypeSort(paramDtypeSpec);
  }

  @Test
  void operators_comparison()
  {
    assertDoesNotThrow(() -> d_tm.getIntegerSort() == new Sort());
    assertDoesNotThrow(() -> d_tm.getIntegerSort() != new Sort());
    assertDoesNotThrow(() -> d_tm.getIntegerSort().compareTo(new Sort()));
  }

  @Test
  void hash()
  {
    assertEquals(d_tm.getIntegerSort().hashCode(), d_tm.getIntegerSort().hashCode());
    assertNotEquals(d_tm.getIntegerSort().hashCode(), d_tm.getStringSort().hashCode());
    assertNotEquals(d_tm.getIntegerSort().hashCode(), (new Sort()).hashCode());
  }

  @Test
  void getKind() throws CVC5ApiException
  {
    Sort b = d_tm.getBooleanSort();
    Sort dt_sort = create_datatype_sort();
    Sort arr_sort = d_tm.mkArraySort(d_tm.getRealSort(), d_tm.getIntegerSort());
    assertEquals(b.getKind(), BOOLEAN_SORT);
    assertEquals(dt_sort.getKind(), DATATYPE_SORT);
    assertEquals(arr_sort.getKind(), ARRAY_SORT);
  }

  @Test
  void hasGetSymbol() throws CVC5ApiException
  {
    Sort n = new Sort();
    Sort b = d_tm.getBooleanSort();
    Sort s0 = d_tm.mkParamSort("s0");
    Sort s1 = d_tm.mkParamSort("|s1\\|");

    assertThrows(CVC5ApiException.class, () -> n.hasSymbol());
    assertFalse(b.hasSymbol());
    assertTrue(s0.hasSymbol());
    assertTrue(s1.hasSymbol());

    assertThrows(CVC5ApiException.class, () -> n.getSymbol());
    assertThrows(CVC5ApiException.class, () -> b.getSymbol());
    assertEquals(s0.getSymbol(), "s0");
    assertEquals(s1.getSymbol(), "|s1\\|");
  }

  @Test
  void isBoolean()
  {
    assertTrue(d_tm.getBooleanSort().isBoolean());
    assertDoesNotThrow(() -> new Sort().isBoolean());
  }

  @Test
  void isInteger()
  {
    assertTrue(d_tm.getIntegerSort().isInteger());
    assertTrue(!d_tm.getRealSort().isInteger());
    assertDoesNotThrow(() -> new Sort().isInteger());
  }

  @Test
  void isReal()
  {
    assertTrue(d_tm.getRealSort().isReal());
    assertTrue(!d_tm.getIntegerSort().isReal());
    assertDoesNotThrow(() -> new Sort().isReal());
  }

  @Test
  void isString()
  {
    assertTrue(d_tm.getStringSort().isString());
    assertDoesNotThrow(() -> new Sort().isString());
  }

  @Test
  void isRegExp()
  {
    assertTrue(d_tm.getRegExpSort().isRegExp());
    assertDoesNotThrow(() -> new Sort().isRegExp());
  }

  @Test
  void isRoundingMode() throws CVC5ApiException
  {
    assertTrue(d_tm.getRoundingModeSort().isRoundingMode());
    assertDoesNotThrow(() -> new Sort().isRoundingMode());
  }

  @Test
  void isBitVector() throws CVC5ApiException
  {
    assertTrue(d_tm.mkBitVectorSort(8).isBitVector());
    assertDoesNotThrow(() -> new Sort().isBitVector());
  }

  @Test
  void isFloatingPoint() throws CVC5ApiException
  {
    assertTrue(d_tm.mkFloatingPointSort(8, 24).isFloatingPoint());
    assertDoesNotThrow(() -> new Sort().isFloatingPoint());
  }

  @Test
  void isDatatype() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    assertTrue(dt_sort.isDatatype());
    assertDoesNotThrow(() -> new Sort().isDatatype());
  }

  @Test
  void isDatatypeConstructor() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getTerm().getSort();
    assertTrue(cons_sort.isDatatypeConstructor());
    assertDoesNotThrow(() -> new Sort().isDatatypeConstructor());
  }

  @Test
  void isDatatypeSelector() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getSelector(1).getTerm().getSort();
    assertTrue(cons_sort.isDatatypeSelector());
    assertDoesNotThrow(() -> new Sort().isDatatypeSelector());
  }

  @Test
  void isDatatypeTester() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getTesterTerm().getSort();
    assertTrue(cons_sort.isDatatypeTester());
    assertDoesNotThrow(() -> new Sort().isDatatypeTester());
  }

  @Test
  void isDatatypeUpdater() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort updater_sort = dt.getConstructor(0).getSelector(0).getUpdaterTerm().getSort();
    assertTrue(updater_sort.isDatatypeUpdater());
    assertDoesNotThrow(() -> new Sort().isDatatypeUpdater());
  }

  @Test
  void isFunction()
  {
    Sort fun_sort = d_tm.mkFunctionSort(d_tm.getRealSort(), d_tm.getIntegerSort());
    assertTrue(fun_sort.isFunction());
    assertDoesNotThrow(() -> new Sort().isFunction());
  }

  @Test
  void isPredicate()
  {
    Sort pred_sort = d_tm.mkPredicateSort(new Sort[] {d_tm.getRealSort()});
    assertTrue(pred_sort.isPredicate());
    assertDoesNotThrow(() -> new Sort().isPredicate());
  }

  @Test
  void isTuple()
  {
    Sort tup_sort = d_tm.mkTupleSort(new Sort[] {d_tm.getRealSort()});
    assertTrue(tup_sort.isTuple());
    assertDoesNotThrow(() -> new Sort().isTuple());
  }

  @Test
  void isNullable()
  {
    Sort sort = d_tm.mkNullableSort(d_tm.getRealSort());
    assertTrue(sort.isNullable());
    assertDoesNotThrow(() -> new Sort().isNullable());
  }

  @Test
  void isRecord()
  {
    Sort rec_sort =
        d_tm.mkRecordSort(new Pair[] {new Pair<String, Sort>("asdf", d_tm.getRealSort())});
    assertTrue(rec_sort.isRecord());
    assertDoesNotThrow(() -> new Sort().isRecord());
  }

  @Test
  void isArray()
  {
    Sort arr_sort = d_tm.mkArraySort(d_tm.getRealSort(), d_tm.getIntegerSort());
    assertTrue(arr_sort.isArray());
    assertDoesNotThrow(() -> new Sort().isArray());
  }

  @Test
  void isSet()
  {
    Sort set_sort = d_tm.mkSetSort(d_tm.getRealSort());
    assertTrue(set_sort.isSet());
    assertDoesNotThrow(() -> new Sort().isSet());
  }

  @Test
  void isBag()
  {
    Sort bag_sort = d_tm.mkBagSort(d_tm.getRealSort());
    assertTrue(bag_sort.isBag());
    assertDoesNotThrow(() -> new Sort().isBag());
  }

  @Test
  void isSequence()
  {
    Sort seq_sort = d_tm.mkSequenceSort(d_tm.getRealSort());
    assertTrue(seq_sort.isSequence());
    assertDoesNotThrow(() -> new Sort().isSequence());
  }

  @Test
  void isAbstract()
  {
    assertTrue(d_tm.mkAbstractSort(SortKind.BITVECTOR_SORT).isAbstract());
    // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
    // is an Array sort, not an abstract sort.
    assertFalse(d_tm.mkAbstractSort(SortKind.ARRAY_SORT).isAbstract());
    assertTrue(d_tm.mkAbstractSort(SortKind.ABSTRACT_SORT).isAbstract());
    assertDoesNotThrow(() -> new Sort().isAbstract());
  }

  @Test
  void isUninterpreted()
  {
    Sort un_sort = d_tm.mkUninterpretedSort("asdf");
    assertTrue(un_sort.isUninterpretedSort());
    assertDoesNotThrow(() -> new Sort().isUninterpretedSort());
  }

  @Test
  void isUninterpretedSortSortConstructor() throws CVC5ApiException
  {
    Sort sc_sort = d_tm.mkUninterpretedSortConstructorSort(1, "asdf");
    assertTrue(sc_sort.isUninterpretedSortConstructor());
    assertDoesNotThrow(() -> new Sort().isUninterpretedSortConstructor());
  }

  @Test
  void getDatatype() throws CVC5ApiException
  {
    Sort dtypeSort = create_datatype_sort();
    assertDoesNotThrow(() -> dtypeSort.getDatatype());
    // create bv sort, check should fail
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getDatatype());
  }

  @Test
  void datatypeSorts() throws CVC5ApiException
  {
    Sort intSort = d_tm.getIntegerSort();
    Sort dtypeSort = create_datatype_sort();
    Datatype dt = dtypeSort.getDatatype();
    assertFalse(dtypeSort.isDatatypeConstructor());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getDatatypeConstructorCodomainSort());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getDatatypeConstructorDomainSorts());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getDatatypeConstructorArity());

    // get constructor
    DatatypeConstructor dcons = dt.getConstructor(0);
    Term consTerm = dcons.getTerm();
    Sort consSort = consTerm.getSort();
    assertTrue(consSort.isDatatypeConstructor());
    assertFalse(consSort.isDatatypeTester());
    assertFalse(consSort.isDatatypeSelector());
    assertEquals(consSort.getDatatypeConstructorArity(), 2);
    Sort[] consDomSorts = consSort.getDatatypeConstructorDomainSorts();
    assertEquals(consDomSorts[0], intSort);
    assertEquals(consDomSorts[1], dtypeSort);
    assertEquals(consSort.getDatatypeConstructorCodomainSort(), dtypeSort);

    // get tester
    Term isConsTerm = dcons.getTesterTerm();
    assertTrue(isConsTerm.getSort().isDatatypeTester());
    assertEquals(isConsTerm.getSort().getDatatypeTesterDomainSort(), dtypeSort);
    Sort booleanSort = d_tm.getBooleanSort();
    assertEquals(isConsTerm.getSort().getDatatypeTesterCodomainSort(), booleanSort);
    assertThrows(CVC5ApiException.class, () -> booleanSort.getDatatypeTesterDomainSort());
    assertThrows(CVC5ApiException.class, () -> booleanSort.getDatatypeTesterCodomainSort());

    // get selector
    DatatypeSelector dselTail = dcons.getSelector(1);
    Term tailTerm = dselTail.getTerm();
    assertTrue(tailTerm.getSort().isDatatypeSelector());
    assertEquals(tailTerm.getSort().getDatatypeSelectorDomainSort(), dtypeSort);
    assertEquals(tailTerm.getSort().getDatatypeSelectorCodomainSort(), dtypeSort);
    assertThrows(CVC5ApiException.class, () -> booleanSort.getDatatypeSelectorDomainSort());
    assertThrows(CVC5ApiException.class, () -> booleanSort.getDatatypeSelectorCodomainSort());
  }

  @Test
  void instantiate() throws CVC5ApiException
  {
    // instantiate parametric datatype, check should not fail
    Sort paramDtypeSort = create_param_datatype_sort();
    assertDoesNotThrow(() -> paramDtypeSort.instantiate(new Sort[] {d_tm.getIntegerSort()}));
    // instantiate non-parametric datatype sort, check should fail
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
    assertThrows(
        CVC5ApiException.class, () -> dtypeSort.instantiate(new Sort[] {d_tm.getIntegerSort()}));
    // instantiate uninterpreted sort constructor
    Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(1, "s");
    assertDoesNotThrow(() -> sortConsSort.instantiate(new Sort[] {d_tm.getIntegerSort()}));
  }

  @Test
  void isInstantiated() throws CVC5ApiException
  {
    Sort paramDtypeSort = create_param_datatype_sort();
    assertFalse(paramDtypeSort.isInstantiated());
    Sort instParamDtypeSort = paramDtypeSort.instantiate(new Sort[] {d_tm.getIntegerSort()});
    assertTrue(instParamDtypeSort.isInstantiated());

    Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(1, "s");
    assertFalse(sortConsSort.isInstantiated());
    Sort instSortConsSort = sortConsSort.instantiate(new Sort[] {d_tm.getIntegerSort()});
    assertTrue(instSortConsSort.isInstantiated());

    assertFalse(d_tm.getIntegerSort().isInstantiated());
    assertFalse(d_tm.mkBitVectorSort(32).isInstantiated());
  }

  @Test
  void getInstantiatedParameters() throws CVC5ApiException
  {
    Sort intSort = d_tm.getIntegerSort();
    Sort realSort = d_tm.getRealSort();
    Sort boolSort = d_tm.getBooleanSort();
    Sort bvSort = d_tm.mkBitVectorSort(8);
    Sort[] instSorts;

    // parametric datatype instantiation
    Sort p1 = d_tm.mkParamSort("p1");
    Sort p2 = d_tm.mkParamSort("p2");
    DatatypeDecl pspec = d_tm.mkDatatypeDecl("pdtype", new Sort[] {p1, p2});
    DatatypeConstructorDecl pcons1 = d_tm.mkDatatypeConstructorDecl("cons1");
    DatatypeConstructorDecl pcons2 = d_tm.mkDatatypeConstructorDecl("cons2");
    DatatypeConstructorDecl pnil = d_tm.mkDatatypeConstructorDecl("nil");
    pcons1.addSelector("sel", p1);
    pcons2.addSelector("sel", p2);
    pspec.addConstructor(pcons1);
    pspec.addConstructor(pcons2);
    pspec.addConstructor(pnil);
    Sort paramDtypeSort = d_tm.mkDatatypeSort(pspec);

    assertThrows(CVC5ApiException.class, () -> paramDtypeSort.getInstantiatedParameters());

    Sort instParamDtypeSort = paramDtypeSort.instantiate(new Sort[] {realSort, boolSort});

    instSorts = instParamDtypeSort.getInstantiatedParameters();
    assertEquals(instSorts[0], realSort);
    assertEquals(instSorts[1], boolSort);

    // uninterpreted sort constructor sort instantiation
    Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(4, "s");
    assertThrows(CVC5ApiException.class, () -> sortConsSort.getInstantiatedParameters());

    Sort instSortConsSort =
        sortConsSort.instantiate(new Sort[] {boolSort, intSort, bvSort, realSort});

    instSorts = instSortConsSort.getInstantiatedParameters();
    assertEquals(instSorts[0], boolSort);
    assertEquals(instSorts[1], intSort);
    assertEquals(instSorts[2], bvSort);
    assertEquals(instSorts[3], realSort);

    assertThrows(CVC5ApiException.class, () -> intSort.getInstantiatedParameters());
    assertThrows(CVC5ApiException.class, () -> bvSort.getInstantiatedParameters());
  }

  @Test
  void getUninterpretedSortConstructor() throws CVC5ApiException
  {
    Sort intSort = d_tm.getIntegerSort();
    Sort realSort = d_tm.getRealSort();
    Sort boolSort = d_tm.getBooleanSort();
    Sort bvSort = d_tm.mkBitVectorSort(8);
    Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(4);
    assertThrows(CVC5ApiException.class, () -> sortConsSort.getUninterpretedSortConstructor());
    Sort instSortConsSort =
        sortConsSort.instantiate(new Sort[] {boolSort, intSort, bvSort, realSort});
    assertEquals(sortConsSort, instSortConsSort.getUninterpretedSortConstructor());
  }

  @Test
  void getFunctionArity() throws CVC5ApiException
  {
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionArity());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionArity());
  }

  @Test
  void getFunctionDomainSorts() throws CVC5ApiException
  {
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionDomainSorts());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionDomainSorts());
  }

  @Test
  void getFunctionCodomainSort() throws CVC5ApiException
  {
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionCodomainSort());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionCodomainSort());
  }

  @Test
  void getArrayIndexSort() throws CVC5ApiException
  {
    Sort elementSort = d_tm.mkBitVectorSort(32);
    Sort indexSort = d_tm.mkBitVectorSort(32);
    Sort arraySort = d_tm.mkArraySort(indexSort, elementSort);
    assertDoesNotThrow(() -> arraySort.getArrayIndexSort());
    assertThrows(CVC5ApiException.class, () -> indexSort.getArrayIndexSort());
  }

  @Test
  void getArrayElementSort() throws CVC5ApiException
  {
    Sort elementSort = d_tm.mkBitVectorSort(32);
    Sort indexSort = d_tm.mkBitVectorSort(32);
    Sort arraySort = d_tm.mkArraySort(indexSort, elementSort);
    assertDoesNotThrow(() -> arraySort.getArrayElementSort());
    assertThrows(CVC5ApiException.class, () -> indexSort.getArrayElementSort());
  }

  @Test
  void getSetElementSort() throws CVC5ApiException
  {
    Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
    assertDoesNotThrow(() -> setSort.getSetElementSort());
    Sort elementSort = setSort.getSetElementSort();
    assertEquals(elementSort, d_tm.getIntegerSort());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSetElementSort());
  }

  @Test
  void getBagElementSort() throws CVC5ApiException
  {
    Sort bagSort = d_tm.mkBagSort(d_tm.getIntegerSort());
    assertDoesNotThrow(() -> bagSort.getBagElementSort());
    Sort elementSort = bagSort.getBagElementSort();
    assertEquals(elementSort, d_tm.getIntegerSort());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getBagElementSort());
  }

  @Test
  void getSequenceElementSort() throws CVC5ApiException
  {
    Sort seqSort = d_tm.mkSequenceSort(d_tm.getIntegerSort());
    assertTrue(seqSort.isSequence());
    assertDoesNotThrow(() -> seqSort.getSequenceElementSort());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertFalse(bvSort.isSequence());
    assertThrows(CVC5ApiException.class, () -> bvSort.getSequenceElementSort());
  }

  @Test
  void getAbstractedKind() throws CVC5ApiException
  {
    assertEquals(
        d_tm.mkAbstractSort(SortKind.BITVECTOR_SORT).getAbstractedKind(), SortKind.BITVECTOR_SORT);
    // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
    // is an Array sort, not an abstract sort and its abstract kind cannot be
    // extracted.
    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkAbstractSort(SortKind.ARRAY_SORT).getAbstractedKind());
    assertEquals(
        d_tm.mkAbstractSort(SortKind.ABSTRACT_SORT).getAbstractedKind(), SortKind.ABSTRACT_SORT);
  }

  @Test
  void getSymbol() throws CVC5ApiException
  {
    Sort uSort = d_tm.mkUninterpretedSort("u");
    assertDoesNotThrow(() -> uSort.getSymbol());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSymbol());
  }

  @Test
  void getUninterpretedSortConstructorName() throws CVC5ApiException
  {
    Sort sSort = d_tm.mkUninterpretedSortConstructorSort(2);
    assertDoesNotThrow(() -> sSort.getSymbol());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSymbol());
  }

  @Test
  void getUninterpretedSortConstructorArity() throws CVC5ApiException
  {
    Sort sSort = d_tm.mkUninterpretedSortConstructorSort(2, "s");
    assertDoesNotThrow(() -> sSort.getUninterpretedSortConstructorArity());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getUninterpretedSortConstructorArity());
  }

  @Test
  void getBitVectorSize() throws CVC5ApiException
  {
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertDoesNotThrow(() -> bvSort.getBitVectorSize());
    Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getBitVectorSize());
  }

  @Test
  void getFloatingPointExponentSize() throws CVC5ApiException
  {
    Sort fpSort = d_tm.mkFloatingPointSort(4, 8);
    assertDoesNotThrow(() -> fpSort.getFloatingPointExponentSize());
    Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getFloatingPointExponentSize());
  }

  @Test
  void getFloatingPointSignificandSize() throws CVC5ApiException
  {
    Sort fpSort = d_tm.mkFloatingPointSort(4, 8);
    assertDoesNotThrow(() -> fpSort.getFloatingPointSignificandSize());
    Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getFloatingPointSignificandSize());
  }

  @Test
  void getDatatypeArity() throws CVC5ApiException
  {
    // create datatype sort, check should not fail
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
    assertDoesNotThrow(() -> dtypeSort.getDatatypeArity());
    // create bv sort, check should fail
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getDatatypeArity());
  }

  @Test
  void getTupleLength() throws CVC5ApiException
  {
    Sort tupleSort = d_tm.mkTupleSort(new Sort[] {d_tm.getIntegerSort(), d_tm.getIntegerSort()});
    assertDoesNotThrow(() -> tupleSort.getTupleLength());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getTupleLength());
  }

  @Test
  void getTupleSorts() throws CVC5ApiException
  {
    Sort tupleSort = d_tm.mkTupleSort(new Sort[] {d_tm.getIntegerSort(), d_tm.getIntegerSort()});
    assertDoesNotThrow(() -> tupleSort.getTupleSorts());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getTupleSorts());
  }

  @Test
  void getNullableElementSort() throws CVC5ApiException
  {
    Sort nullableSort = d_tm.mkNullableSort(d_tm.getIntegerSort());
    assertDoesNotThrow(() -> nullableSort.getNullableElementSort());
    Sort elementSort = nullableSort.getNullableElementSort();
    assertEquals(elementSort, d_tm.getIntegerSort());
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getNullableElementSort());
  }

  @Test
  void sortCompare() throws CVC5ApiException
  {
    Sort boolSort = d_tm.getBooleanSort();
    Sort intSort = d_tm.getIntegerSort();
    Sort bvSort = d_tm.mkBitVectorSort(32);
    Sort bvSort2 = d_tm.mkBitVectorSort(32);
    assertTrue(bvSort.compareTo(bvSort2) >= 0);
    assertTrue(bvSort.compareTo(bvSort2) <= 0);
    assertTrue(intSort.compareTo(boolSort) > 0 != intSort.compareTo(boolSort) < 0);
    assertTrue((intSort.compareTo(bvSort) > 0 || intSort.equals(bvSort))
        == (intSort.compareTo(bvSort) >= 0));
  }

  @Test
  void sortScopedToString() throws CVC5ApiException
  {
    String name = "uninterp-sort";
    Sort bvsort8 = d_tm.mkBitVectorSort(8);
    Sort uninterp_sort = d_tm.mkUninterpretedSort(name);
    assertEquals(bvsort8.toString(), "(_ BitVec 8)");
    assertEquals(uninterp_sort.toString(), name);
    Solver solver2;
    assertEquals(bvsort8.toString(), "(_ BitVec 8)");
    assertEquals(uninterp_sort.toString(), name);
  }

  @Test
  void sortSubstitute() throws CVC5ApiException
  {
    Sort sortVar0 = d_tm.mkParamSort("T0");
    Sort sortVar1 = d_tm.mkParamSort("T1");
    Sort intSort = d_tm.getIntegerSort();
    Sort realSort = d_tm.getRealSort();
    Sort arraySort0 = d_tm.mkArraySort(sortVar0, sortVar0);
    Sort arraySort1 = d_tm.mkArraySort(sortVar0, sortVar1);
    // Now create instantiations of the defined sorts
    assertDoesNotThrow(() -> arraySort0.substitute(sortVar0, intSort));
    assertDoesNotThrow(()
                           -> arraySort1.substitute(
                               new Sort[] {sortVar0, sortVar1}, new Sort[] {intSort, realSort}));
  }
}
