/******************************************************************************
 * Top contributors (to current version):
 *   Andrew V. Jones, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Two tests to validate the use of the separation logic API.
 *
 * First test validates that we cannot use the API if not using separation
 * logic.
 *
 * Second test validates that the expressions returned from the API are
 * correct and can be interrogated.
 *
 ****************************************************************************/

#include <cvc5/cvc5.h>

using namespace cvc5;
using namespace std;

/**
 * Test function to validate that we *cannot* obtain the heap/nil expressions
 * when *not* using the separation logic theory
 */
int validate_exception(void)
{
  TermManager tm;
  Solver slv(tm);

  /*
   * Setup some options for cvc5 -- we explictly want to use a simplistic
   * theory (e.g., QF_IDL)
   */
  slv.setLogic("QF_IDL");
  slv.setOption("produce-models", "true");
  slv.setOption("incremental", "false");

  /* Our integer type */
  Sort integer = tm.getIntegerSort();

  /** we intentionally do not set the separation logic heap */

  /* Our SMT constants */
  Term x = tm.mkConst(integer, "x");
  Term y = tm.mkConst(integer, "y");

  /* y > x */
  Term y_gt_x(tm.mkTerm(Kind::GT, {y, x}));

  /* assert it */
  slv.assertFormula(y_gt_x);

  /* check */
  Result r(slv.checkSat());

  /* If this is UNSAT, we have an issue; so bail-out */
  if (!r.isSat())
  {
    return -1;
  }

  /*
   * We now try to obtain our separation logic expressions from the solver --
   * we want to validate that we get our expected exceptions.
   */
  bool caught_on_heap(false);
  bool caught_on_nil(false);

  /* The exception message we expect to obtain */
  std::string expected(
      "cannot obtain separation logic expressions if not using the separation "
      "logic theory.");

  /* test the heap expression */
  try
  {
    Term heap_expr = slv.getValueSepHeap();
  }
  catch (const CVC5ApiException& e)
  {
    caught_on_heap = true;

    /* Check we get the correct exception string */
    if (e.what() != expected)
    {
      return -1;
    }
  }

  /* test the nil expression */
  try
  {
    Term nil_expr = slv.getValueSepNil();
  }
  catch (const CVC5ApiException& e)
  {
    caught_on_nil = true;

    /* Check we get the correct exception string */
    if (e.what() != expected)
    {
      return -1;
    }
  }

  if (!caught_on_heap || !caught_on_nil)
  {
    return -1;
  }

  /* All tests pass! */
  return 0;
}

/**
 * Test function to demonstrate the use of, and validate the capability, of
 * obtaining the heap/nil expressions when using separation logic.
 */
int validate_getters(void)
{
  TermManager tm;
  Solver slv(tm);

  /* Setup some options for cvc5 */
  slv.setLogic("QF_ALL");
  slv.setOption("produce-models", "true");
  slv.setOption("incremental", "false");

  /* Our integer type */
  Sort integer = tm.getIntegerSort();

  /** Declare the separation logic heap types */
  slv.declareSepHeap(integer, integer);

  /* A "random" constant */
  Term random_constant = tm.mkInteger(0xDEADBEEF);

  /* Another random constant */
  Term expr_nil_val = tm.mkInteger(0xFBADBEEF);

  /* Our nil term */
  Term nil = tm.mkSepNil(integer);

  /* Our SMT constants */
  Term x = tm.mkConst(integer, "x");
  Term y = tm.mkConst(integer, "y");
  Term p1 = tm.mkConst(integer, "p1");
  Term p2 = tm.mkConst(integer, "p2");

  /* Constraints on x and y */
  Term x_equal_const = tm.mkTerm(Kind::EQUAL, {x, random_constant});
  Term y_gt_x = tm.mkTerm(Kind::GT, {y, x});

  /* Points-to expressions */
  Term p1_to_x = tm.mkTerm(Kind::SEP_PTO, {p1, x});
  Term p2_to_y = tm.mkTerm(Kind::SEP_PTO, {p2, y});

  /* Heap -- the points-to have to be "starred"! */
  Term heap = tm.mkTerm(Kind::SEP_STAR, {p1_to_x, p2_to_y});

  /* Constain "nil" to be something random */
  Term fix_nil = tm.mkTerm(Kind::EQUAL, {nil, expr_nil_val});

  /* Add it all to the solver! */
  slv.assertFormula(x_equal_const);
  slv.assertFormula(y_gt_x);
  slv.assertFormula(heap);
  slv.assertFormula(fix_nil);

  /*
   * Incremental is disabled due to using separation logic, so don't query
   * twice!
   */
  Result r(slv.checkSat());

  /* If this is UNSAT, we have an issue; so bail-out */
  if (!r.isSat())
  {
    return -1;
  }

  /* Obtain our separation logic terms from the solver */
  Term heap_expr = slv.getValueSepHeap();
  Term nil_expr = slv.getValueSepNil();

  /* If the heap is not a separating conjunction, bail-out */
  if (heap_expr.getKind() != Kind::SEP_STAR)
  {
    return -1;
  }

  /* If nil is not a direct equality, bail-out */
  if (nil_expr.getKind() != Kind::EQUAL)
  {
    return -1;
  }

  /* Obtain the values for our "pointers" */
  Term val_for_p1 = slv.getValue(p1);
  Term val_for_p2 = slv.getValue(p2);

  /* We need to make sure we find both pointers in the heap */
  bool checked_p1(false);
  bool checked_p2(false);

  /* Walk all the children */
  for (const Term& child : heap_expr)
  {
    /* If we don't have a PTO operator, bail-out */
    if (child.getKind() != Kind::SEP_PTO)
    {
      return -1;
    }

    /* Find both sides of the PTO operator */
    Term addr = slv.getValue(child[0]);
    Term value = slv.getValue(child[1]);

    /* If the current address is the value for p1 */
    if (addr == val_for_p1)
    {
      checked_p1 = true;

      /* If it doesn't match the random constant, we have a problem */
      if (value != random_constant)
      {
        return -1;
      }
      continue;
    }

    /* If the current address is the value for p2 */
    if (addr == val_for_p2)
    {
      checked_p2 = true;

      /*
       * Our earlier constraint was that what p2 points to must be *greater*
       * than the random constant -- if we get a value that is LTE, then
       * something has gone wrong!
       */
      if (value.getInt64Value() <= random_constant.getInt64Value())
      {
        return -1;
      }
      continue;
    }

    /*
     * We should only have two addresses in heap, so if we haven't hit the
     * "continue" for p1 or p2, then bail-out
     */
    return -1;
  }

  /*
   * If we complete the loop and we haven't validated both p1 and p2, then we
   * have a problem
   */
  if (!checked_p1 || !checked_p2)
  {
    return -1;
  }

  /* We now get our value for what nil is */
  Term value_for_nil = slv.getValue(nil_expr[1]);

  /*
   * The value for nil from the solver should be the value we originally tied
   * nil to
   */
  if (value_for_nil != expr_nil_val)
  {
    return -1;
  }

  /* All tests pass! */
  return 0;
}

int main(void)
{
  /* check that we get an exception when we should */
  int check_exception(validate_exception());

  if (check_exception)
  {
    return check_exception;
  }

  /* check the getters */
  int check_getters(validate_getters());

  if (check_getters)
  {
    return check_getters;
  }

  return 0;
}
