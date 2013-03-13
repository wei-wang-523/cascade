package edu.nyu.cascade.z3;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type.DomainType;
import edu.nyu.cascade.z3.BooleanExpressionImpl;
import edu.nyu.cascade.z3.BooleanTypeImpl;
import edu.nyu.cascade.z3.ExpressionManagerImpl;
import edu.nyu.cascade.z3.IntegerExpressionImpl;
import edu.nyu.cascade.z3.IntegerTypeImpl;
import edu.nyu.cascade.z3.IntegerVariableImpl;
import edu.nyu.cascade.z3.RationalTypeImpl;

public class ExpressionManagerTest {
  private TheoremProverImpl theoremProver;
  private ExpressionManagerImpl exprManager;
  private IntegerTypeImpl intType;
  private RationalTypeImpl ratType;
  private BooleanTypeImpl boolType;

  private void assertInvalid(Expression b) {
    assertTrue(theoremProver.checkValidity(b).isInvalid());
  }

  private void assertSat(Expression b) {
    assertTrue (theoremProver.checkSat(b).isSatisfiable());
  }

  private void assertUnsat(Expression b) {
    assertTrue (theoremProver.checkSat(b).isUnsatisfiable());
  }

  private void assertValid(Expression b) {
    assertTrue (theoremProver.checkValidity(b).isValid());
  }

  @Before
  public void setUp() {
    theoremProver = new TheoremProverImpl();
    exprManager = theoremProver.getExpressionManager();
    intType = exprManager.integerType();
    ratType = exprManager.rationalType();
    boolType = exprManager.booleanType();
  }

  @Test
  public void testArrayType() {
    ArrayType arrayType = exprManager.arrayType(
        intType, intType);
    assertEquals(DomainType.ARRAY, arrayType.getDomainType());
    assertEquals(intType, arrayType.getIndexType());
    assertEquals(intType, arrayType.getElementType());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testArrayType2() {
    // Cannot create a CVC array with boolean elements
    ArrayType arrayType2 = exprManager.arrayType(
        intType, boolType);
    assertEquals(DomainType.ARRAY, arrayType2.getDomainType());
    assertEquals(intType, arrayType2.getIndexType());
    assertEquals(boolType, arrayType2.getElementType());
  }

  @Test
  public void testBitVectorOne() {
    Expression one = exprManager.bitVectorOne(1);
    assertValid( exprManager.greaterThan(one, exprManager.bitVectorZero(1)) );
  }

  @Test
  public void testBitVectorOne2() {
    BitVectorExpression one = exprManager.bitVectorOne(8);
    assertEquals(8, one.getSize());
    assertEquals(8, one.getType().getSize());
    assertValid( exprManager.greaterThan(one, exprManager.bitVectorZero(8)) );
    assertValid( exprManager.lessThan(one, exprManager.bitVectorConstant(2,8)) );
  }

  @Test
  public void testBitVectorSlice() {
    VariableExpression bv = exprManager.variable("b",
        exprManager.bitVectorType(8), true);
    BitVectorExpression slice = exprManager.extract(bv, 0, 7);
    assertEquals(8, slice.getSize());

    slice = exprManager.extract(bv, 1, 5);
    assertEquals(5, slice.getSize());

    slice = exprManager.extract(bv, 6, 6);
    assertEquals(1, slice.getType().getSize());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testBitVectorSliceInverted() {
    VariableExpression bv = exprManager.variable("b",
        exprManager.bitVectorType(8), true);
    exprManager.extract(bv, 5, 0);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testBitVectorSliceOverflow() {
    VariableExpression bv = exprManager.variable("b",
        exprManager.bitVectorType(8), true);
    exprManager.extract(bv, 0, 8);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testBitVectorSliceUnderflow() {
    VariableExpression bv = exprManager.variable("b",
        exprManager.bitVectorType(8), true);
    exprManager.extract(bv, -1, 7);
  }

  @Test
  public void testConstructor() {
    Constructor foo = exprManager.constructor("foo");
    // assertEquals("foo",foo.getName());
    assertEquals(0, foo.getSelectors().size());
    Constructor foo2 = exprManager.constructor("foo");
    assertNotSame(foo, foo2);
  }

  @Test
  public void testConstructor2() {
    Selector x = exprManager.selector("x", intType);
    Selector y = exprManager.selector("y", boolType);
    Constructor foo = exprManager.constructor("foo", x, y);
    // assertEquals("foo",foo.getName());
    assertEquals(ImmutableList.of(x, y), foo.getSelectors());
    Constructor foo2 = exprManager.constructor("foo", x, y);
    assertNotSame(foo, foo2);
  }

  @Test
  public void testDatatype() {
    Constructor foo = exprManager.constructor("foo");
    Constructor bar = exprManager.constructor("bar");
    InductiveType t = exprManager.dataType("foobar", foo, bar);
    assertEquals("foobar", t.getName());
    ImmutableList<? extends Constructor> constrs = t.getConstructors();
    assertEquals(ImmutableList.of(foo, bar), constrs);
  }

  @Test
  public void testDatatype2() {
    Selector valueSelector = exprManager.selector("value",
        intType);

    Constructor okConstructor = exprManager.constructor("ok", valueSelector);

    InductiveType memType = exprManager.dataType("memory", okConstructor);
    assertNotNull(memType);
  }

  @Test
  public void testDatatype3() {
    ArrayType memArrayType = exprManager.arrayType(
        intType, intType);

    Selector valueSelector = exprManager
        .selector("value", memArrayType);

    Constructor okConstructor = exprManager.constructor("ok", valueSelector);

    InductiveType memType = exprManager.dataType("memory", okConstructor);
    assertNotNull(memType);
  }

  @Test
  public void testDatatype4() {
    ArrayType memArrayType = exprManager.arrayType(
        intType, intType);

    Selector valueSelector = exprManager
        .selector("value", memArrayType);

    Constructor okConstructor = exprManager.constructor("ok", valueSelector);
    Constructor bottomConstructor = exprManager.constructor("bottom");

    InductiveType memType = exprManager.dataType("memory", okConstructor,
        bottomConstructor);
    assertNotNull(memType);
  }

/** TheoremProverException is not captured in z3, unlike cvc3 */
//  @Test(expected = TheoremProverException.class)
  @Test(expected = IllegalArgumentException.class)
  public void testDatatype5() {
    Selector sel1 = exprManager.selector("val1", intType);
    Constructor constr1 = exprManager.constructor("mkT1", sel1);
    exprManager.dataType("T", constr1);
    Selector sel2 = exprManager.selector("val2", intType);
    Constructor constr2 = exprManager.constructor("mkT2", sel2);
    // Throws an exception because "T" is already defined
    exprManager.dataType("T", constr2);
  }

  @Test
  public void testDatatype6() {
    exprManager.integerVar("x", true);
    Selector sel1 = exprManager.selector("val1", intType);
    Constructor constr1 = exprManager.constructor("mkT1", sel1);
    exprManager.dataType("x", constr1);
  }

  /*
   * @SuppressWarnings("unchecked")
   * 
   * @Test public void testDatatype5() { final
   * String DATATYPE_NAME_0 = "Dn";
   * 
   * final String CONSTRUCTOR_NAME_0A = "dn0a"; final String TAG_SELECTOR_NAME =
   * "tag"; final String REST_SELECTOR_NAME_0A = "dn0a_rest";
   * 
   * final String CONSTRUCTOR_NAME_0B = "dn0b"; final String NULL_SELECTOR_NAME
   * = "nullt";
   * 
   * final String DATATYPE_NAME_1 = "Dn1";
   * 
   * final String CONSTRUCTOR_NAME_1A = "dn1a"; final String
   * LENGTH_SELECTOR_NAME = "len"; final String LABEL_SELECTOR_NAME = "label";
   * final String REST_SELECTOR_NAME_1A = "dn1a_rest";
   * 
   * final String CONSTRUCTOR_NAME_1B = "dn1b"; final String
   * OFFSET_SELECTOR_NAME = "offset";
   * 
   * final IInductiveType dn; final IInductiveType dn0; final IConstructor
   * constr0a; final IConstructor constr0b, constr1a, constr1b; final
   * ISelector tagSel; final ISelector nullSel,
   * lenSel, offsetSel; final ISelector<IArrayType<IBitVectorType,
   * IBitVectorType>> labelSel; final ISelector restSel0a; final
   * ISelector restSel1a;
   * 
   * IBitVectorType wordType = exprManager.bitVectorType(32); IBitVectorType
   * shortType = exprManager.bitVectorType(16); IBitVectorType charType =
   * exprManager.bitVectorType(8); IBitVectorType lenType =
   * exprManager.bitVectorType(6); IBitVectorType tagType =
   * exprManager.bitVectorType(2); IBitVectorType offsetType =
   * exprManager.bitVectorType(14);
   * 
   * IArrayType memType =
   * exprManager.arrayType(wordType, charType); IArrayType<IBitVectorType,
   * IBitVectorType> stringType = memType;
   * 
   * Create datatype constructors
   * 
   * tagSel = exprManager.selector(TAG_SELECTOR_NAME, tagType); restSel0a =
   * exprManager.selector(REST_SELECTOR_NAME_0A, exprManager
   * .inductiveTypeDescriptor(DATATYPE_NAME_1)); constr0a =
   * exprManager.constructor(CONSTRUCTOR_NAME_0A, tagSel, restSel0a);
   * 
   * nullSel = exprManager.selector(NULL_SELECTOR_NAME, charType); constr0b =
   * exprManager.constructor(CONSTRUCTOR_NAME_0B, nullSel);
   * 
   * lenSel = exprManager.selector(LENGTH_SELECTOR_NAME, lenType); labelSel =
   * exprManager.selector(LABEL_SELECTOR_NAME, stringType); restSel1a =
   * exprManager.selector(REST_SELECTOR_NAME_1A, exprManager
   * .inductiveTypeDescriptor(DATATYPE_NAME_0)); constr1a =
   * exprManager.constructor(CONSTRUCTOR_NAME_1A, lenSel, labelSel,restSel1a);
   * 
   * offsetSel = exprManager.selector(OFFSET_SELECTOR_NAME, offsetType);
   * constr1b = exprManager.constructor(CONSTRUCTOR_NAME_1B, offsetSel);
   * 
   * Create datatypes
   * 
   * List<IConstructor> dnConstr = ImmutableList.of(constr0a, constr0b);
   * List<IConstructor> dn0Constr = ImmutableList.of(constr1a, constr1b);
   * 
   * List<? extends IInductiveType> types = exprManager.dataTypes(
   * ImmutableList.of(DATATYPE_NAME_0, DATATYPE_NAME_1), dnConstr, dn0Constr );
   * assertTrue( types.size() == 2 ); dn = types.get(0); assertEquals( dnConstr,
   * dn.getConstructors() );
   * 
   * dn0 = types.get(1); assertEquals( dn0Constr, dn0.getConstructors() );
   * 
   * IVariableExpression xDn = dn.newVariable("x");
   * IVariableExpression s =
   * stringType .newVariable("s"); IVariableExpression wBv1 =
   * wordType.newVariable("w1"); IVariableExpression wBv2 =
   * wordType.newVariable("w2");
   * 
   * 
   * assertEquals( dn0, exprManager.selectExpression( restSel0a, xDn).getType()
   * ); assertTrue FORALL (x : Dn) : is_dn0a(x) AND tag(x) = 0bin00 =>
   * is_dn1a(dn0a_rest(x)) IExpression tagAxiom0 =
   * exprManager.forall( ImmutableList.of(xDn),
   * exprManager.impliesExpression(
   * exprManager.andExpression(exprManager.testExpression(constr0a, xDn),
   * exprManager.eqExpression(exprManager.selectExpression(tagSel, xDn),
   * exprManager.bitVectorConstant("00"))), exprManager.testExpression(constr1a,
   * exprManager.selectExpression( restSel0a, xDn)))); }
   */

  @Test
  public void testFf() {
    BooleanExpressionImpl ff = exprManager.ff();
    assertUnsat(ff);
    assertInvalid(ff);
  }

  @Test
  public void testForallExpr() {
    VariableExpression x = exprManager.integerVar("x", true);
    assertInvalid(exprManager.forall(ImmutableList.of(x), exprManager
        .greaterThan(x, exprManager.zero())));
  }

  @Test
  public void testForallExpr2() {
    VariableExpression var_x = exprManager.integerVar("x", true);
    VariableExpression var_y = exprManager.integerVar("y", true);

    Expression x = exprManager.boundExpression(1, intType);
    Expression y = exprManager.boundExpression(0, intType);
    
    FunctionType f = exprManager.functionType("f", intType, intType);
    
    Expression fx = exprManager.applyExpr(f, x);
    Expression fy = exprManager.applyExpr(f, y);

    // Using a trigger
    
    List<? extends Expression> triggers = ImmutableList.of(fx, fy);
    BooleanExpression b = exprManager.forall(ImmutableList.of(var_x, var_y), x.eq(
        y).implies(fx.eq(fy)), triggers);

    assertValid(b);
    
    // Compare triggers
    assertEquals(Lists.transform(triggers, new Function<Expression, 
        ImmutableList<Expression>>(){
      @Override
      public ImmutableList<Expression> apply(Expression e) {
        return ImmutableList.of(e);
      }}), b.getTriggers());
  }

  @Test
  public void testFunctionApplication() {
    // assume forall x : f(x) == x
    VariableExpression x_var = exprManager.integerVar("x", true);
    
    Expression x = exprManager.boundExpression(0, intType);
    FunctionType f = exprManager.functionType("f", intType, intType);
    Expression fx = exprManager.applyExpr(f, x);
    Expression axiom = exprManager.forall(x_var, fx.eq(x)); // f(x) = x
    
    exprManager.getTheoremProver().assume(axiom);
    
    // check if f(y) == y
    VariableExpression y = exprManager.integerVar("y", true);
    Expression fy = exprManager.applyExpr(f, y);
    assertValid(fy.eq(y));
  }

  @Test
  public void testFunctionApplication2() {
    VariableExpression x = exprManager.integerVar("x", true);
    VariableExpression y = exprManager.integerVar("y", true);

    FunctionType f = exprManager.functionType("f", intType, intType);
    Expression fx = exprManager.applyExpr(f, x);
    Expression fy = exprManager.applyExpr(f, y);

    assertValid(x.eq(y).implies(fx.eq(fy)));
  }

  @Test
  public void testIntegerConstants() {
    Expression negOne = exprManager.negativeOne();
    Expression one = exprManager.one();
    Expression zero = exprManager.zero();
    IntegerExpressionImpl two = exprManager.constant(2);

    assertValid(exprManager.eq(zero, zero)); // 0==0
    assertInvalid(exprManager.eq(zero, one)); // 0=/=1
    assertValid(exprManager.greaterThan(one, zero)); // 1 > 0
    assertValid(exprManager.lessThan(negOne, zero)); // -1 < 0
    assertValid(exprManager.greaterThan(two, one)); // 2 > 1
    assertValid(exprManager.eq(two, exprManager.plus(one, one))); // 2==1+1
    assertValid(exprManager.eq(exprManager.negate(one), negOne)); // -(1)
                                                                                // ==
                                                                                // (-1)

    IntegerVariableImpl x = exprManager.integerVar("x", true);
    assertValid(exprManager.eq(exprManager.plus(zero, x), x)); // 0
                                                                             // +
                                                                             // x
                                                                             // ==
                                                                             // x
    assertValid(exprManager.eq(exprManager.mult(zero, x), zero)); // 0
                                                                                // *
                                                                                // x
                                                                                // ==
                                                                                // 0
    assertValid(exprManager.eq(exprManager.mult(one, x), x)); // 1
                                                                            // *
                                                                            // x
                                                                            // ==
                                                                            // x
    assertValid(exprManager.eq(exprManager.mult(negOne, x),
        exprManager.negate(x))); // -1 * x == -x

    assertValid(exprManager.eq(exprManager.minus(x, x), zero)); // x
                                                                              // -
                                                                              // x
                                                                              // ==
                                                                              // 0

    /*
     * // divide isn't implemented yet
     * assertValid(exprManager.eqExpression(exprManager.divideExpr(zero, x),
     * zero)); // 0 / x == 0
     * assertValid(exprManager.eqExpression(exprManager.divideExpr(x, x), one));
     * // x / x == 1
     * assertValid(exprManager.eqExpression(exprManager.divideExpr(exprManager
     * .unaryMinusExpr(x), x), negOne)); // -x / x == -1
     */
    assertValid(exprManager.eq(exprManager.plus(x, exprManager
        .negate(x)), zero)); // x + -x == 0
    assertValid(exprManager.eq(exprManager.mult(negOne, negOne),
        one)); // -1 * -1 == 1
    assertValid(exprManager.eq(exprManager.minus(zero, x),
        exprManager.negate(x))); // 0 - x == -x
  }

  @Ignore
  @Test
  public void testLambda() {
    VariableExpression x = exprManager.integerVar("x", true);
    exprManager.lambda(x, x);
  }

  @SuppressWarnings("unchecked")
  @Test
  public void testRecursiveDatatypes() {
    InductiveType t2Stub = exprManager.inductiveType("t2");
    Selector s1 = exprManager.selector("s1", t2Stub, 1);
    Constructor c1 = exprManager.constructor("c1", s1);

    InductiveType t1Stub = exprManager.inductiveType("t1");
    Selector s2 = exprManager.selector("s2", t1Stub, 1);
    Constructor c2 = exprManager.constructor("c2", s2);
    Constructor c3 = exprManager.constructor("c3"); // important: this is the
                                                     // base case!

    ImmutableList<? extends InductiveType> ts = exprManager.dataTypes(
        ImmutableList.of("t1", "t2"), ImmutableList.of(c1), ImmutableList.of(
            c2, c3));

    assertEquals(2, ts.size());
    InductiveType t1 = ts.get(0);
    InductiveType t2 = ts.get(1);

    // assertEquals("t1",t1.getName());
    assertEquals(ImmutableList.of(c1), t1.getConstructors());
    // assertEquals("t2",t2.getName());
    assertEquals(ImmutableList.of(c2, c3), t2.getConstructors());

    assertEquals(t1, s2.getType());
    assertEquals(t2, s1.getType());
  }

  /** (expected=TheoremProverException.class), this time CVC won't barf, 
   * consturctor's name is made unique in Cascade.
   */
  @SuppressWarnings("unchecked")
  @Test
  public void testRecursiveDatatypes2() {
    /*
     * We re-use ids for selectors and constructors, which will make CVC barf.
     */
    InductiveType t2Stub = exprManager.inductiveType("t2");
    Selector s1 = exprManager.selector("s", t2Stub, 1);
    Constructor c1 = exprManager.constructor("c", s1);

    InductiveType t1Stub = exprManager.inductiveType("t1");
    Selector s2 = exprManager.selector("s", t1Stub, 1);
    Constructor c2 = exprManager.constructor("c", s2);
    Constructor c3 = exprManager.constructor("c2"); // important: this is the
                                                     // base case!

    exprManager.dataTypes(
        ImmutableList.of("t1", "t2"), ImmutableList.of(c1), ImmutableList.of(
            c2, c3));

  }

  @Test
  public void testSelector() {
    Selector x = exprManager.selector("x", intType);
    // assertEquals("x",x.getName());
    assertEquals(intType, x.getType());

    Selector x2 = exprManager.selector("x", intType);
    // assertEquals("x",x.getName());
    assertNotSame(x, x2);

    Selector y = exprManager.selector("y", boolType);
    // assertEquals("y",y.getName());
    assertEquals(boolType, y.getType());

    InductiveType t1Stub = exprManager.inductiveType("t1");
    Selector s1 = exprManager.selector("s1", t1Stub, 1);
    // assertEquals("s1",s1.getName());
    assertEquals(t1Stub, s1.getType()); // null != null
  }

  @Test
  public void testTt() {
    BooleanExpressionImpl tt = exprManager.tt();
    assertSat(tt);
    assertValid(tt);
  }

  @Test
  public void testTuple() {
    Expression one = exprManager.one();
    Expression two = exprManager.constant(2);
    Expression three = exprManager.constant(3);
    Expression half = exprManager.rationalConstant(1, 2);

    /** Tuple expression must have more than one child */
/*    TupleExpression tuple = exprManager.tuple(one);
    assertEquals(ImmutableList.of(one), tuple.getChildren());
    assertEquals(ImmutableList.of(intType), tuple.getType().getElementTypes());*/
    
    TupleType tupleType_2 = exprManager.tupleType("tuple_int_2", intType, intType);
    TupleExpression tuple = exprManager.tuple(tupleType_2, one, two);
    assertEquals(ImmutableList.of(one, two), tuple.getChildren());
    assertEquals(ImmutableList.of(intType, intType), tuple
        .getType()
        .getElementTypes());

    TupleType tupleType_3 = exprManager.tupleType("tuple_iri_3", intType, ratType, intType);
    tuple = exprManager.tuple(tupleType_3, three, half, one);
    assertEquals(ImmutableList.of(three, half, one), tuple.getChildren());
    assertEquals(ImmutableList.of(intType, ratType, intType), tuple
        .getType()
        .getElementTypes());
  }

  @Test
  public void testTupleType() {
    /** Tuple type must have more than one child */
/*    TupleType tupleType = exprManager.tupleType(intType);
    assertEquals(ImmutableList.of(intType), tupleType.getElementTypes());*/

    TupleType tupleType_2 = exprManager.tupleType("tuple_int_2", intType, intType);
    assertEquals(ImmutableList.of(intType, intType), tupleType_2
        .getElementTypes());

    TupleType tupleType_3 = exprManager.tupleType("tuple_rir_3", ratType, intType, ratType);
    assertEquals(ImmutableList.of(ratType, intType, ratType), tupleType_3
        .getElementTypes());
  }

  @Test
  public void testVarIntegerExpression() {
    VariableExpression x = exprManager.integerVar("x", true);
    assertEquals(intType, x.getType());
  }

  @Test
  public void testVarIntegerExpression2() {
    VariableExpression x = exprManager.integerVar("x", true);
    VariableExpression x2 = exprManager
        .integerVar("x", true);
    assertTrue (!x.equals(x2));
  }
}
