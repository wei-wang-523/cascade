package edu.nyu.cascade.cvc4;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.FunctionType;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type.DomainType;
import edu.nyu.cascade.util.IOUtils;

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
		assertTrue(theoremProver.checkSat(b).isSatisfiable());
	}

	private void assertUnsat(Expression b) {
		assertTrue(theoremProver.checkSat(b).isUnsatisfiable());
	}

	private void assertValid(Expression b) {
		assertTrue(theoremProver.checkValidity(b).isValid());
	}

	private void assume(Expression b) {
		theoremProver.assume(b);
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
		ArrayType arrayType = exprManager.arrayType(intType, intType);
		assertEquals(DomainType.ARRAY, arrayType.getDomainType());
		assertEquals(intType, arrayType.getIndexType());
		assertEquals(intType, arrayType.getElementType());
	}

	@Test
	public void testArrayType2() {
		// Cannot create a CVC array with boolean elements
		ArrayType arrayType2 = exprManager.arrayType(intType, boolType);
		assertEquals(DomainType.ARRAY, arrayType2.getDomainType());
		assertEquals(intType, arrayType2.getIndexType());
		assertEquals(boolType, arrayType2.getElementType());
	}

	@Test
	public void testBitVectorOne() {
		Expression one = exprManager.bitVectorOne(1);
		assertValid(exprManager.greaterThan(one, exprManager.bitVectorZero(1)));
	}

	@Test
	public void testBitVectorOne2() {
		BitVectorExpression one = exprManager.bitVectorOne(8);
		assertEquals(8, one.getSize());
		assertEquals(8, one.getType().getSize());
		assertValid(exprManager.greaterThan(one, exprManager.bitVectorZero(8)));
		assertValid(exprManager.lessThan(one, exprManager.bitVectorConstant(2, 8)));
	}

	@Test
	public void testBitVectorSlice() {
		VariableExpression bv = exprManager.variable("b", exprManager.bitVectorType(
		    8), true);
		BitVectorExpression slice = exprManager.extract(bv, 0, 7);
		assertEquals(8, slice.getSize());

		slice = exprManager.extract(bv, 1, 5);
		assertEquals(5, slice.getSize());

		slice = exprManager.extract(bv, 6, 6);
		assertEquals(1, slice.getType().getSize());
	}

	@Test
	public void testBitVectorExtend() {
		VariableExpression bv = exprManager.variable("b", exprManager.bitVectorType(
		    8), true);
		BitVectorExpression slice = exprManager.signedExtend(8, bv);
		assertEquals(8, slice.getSize());

		slice = exprManager.signedExtend(10, bv);
		assertEquals(10, slice.getSize());

		slice = exprManager.zeroExtend(10, bv);
		assertEquals(10, slice.getSize());
	}

	@Test
	public void testBitVectorPlus() {
		Expression bv1 = exprManager.variable("bv1", exprManager.bitVectorType(64),
		    true);
		Expression bv2 = exprManager.bitVectorConstant(1, 32);

		BitVectorExpression sum = exprManager.bitVectorPlus(64, bv1, bv2);
		assertEquals(64, sum.getSize());
	}

	@Test
	public void testBitVectorMinus() {
		Expression bv1 = exprManager.variable("bv1", exprManager.bitVectorType(64),
		    true);
		Expression bv2 = exprManager.bitVectorConstant(1, 32);

		BitVectorExpression res = exprManager.bitVectorMinus(bv1, bv2);
		assertEquals(64, res.getSize());
	}

	@Test
	public void testBitVectorMult() {
		VariableExpression bv1 = exprManager.variable("bv1", exprManager
		    .bitVectorType(4), true);
		VariableExpression bv2 = exprManager.variable("bv2", exprManager
		    .bitVectorType(8), true);

		BitVectorExpression res = exprManager.bitVectorMult(4, bv1, bv2);
		assertEquals(4, res.getSize());
	}

	@Test
	public void testBitVectorShift() {
		VariableExpression bv1 = exprManager.variable("bv1", exprManager
		    .bitVectorType(8), true);
		BitVectorExpression bv2 = exprManager.bitVectorConstant(2);

		BitVectorExpression res = bv1.asBitVector().lshift(bv2);
		assertEquals(8, res.getSize());

		res = bv1.asBitVector().rshift(bv2);
		assertEquals(8, res.getSize());

		res = bv1.asBitVector().signedRshift(bv2);
		assertEquals(8, res.getSize());
	}

	@Test
	public void testBitVectorDivide() {
		VariableExpression bv1 = exprManager.variable("bv1", exprManager
		    .bitVectorType(8), true);
		BitVectorExpression bv2 = exprManager.bitVectorConstant(2);

		BitVectorExpression res = bv1.asBitVector().divides(bv2);
		assertEquals(8, res.asBitVector().getSize());

		res = bv1.asBitVector().signedDivides(bv2);
		assertEquals(8, res.asBitVector().getSize());
	}

	@Test
	public void testBitVectorRem() {
		VariableExpression bv1 = exprManager.variable("bv1", exprManager
		    .bitVectorType(8), true);
		BitVectorExpression bv2 = exprManager.bitVectorConstant(2);

		BitVectorExpression res = bv1.asBitVector().rems(bv2);
		assertEquals(8, res.asBitVector().getSize());

		res = bv1.asBitVector().signedRems(bv2);
		assertEquals(8, res.asBitVector().getSize());
	}

	@Test
	public void testBitVectorConcact() {
		VariableExpression bv1 = exprManager.variable("bv1", exprManager
		    .bitVectorType(8), true);
		BitVectorExpression bv2 = exprManager.bitVectorConstant(2);

		BitVectorExpression res = exprManager.concat(bv1, bv2);
		assertEquals(10, res.asBitVector().getSize());
	}

	@Test(expected = IllegalArgumentException.class)
	public void testBitVectorSliceInverted() {
		VariableExpression bv = exprManager.variable("b", exprManager.bitVectorType(
		    8), true);
		exprManager.extract(bv, 5, 0);
	}

	@Test(expected = IllegalArgumentException.class)
	public void testBitVectorSliceOverflow() {
		VariableExpression bv = exprManager.variable("b", exprManager.bitVectorType(
		    8), true);
		exprManager.extract(bv, 0, 8);
	}

	@Test(expected = IllegalArgumentException.class)
	public void testBitVectorSliceUnderflow() {
		VariableExpression bv = exprManager.variable("b", exprManager.bitVectorType(
		    8), true);
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
		Selector valueSelector = exprManager.selector("value", intType);

		Constructor okConstructor = exprManager.constructor("ok", valueSelector);

		InductiveType memType = exprManager.dataType("memory", okConstructor);
		assertNotNull(memType);
	}

	@Test
	public void testDatatype3() {
		ArrayType memArrayType = exprManager.arrayType(intType, intType);

		Selector valueSelector = exprManager.selector("value", memArrayType);

		Constructor okConstructor = exprManager.constructor("ok", valueSelector);

		InductiveType memType = exprManager.dataType("memory", okConstructor);
		assertNotNull(memType);
	}

	@Test
	public void testDatatype4() {
		ArrayType memArrayType = exprManager.arrayType(intType, intType);

		Selector valueSelector = exprManager.selector("value", memArrayType);

		Constructor okConstructor = exprManager.constructor("ok", valueSelector);
		Constructor bottomConstructor = exprManager.constructor("bottom");

		InductiveType memType = exprManager.dataType("memory", okConstructor,
		    bottomConstructor);
		assertNotNull(memType);
	}

	/** TheoremProverException is not captured in cvc4, unlike cvc3 */
	// @Test(expected = TheoremProverException.class)
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
		Selector sel1 = exprManager.selector("val1", intType);
		Constructor constr1 = exprManager.constructor("mkT1", sel1);
		exprManager.dataType("x", constr1);
	}

	/*
	 * @SuppressWarnings("unchecked")
	 * 
	 * @Test public void testDatatype5() { final String DATATYPE_NAME_0 = "Dn";
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
	 * constr0a; final IConstructor constr0b, constr1a, constr1b; final ISelector
	 * tagSel; final ISelector nullSel, lenSel, offsetSel; final
	 * ISelector<IArrayType<IBitVectorType, IBitVectorType>> labelSel; final
	 * ISelector restSel0a; final ISelector restSel1a;
	 * 
	 * IBitVectorType wordType = exprManager.bitVectorType(32); IBitVectorType
	 * shortType = exprManager.bitVectorType(16); IBitVectorType charType =
	 * exprManager.bitVectorType(8); IBitVectorType lenType =
	 * exprManager.bitVectorType(6); IBitVectorType tagType =
	 * exprManager.bitVectorType(2); IBitVectorType offsetType =
	 * exprManager.bitVectorType(14);
	 * 
	 * IArrayType memType = exprManager.arrayType(wordType, charType);
	 * IArrayType<IBitVectorType, IBitVectorType> stringType = memType;
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
	 * IVariableExpression xDn = dn.newVariable("x"); IVariableExpression s =
	 * stringType .newVariable("s"); IVariableExpression wBv1 =
	 * wordType.newVariable("w1"); IVariableExpression wBv2 =
	 * wordType.newVariable("w2");
	 * 
	 * 
	 * assertEquals( dn0, exprManager.selectExpression( restSel0a, xDn).getType()
	 * ); assertTrue FORALL (x : Dn) : is_dn0a(x) AND tag(x) = 0bin00 =>
	 * is_dn1a(dn0a_rest(x)) IExpression tagAxiom0 = exprManager.forall(
	 * ImmutableList.of(xDn), exprManager.impliesExpression(
	 * exprManager.andExpression(exprManager.testExpression(constr0a, xDn),
	 * exprManager.eqExpression(exprManager.selectExpression(tagSel, xDn),
	 * exprManager.bitVectorConstant("00"))), exprManager.testExpression(constr1a,
	 * exprManager.selectExpression( restSel0a, xDn)))); }
	 */

	@Test
	public void testFf() {
		BooleanExpression ff = exprManager.ff();
		assertUnsat(ff);
		assertInvalid(ff);
	}

	@Test
	public void testForallExpr() {
		BoundExpression x = intType.boundVar("x", true);
		assertInvalid(exprManager.forall(ImmutableList.of(x), exprManager
		    .greaterThan(x, exprManager.zero())));
	}

	@Test
	public void testCVC4Expr() {
		ExprManager em = exprManager.getTheoremProver().getCvc4ExprManager();
		Expr p = em.mkBoundVar("p", em.integerType());
		FunctionType funcType = em.mkFunctionType(em.integerType(), em
		    .booleanType());
		Expr isGood = em.mkVar("f", funcType);
		Expr body = em.mkExpr(Kind.APPLY_UF, isGood, p);
		vectorExpr varList = new vectorExpr();
		varList.add(p);
		Expr boundVarList = em.mkExpr(Kind.BOUND_VAR_LIST, varList);
		Expr qTerm = em.mkExpr(Kind.EXISTS, boundVarList, body);

		FunctionType funcType2 = em.mkFunctionType(em.integerType(), em
		    .booleanType());
		Expr isBad = em.mkVar("g", funcType2);
		Expr body2 = em.mkExpr(Kind.APPLY_UF, isBad, p);
		Expr qTerm2 = em.mkExpr(Kind.EXISTS, boundVarList, body2);

		IOUtils.err().println(exprManager.getTheoremProver().getSmtEngine()
		    .checkSat(qTerm));
		IOUtils.err().println(exprManager.getTheoremProver().getSmtEngine()
		    .checkSat(qTerm2));
	}

	@Test
	public void testCVC4Expr2() {
		ExprManager em = exprManager.getTheoremProver().getCvc4ExprManager();
		Expr p = em.mkBoundVar("p", em.integerType());
		Expr q = em.mkBoundVar("q", em.integerType());
		vectorExpr varList = new vectorExpr();
		varList.add(p);
		varList.add(q);

		Expr boundVarList = em.mkExpr(Kind.BOUND_VAR_LIST, varList);
		Expr body = em.mkExpr(Kind.NOT, em.mkExpr(Kind.EQUAL, p, q));
		Expr op = em.mkExpr(Kind.LAMBDA, boundVarList, body);

		Expr y = em.mkVar("y", em.integerType());
		Expr a = em.mkExpr(Kind.APPLY_UF, op, y, y);
		IOUtils.err().println(exprManager.getTheoremProver().getSmtEngine()
		    .checkSat(a));
	}

	@Test
	public void testForallExpr2() {
		BoundExpression x = intType.boundVar("x", true);
		BoundExpression y = intType.boundVar("y", true);

		FunctionExpression f = exprManager.functionDeclarator("f", exprManager
		    .functionType(intType, intType), true).asFunctionExpression();
		Expression fx = exprManager.applyExpr(f, x);
		Expression fy = exprManager.applyExpr(f, y);

		// Using a trigger
		List<? extends Expression> triggers = ImmutableList.of(fx);
		BooleanExpression b = exprManager.forall(ImmutableList.of(x, y), x.eq(y)
		    .implies(fx.eq(fy)), triggers);

		assertValid(b);
		assertEquals(ImmutableList.of(triggers), b.getTriggers());
	}

	@Test
	public void testFunctionApplication() {
		BoundExpression x = intType.boundVar("x", true);
		BoundExpression y = intType.boundVar("y", true);
		Expression a = exprManager.applyExpr(((ExpressionManagerImpl) exprManager)
		    .lambda(x, x), y);
		assertValid(a.eq(y));
	}

	@Test
	public void testFunctionApplication2() {
		BoundExpression x = intType.boundVar("x", true);
		BoundExpression y = intType.boundVar("y", true);

		FunctionExpression f = exprManager.functionDeclarator("f", exprManager
		    .functionType(intType, intType), true).asFunctionExpression();

		Expression fx = exprManager.applyExpr(f, x);
		Expression fy = exprManager.applyExpr(f, y);

		assertValid(x.eq(y).implies(fx.eq(fy)));
	}

	@Test
	public void testFunctionApplication3() {
		BoundExpression x = intType.boundVar("x", true);
		BoundExpression y = intType.boundVar("y", true);

		FunctionExpression f = exprManager.functionDeclarator("f", exprManager
		    .functionType(intType, intType), true).asFunctionExpression();
		FunctionExpression f1 = ((ExpressionManagerImpl) exprManager).lambda(x, x);

		assume(f.eq(f1));
		assertValid(f.apply(y).eq(y));
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

		Expression x = exprManager.variable("x", exprManager.integerType(), true);
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
		assertValid(exprManager.eq(exprManager.mult(negOne, x), exprManager.negate(
		    x))); // -1 * x == -x

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
		assertValid(exprManager.eq(exprManager.plus(x, exprManager.negate(x)),
		    zero)); // x + -x == 0
		assertValid(exprManager.eq(exprManager.mult(negOne, negOne), one)); // -1 *
		                                                                    // -1 ==
		                                                                    // 1
		assertValid(exprManager.eq(exprManager.minus(zero, x), exprManager.negate(
		    x))); // 0 - x == -x
	}

	@Test
	public void testLambda() {
		BoundExpression x = intType.boundVar("x", true);
		((ExpressionManagerImpl) exprManager).lambda(x, x);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testRecursiveDatatypes() {
		InductiveType t2Stub = exprManager.inductiveType("t2");
		Selector s1 = exprManager.selector("s1", t2Stub);
		Constructor c1 = exprManager.constructor("c1", s1);

		InductiveType t1Stub = exprManager.inductiveType("t1");
		Selector s2 = exprManager.selector("s2", t1Stub);
		Constructor c2 = exprManager.constructor("c2", s2);
		Constructor c3 = exprManager.constructor("c3"); // important: this is the
		                                                // base case!

		ImmutableList<? extends InductiveType> ts = exprManager.dataTypes(
		    ImmutableList.of("t1", "t2"), ImmutableList.of(c1), ImmutableList.of(c2,
		        c3));

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

	/**
	 * (expected=TheoremProverException.class), this time CVC won't barf,
	 * consturctor's name is made unique in Cascade.
	 */
	@SuppressWarnings("unchecked")
	@Test
	public void testRecursiveDatatypes2() {
		/*
		 * We re-use ids for selectors and constructors, which will make CVC barf.
		 */
		InductiveType t2Stub = exprManager.inductiveType("t2");
		Selector s1 = exprManager.selector("s", t2Stub);
		Constructor c1 = exprManager.constructor("c", s1);

		InductiveType t1Stub = exprManager.inductiveType("t1");
		Selector s2 = exprManager.selector("s", t1Stub);
		Constructor c2 = exprManager.constructor("c", s2);
		Constructor c3 = exprManager.constructor("c2"); // important: this is the
		                                                // base case!

		exprManager.dataTypes(ImmutableList.of("t1", "t2"), ImmutableList.of(c1),
		    ImmutableList.of(c2, c3));

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
		Selector s1 = exprManager.selector("s1", t1Stub);
		// assertEquals("s1",s1.getName());
		assertEquals(t1Stub, s1.getType()); // null != null
	}

	@Test
	public void testTt() {
		BooleanExpression tt = exprManager.tt();
		assertSat(tt);
		assertValid(tt);
	}

	@Test
	public void testEqBool() {
		BooleanExpression tt = exprManager.tt();
		BooleanExpression var = exprManager.booleanType().variable("x", true);
		assertSat(var.eq(tt));
		assertInvalid(var.eq(tt));
	}

	@Test
	public void testTuple() {
		Expression one = exprManager.one();
		Expression two = exprManager.constant(2);
		Expression three = exprManager.constant(3);
		Expression half = exprManager.rationalConstant(1, 2);

		/** Tuple expression must have more than one child */
		/*
		 * TupleExpression tuple = exprManager.tuple(one);
		 * assertEquals(ImmutableList.of(one), tuple.getChildren());
		 * assertEquals(ImmutableList.of(intType),
		 * tuple.getType().getElementTypes());
		 */
		TupleType t1 = exprManager.tupleType("t1", one.getType(), two.getType());
		TupleExpression tuple = exprManager.tuple(t1, one, two);
		assertEquals(ImmutableList.of(one, two), tuple.getChildren());
		assertEquals(ImmutableList.of(intType, intType), tuple.getType()
		    .getElementTypes());

		TupleType t2 = exprManager.tupleType("t2", three.getType(), half.getType(),
		    one.getType());
		tuple = exprManager.tuple(t2, three, half, one);
		assertEquals(ImmutableList.of(three, half, one), tuple.getChildren());
		assertEquals(ImmutableList.of(intType, ratType, intType), tuple.getType()
		    .getElementTypes());
	}

	@Test
	public void testTupleType() {
		/** Tuple type must have more than one child */
		/*
		 * TupleType tupleType = exprManager.tupleType(intType);
		 * assertEquals(ImmutableList.of(intType), tupleType.getElementTypes());
		 */

		TupleType tupleType = exprManager.tupleType("tuple_1", intType, intType);
		assertEquals(ImmutableList.of(intType, intType), tupleType
		    .getElementTypes());

		tupleType = exprManager.tupleType("tuple_2", ratType, intType, ratType);
		assertEquals(ImmutableList.of(ratType, intType, ratType), tupleType
		    .getElementTypes());
	}

	@Test
	public void testRecord() {
		Expression one = exprManager.one();
		Expression two = exprManager.constant(2);
		Expression three = exprManager.constant(3);
		Expression half = exprManager.rationalConstant(1, 2);

		/** Record expression must have more than one child */
		RecordType r1 = exprManager.recordType("record_1", ImmutableList.of("fld_1",
		    "fld_2"), ImmutableList.of(one.getType(), two.getType()));
		RecordExpression record_1 = exprManager.record(r1, one, two);
		assertEquals(ImmutableList.of(one, two), record_1.getChildren());
		assertEquals(ImmutableList.of(intType, intType), record_1.getType()
		    .getElementTypes());

		RecordType r2 = exprManager.recordType("record_2", ImmutableList.of("fld_1",
		    "fld_2", "fld_3"), ImmutableList.of(three.getType(), half.getType(), one
		        .getType()));
		RecordExpression record_2 = exprManager.record(r2, three, half, one);
		assertEquals(ImmutableList.of(three, half, one), record_2.getChildren());
		assertEquals(ImmutableList.of(intType, ratType, intType), record_2.getType()
		    .getElementTypes());
	}

	@Test
	public void testRecordType() {
		RecordType recordType = exprManager.recordType("record_1", "fld_1",
		    intType);
		assertEquals(ImmutableList.of(intType), recordType.getElementTypes());

		RecordType recordType_2 = exprManager.recordType("record_2", ImmutableList
		    .of("fld_1", "fld_2"), ImmutableList.of(intType, intType));
		assertEquals(ImmutableList.of(intType, intType), recordType_2
		    .getElementTypes());

		RecordType recordType_3 = exprManager.recordType("record_3", ImmutableList
		    .of("fld_1", "fld_2", "fld_3"), ImmutableList.of(ratType, intType,
		        ratType));
		assertEquals(ImmutableList.of(ratType, intType, ratType), recordType_3
		    .getElementTypes());
	}

	@Test
	public void testVarIntegerExpression() {
		VariableExpression x = exprManager.variable("x", exprManager.integerType(),
		    true);
		assertEquals(intType, x.getType());
	}

	@Test
	public void testVarIntegerExpression2() {
		VariableExpression x = exprManager.variable("x", exprManager.integerType(),
		    true);
		VariableExpression x2 = exprManager.variable("x", exprManager.integerType(),
		    true);
		assertTrue(!x.equals(x2));
	}
}
