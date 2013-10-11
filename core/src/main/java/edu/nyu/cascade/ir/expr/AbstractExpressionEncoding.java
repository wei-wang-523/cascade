package edu.nyu.cascade.ir.expr;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import xtc.type.Type;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/** An abstract implementation of the <code>ExpressionEncoding</code> interface,
 * with convenience implementations of several methods. 
 * 
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 * @author <a href="mailto:wwang1109@cs.nyu.edu">Wei Wang</a>
 *
 * @param <Expression> The underlying expression encoding
 */

public abstract class AbstractExpressionEncoding
    implements ExpressionEncoding {
  private final ExpressionManager exprManager;

//  private static final String STATE_VARIABLE_NAME = "s";

  private final BiMap<String, Expression> varBindings;
  private final Map<String, IRType> varTypes;
  
  protected static final int DefaultSize = 8;
  
  protected static xtc.type.C cAnalyzer = new xtc.type.C();

  protected final IntegerEncoding<? extends Expression> integerEncoding;

  protected final BooleanEncoding<? extends Expression> booleanEncoding;

  protected final ArrayEncoding<? extends Expression> arrayEncoding;
  
  protected final PointerEncoding<? extends Expression> pointerEncoding;
  
  protected AbstractExpressionEncoding(ExpressionManager exprManager,
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding) {
    this(integerEncoding,booleanEncoding,
    		UnimplementedArrayEncoding.<Expression>create(),
    		UnimplementedPointerEncoding.<Expression>create());
  }
  
  protected AbstractExpressionEncoding(ExpressionManager exprManager,
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding,
      ArrayEncoding<? extends Expression> arrayEncoding) {
    this(integerEncoding,booleanEncoding,arrayEncoding,
    		UnimplementedPointerEncoding.<Expression>create());
  }
  
  protected AbstractExpressionEncoding(
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding,
      ArrayEncoding<? extends Expression> arrayEncoding,
      PointerEncoding<? extends Expression> pointerEncoding) {
    Preconditions.checkArgument( integerEncoding.getExpressionManager().
        equals( booleanEncoding.getExpressionManager()) );
    Preconditions.checkArgument( 
        arrayEncoding instanceof UnimplementedArrayEncoding ||
        integerEncoding.getExpressionManager().equals( arrayEncoding.getExpressionManager()) );
 
    this.exprManager = integerEncoding.getExpressionManager();
    
    // WARNING: variable() better generate well-behaved HashMap keys!
    this.varBindings = HashBiMap.create();
    this.varTypes = Maps.newHashMap();
    
    this.integerEncoding = integerEncoding;
    this.booleanEncoding = booleanEncoding;
    this.arrayEncoding = arrayEncoding;
    this.pointerEncoding = pointerEncoding;
  }

  @Override
  public Expression addSourceVariable(String qName, IRType type) {
    Expression binding = variable(qName, type, true);
    varBindings.put(qName, binding);
    varTypes.put(qName, type);
    return binding;
  }

  @Override
  public Expression and(Expression... conjuncts)
      {
    return and(Arrays.asList(conjuncts));
  }
  
  @Override
  public Expression bindingForSourceVar(String qName) {
    return varBindings.get(Identifiers.fullyQualify(qName));
  }
  
  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>minus()</code> and
   * <code>one()</code>.
   */
  public Expression decr(Expression expr) {
    return minus(expr, one());
  }
  
  @Override
  public Expression functionCall(String name, Expression... args) {
    return functionCall(name,Lists.newArrayList(args));
  }

  /**
   * {@inheritDoc}
   * 
   * Default implementation: returns <code>unknown()</code> for every call.
   */
  @Override
  public Expression functionCall(String name,
      Iterable<? extends Expression> args) {
    IOUtils.err().println(
        "APPROX: ExpressionEncoding treating unexpected function call as unknown: "
            + name);
    return getIntegerEncoding().unknown();
  }
  
  /** {@inheritDoc}
   * 
   * Default implementation: an empty set of assumptions.
   */
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions() {
    return ImmutableSet.of();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return exprManager;
  }

  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>plus()</code> and
   * <code>one()</code>.
   */
  public Expression incr(Expression expr) {
    return plus(expr, one());
  }

  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>and()</code> and
   * <code>castToBoolean()</code>.
   */
  @Override
  public Expression integerAnd(Expression lhs, Expression rhs) {
    return and(castToBoolean(lhs), castToBoolean(rhs));
  }

  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>not()</code> and
   * <code>castToBoolean()</code>.
   */
  @Override
  public Expression integerNot(Expression e) {
    return not(castToBoolean(e));
  }

  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>or()</code> and
   * <code>castToBoolean()</code>.
   */
  @Override
  public Expression integerOr(Expression lhs, Expression rhs) {
    return or(castToBoolean(lhs), castToBoolean(rhs));
  }

  @Override
  public Expression or(Expression... disjuncts)
      {
    return or(Arrays.asList(disjuncts));
  }

  @Override
  public Expression plus(Expression... args)
      {
    return plus(Arrays.asList(args));
  }

  @Override
  public String sourceVarForBinding(Expression var) {
    return varBindings.inverse().get(var);
  }
  
  @Override
  public IRType typeForSourceVar(String qName) {
    return varTypes.get(Identifiers.fullyQualify(qName));
  }

  @Override
  public Expression and(Expression lhs, Expression rhs) {
    return and_(getBooleanEncoding(), lhs, rhs);
  }

  private <T extends Expression> T and_(BooleanEncoding<T> be, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isBoolean(lhs));
    Preconditions.checkArgument(isBoolean(rhs));
    return be.and(be.ofExpression(lhs), be.ofExpression(rhs));
  }
  
  @Override
  public Expression and(Iterable<? extends Expression> conjuncts) {
    return and_(getBooleanEncoding(),conjuncts);
  }

  private <T extends Expression> T and_(BooleanEncoding<T> be,
      Iterable<? extends Expression> conjuncts) {
    List<T> bConjs = Lists.newArrayList();
    for (Expression c : conjuncts) {
      Preconditions.checkArgument(isBoolean(c));
      bConjs.add(be.ofExpression(c));
    }
    return be.and(bConjs);
  }

  @Override
  public Expression bitwiseAnd(Expression a, Expression b) {
    return bitwiseAnd_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> T bitwiseAnd_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.bitwiseAnd(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression lshift(Expression a, Expression b) {
    return lshift_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> Expression lshift_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.lshift(bvIntEncoding.ofExpression(a), bvIntEncoding.ofExpression(b));
    } else {
      throw new UnsupportedOperationException("lshift_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression rshift(Expression a, Expression b) {
    return rshift_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> Expression rshift_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.rshift(bvIntEncoding.ofExpression(a), bvIntEncoding.ofExpression(b));
    } else {
      throw new UnsupportedOperationException("lshift_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression castToBoolean(Expression expr) {
    return isBoolean(expr) 
        ? expr 
        : ofBoolean(castToBoolean_(getIntegerEncoding(),expr));
  }
  
  @Override
  public BooleanExpression toBoolean(Expression expr) {
    Preconditions.checkArgument(isBoolean(expr));
    return toBoolean_(getBooleanEncoding(),expr);
  }

  /* expr should be the type of expression created by the BooleanEncoding. */
  private <T extends Expression> BooleanExpression toBoolean_(
      BooleanEncoding<T> booleanEncoding, Expression e) {
    return booleanEncoding.toBoolean(booleanEncoding.ofExpression(e));
  }
  
  private <T extends Expression> BooleanExpression castToBoolean_(IntegerEncoding<T> ie, Expression a) {
    Preconditions.checkArgument(isInteger(a));
    return ie.toBoolean(ie.ofExpression(a));
  }
  
  @Override
  public Expression castToInteger(Expression bool) {
    return isInteger(bool)
        ? bool
        : getIntegerEncoding().ofBoolean(toBoolean(getBooleanEncoding(),bool));
  }
  
/*  @Override
  public Expression castToRational(Expression expr) {
    return isRational(expr)
        ? expr
        : (Expression) expr.asRationalExpression();
  }*/

  private <T extends Expression> BooleanExpression toBoolean(BooleanEncoding<T> be, Expression e) {
    Preconditions.checkArgument(isBoolean(e));
    return be.toBoolean(be.ofExpression(e));
  }
  
  @Override
  public Expression distinct(Iterable<? extends Expression> exprs) {
    return ofBoolean(distinct_(getIntegerEncoding(),exprs));
  }

  private <T extends Expression> BooleanExpression distinct_(IntegerEncoding<T> ie,
      Iterable<? extends Expression> terms) {
    List<T> iTerms = Lists.newArrayList();
    for (Expression t : terms) {
      Preconditions.checkArgument(isInteger(t));
      iTerms.add(ie.ofExpression(t));
    }
    return ie.distinct(iTerms);
  }
  
  public TypeEncoding<? extends Expression> encodingForType(IRType type) {
    switch (type.getKind()) {
    case ARRAY:
      // TODO(cconway): Handle multi-dimensional arrays
      List<? extends IRType> typeArgsArr = type.getTypeArguments();
      assert( typeArgsArr.size() == 2 );
      return getArrayEncoding().getInstance( encodingForType(typeArgsArr.get(0)),
          encodingForType(typeArgsArr.get(1)));

    case BOOLEAN:
      return getBooleanEncoding();
      
    case INTEGER:
    case RANGE:
      return getIntegerEncoding();
      
    case TUPLE:
      List<? extends IRType> typeArgsPtr = type.getTypeArguments();
      ImmutableList<TypeEncoding<?>> encodings = new ImmutableList.Builder<TypeEncoding<?>>()
          .add(encodingForType(typeArgsPtr.get(0)),
              encodingForType(typeArgsPtr.get(1))).build();
      return getPointerEncoding().getInstance(encodings);
		default:
			throw new UnsupportedOperationException("type=" + type);
    }
  }
  
  private int getMaxSize(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isBitVector() && rhs.isBitVector());
    return Math.max(lhs.asBitVector().getSize(), rhs.asBitVector().getSize());
  }

  @Override
  public Expression eq(Expression lhs, Expression rhs) {
    if(isInteger(lhs) && isInteger(rhs) && 
        !lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return getBooleanEncoding().ofBooleanExpression( lhs.eq((Expression)rhs) );
  }

  @Override
  public Expression ff() {
    return getBooleanEncoding().ff();
  }

  @Override
  public Expression forall(Expression var, Expression p) {
    Preconditions.checkArgument(var.isVariable());
    return forall_(getBooleanEncoding(), var, p);
  }
  
  private <T extends Expression> T forall_(BooleanEncoding<T> be, Expression var, Expression p) {
    Preconditions.checkArgument(isVariable(var));
    Preconditions.checkArgument(isBoolean(p));
    return be.forall(ImmutableList.of(var.asVariable()), be.ofExpression(p));
  }
  
  @Override
  public ArrayEncoding<? extends Expression> getArrayEncoding() {
    return arrayEncoding;
  }

  @Override
  public BooleanEncoding<? extends Expression> getBooleanEncoding() {
    return booleanEncoding;
  }

  @Override
  public IntegerEncoding<? extends Expression> getIntegerEncoding() { 
    return integerEncoding; 
  }
  
  @Override
  public PointerEncoding<? extends Expression> getPointerEncoding() {
    return pointerEncoding;
  }

  @Override
  public Expression greaterThan(Expression lhs, Expression rhs) {
    return ofBoolean(greaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression greaterThan_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.greaterThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression signedGreaterThan(Expression lhs, Expression rhs) {
    return ofBoolean(signedGreaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThan_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.signedGreaterThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression greaterThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(greaterThanOrEqual_(getIntegerEncoding(), lhs,
        rhs));
  }

  private <T extends Expression> BooleanExpression greaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.greaterThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression signedGreaterThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(signedGreaterThanOrEqual_(getIntegerEncoding(), lhs,
        rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.signedGreaterThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression ifThenElse(Expression bool, Expression thenExpr, Expression elseExpr) {
    return ifThenElse_(getIntegerEncoding(), toBoolean(getBooleanEncoding(),
        bool), thenExpr, elseExpr);
  }

  private <T extends Expression> T ifThenElse_(IntegerEncoding<T> ie,
      BooleanExpression b, Expression thenExpr, Expression elseExpr) {
    return ie.ifThenElse(b, ie.ofExpression(thenExpr), ie
        .ofExpression(elseExpr));
  }
  
  @Override
  public Expression indexArray(Expression array, Expression index) {
    return (Expression) indexArray_(getArrayEncoding(),array,index);
  }

  private <T extends Expression> Expression indexArray_(ArrayEncoding<T> ae, Expression array, Expression index) {
    return ae.index(ae.ofExpression(array), index);
  }

  @Override
  public Expression integerConstant(int c) {
    return getIntegerEncoding().constant(c);
  }

  @Override
  public boolean isArray(Expression expr) {
    return getArrayEncoding().isEncodingFor(expr);
  }

  @Override
  public boolean isBoolean(Expression expr) {
    return getBooleanEncoding().isEncodingFor(expr);
  }

  @Override
  public boolean isInteger(Expression expr) {
    return getIntegerEncoding().isEncodingFor(expr);
  }

  @Override
  public boolean isVariable(Expression expr) {
    return expr.isVariable();
  }

  @Override
  public Expression lessThan(Expression lhs, Expression rhs) {
    return ofBoolean(lessThan_(getIntegerEncoding(), lhs, rhs));
  }
  
  @Override
  public Expression signedLessThan(Expression lhs, Expression rhs) {
    return ofBoolean(signedLessThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression lessThan_(IntegerEncoding<T> ie,
      Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.lessThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  private <T extends Expression> BooleanExpression signedLessThan_(IntegerEncoding<T> ie,
      Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.signedLessThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression lessThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(lessThanOrEqual_(getIntegerEncoding(), lhs, rhs));
  }

  @Override
  public Expression signedLessThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(signedLessThanOrEqual_(getIntegerEncoding(), lhs, rhs));
  }
  
  private <T extends Expression> BooleanExpression lessThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.lessThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  private <T extends Expression> BooleanExpression signedLessThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.signedLessThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression minus(Expression lhs, Expression rhs) {
    return minus_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T minus_(
    IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.minus(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression times(Expression lhs, Expression rhs) {
    return times_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T times_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.times(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression divide(Expression lhs, Expression rhs) {
    return divide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T divide_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.divide(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression mod(Expression lhs, Expression rhs) {
    return mod_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T mod_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.mod(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression rem(Expression lhs, Expression rhs) {
    return rem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression rem_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.rem(bvIntEncoding.ofExpression(lhs), bvIntEncoding.ofExpression(rhs));
    } else {
      throw new UnsupportedOperationException("rem_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression signedRem(Expression lhs, Expression rhs) {
    return signedRem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedRem_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.signedRem(bvIntEncoding.ofExpression(lhs), bvIntEncoding.ofExpression(rhs));
    } else {
      throw new UnsupportedOperationException("signedRem_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression signedDivide(Expression lhs, Expression rhs) {
    return signedDivide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedDivide_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.signedDivide(bvIntEncoding.ofExpression(lhs), bvIntEncoding.ofExpression(rhs));
    } else {
      throw new UnsupportedOperationException("signedDivide_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression negate(Expression arg) {
    return negate_(getIntegerEncoding(),arg);
  }

  private <T extends Expression> T negate_(IntegerEncoding<T> ie, Expression a) {
    Preconditions.checkArgument(isInteger(a));
    return ie.negate(ie.ofExpression(a));
  }
  
  @Override
  public Expression neq(Expression lhs, Expression rhs){
    return not(eq(lhs,rhs));
  }

  @Override
  public Expression nor(Iterable<Expression> disjuncts) {
    return not(or(disjuncts));
  }

  @Override
  public Expression not(Expression b) {
    return not_(getBooleanEncoding(),b);
  }
  
  private <T extends Expression> T not_(BooleanEncoding<T> be, Expression b) {
    Preconditions.checkArgument(isBoolean(b));
    return be.not(be.ofExpression(b));
  }

/*  @Override
  public Expression ofBoolean(Expression expr) {
    return getBooleanEncoding().ofExpression(expr);
  }
*/
  @Override
  public Expression ofInteger(Expression x) {
    Preconditions.checkArgument(x.isInteger());
    return getIntegerEncoding().ofExpression(x);
  }

  @Override
  public Expression ofBoolean(Expression x) {
    Preconditions.checkArgument(x.isBoolean());
    return getBooleanEncoding().ofBooleanExpression(x.asBooleanExpression());
  }

  @Override
  public Expression one() {
    return getIntegerEncoding().one();
  }

  @Override
  public Expression or(Expression lhs, Expression rhs) {
    return or_(getBooleanEncoding(),lhs,rhs);
  }
  
  private <T extends Expression> T or_(
      BooleanEncoding<T> be, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isBoolean(lhs));
    Preconditions.checkArgument(isBoolean(rhs));
    return be.or(be.ofExpression(lhs), be.ofExpression(rhs));
  }
  
  @Override
  public Expression or(Iterable<? extends Expression> disjuncts) {
    return or_(getBooleanEncoding(),disjuncts);
  }
  
  private <T extends Expression> T or_(BooleanEncoding<T> be,
      Iterable<? extends Expression> disjuncts) {
    List<T> bDisjs = Lists.newArrayList();
    for (Expression d : disjuncts) {
      Preconditions.checkArgument(isBoolean(d));
      bDisjs.add(be.ofExpression(d));
    }
    return be.and(bDisjs);
  }

  @Override
  public Expression plus(Expression lhs, Expression rhs) {
    return plus_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T plus_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs) && isInteger(rhs));
    if(!lhs.getType().equals(rhs.getType())) {
      int size = getMaxSize(lhs, rhs);
      lhs = lhs.asBitVector().zeroExtend(size);
      rhs = rhs.asBitVector().zeroExtend(size);
    }
    return ie.plus(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression plus(Iterable<? extends Expression> args) {
    return plus_(getIntegerEncoding(),args);
  }

  private <T extends Expression> T plus_(IntegerEncoding<T> ie,
      Iterable<? extends Expression> terms) {
    List<T> iTerms = Lists.newArrayList();
    for (Expression t : terms) {
      Preconditions.checkArgument(isInteger(t));
      iTerms.add(ie.ofExpression(t));
    }
    return ie.plus(iTerms);
  }
  
  @Override
  public Expression symbolicConstant(String name, IRType t, boolean fresh) {
    TypeEncoding<? extends Expression> encoding = encodingForType(t);
    return encoding.symbolicConstant(name, fresh);
  }

  @Override
  public Expression tt() {
    return getBooleanEncoding().tt();
  }

  @Override
  public Expression uminus(Expression expr) {
  	return uminus_(getIntegerEncoding(), expr);
  }
  
  private <T extends Expression> Expression uminus_(
      IntegerEncoding<T> ie, Expression lhs) {
  	return ie.uminus(ie.ofExpression(lhs));
  }
  
  @Override
  public Expression updateArray(Expression array, Expression index, Expression newValue) {
    return updateArray_(getArrayEncoding(),array,index,newValue);
  }

  private <T extends Expression> Expression updateArray_(ArrayEncoding<T> ae, 
      Expression array, Expression index, Expression newValue) {
    return ae.update(ae.ofExpression(array), index, newValue);
  }
  
  @Override
  public Expression castExpression(Expression src, Type targetType) {
    if(!Preferences.isSet(Preferences.OPTION_THEORY)) return src;
    
    String theory = Preferences.getString(Preferences.OPTION_THEORY);
    if(theory.equals(Preferences.OPTION_THEORY_BURSTALL) ||
        theory.equals(Preferences.OPTION_THEORY_BURSTALLFIX) ||
        theory.equals(Preferences.OPTION_THEORY_BURSTALLView)) {
      CellKind srcKind = CType.getCellKind(CType.getType(src.getNode()));
      CellKind targetKind = CType.getCellKind(targetType);
      if(CellKind.POINTER.equals(targetKind) && CellKind.SCALAR.equals(srcKind)) {
        assert src.isConstant();
        return pointerEncoding.getNullPtr();
      }
      
      if(theory.equals(Preferences.OPTION_THEORY_BURSTALLFIX)
          && CellKind.SCALAR.equals(targetKind) 
          && targetKind.equals(srcKind)) {
        int srcSize = src.getType().asBitVectorType().getSize();
        int targetSize = (int) (getCAnalyzer().getSize(targetType) * getCellSize());
        if(srcSize < targetSize)
          return src.asBitVector().zeroExtend(targetSize);
        else
          return src.asBitVector().extract(targetSize-1, 0);
      }
    }
    return src;
  }
  
  @Override
  public Expression castConstant(int value, xtc.type.Type targetType) {
    if(!(Preferences.isSet(Preferences.OPTION_THEORY) &&
        Preferences.get(Preferences.OPTION_THEORY).equals(Preferences.OPTION_THEORY_BURSTALLFIX)))
    return integerConstant(value);
    
    int size = (int) (getCAnalyzer().getSize(targetType) * getCellSize());
    return getExpressionManager().bitVectorConstant(value, size);
  }
  
  @Override
  public Expression variable(String name, IRType type, boolean fresh) {
    return encodingForType(type).variable(name, fresh);
  }

  @Override
  public Expression zero() {
    return getIntegerEncoding().zero();
  }
  
  @Override
  public xtc.type.C getCAnalyzer() {
    return cAnalyzer;
  }
  
  @Override
  public int getCellSize() {
    return DefaultSize;
  }
}
