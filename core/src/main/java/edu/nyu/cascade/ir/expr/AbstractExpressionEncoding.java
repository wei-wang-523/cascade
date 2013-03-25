package edu.nyu.cascade.ir.expr;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.inject.internal.Preconditions;

import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

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

  protected final IntegerEncoding<? extends Expression> integerEncoding;

  protected final BooleanEncoding<? extends Expression> booleanEncoding;

  protected final ArrayEncoding<? extends Expression> arrayEncoding;
  
  protected AbstractExpressionEncoding(ExpressionManager exprManager,
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding) {
    this(integerEncoding,booleanEncoding,UnimplementedArrayEncoding.<Expression>create());
  }
  
  protected AbstractExpressionEncoding(
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding,
      ArrayEncoding<? extends Expression> arrayEncoding) {
    Preconditions.checkArgument( integerEncoding.getExpressionManager().equals( booleanEncoding.getExpressionManager()) );
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
    return unknown();
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

  private Expression rshift_(IntegerEncoding ie, Expression a, Expression b) {
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
      List<? extends IRType> typeArgs = type.getTypeArguments();
      assert( typeArgs.size() == 2 );
      return getArrayEncoding().getInstance( encodingForType(typeArgs.get(0)),
          encodingForType(typeArgs.get(1)));

    case BOOLEAN:
      return getBooleanEncoding();
      
    case INTEGER:
    case RANGE:
      return getIntegerEncoding();
      
    case POINTER:
      return ((PointerExpressionEncoding) this).getPointerEncoding();
    }
    throw new UnsupportedOperationException("type=" + type);
  }

  @Override
  public Expression eq(Expression lhs, Expression rhs) {
      Preconditions.checkArgument(lhs.getType().equals(rhs.getType()));
      return getBooleanEncoding().ofBooleanExpression( lhs.eq((Expression)rhs) );
  /*    if (isInteger(lhs) && isInteger(rhs)) {
        return ofBooleanExpression(getIntegerEncoding().eq(lhs, rhs));
      } else if (isArray(lhs) && isArray(rhs)) {
        Preconditions.checkArgument(getArrayInstance(lhs).equals(
            getArrayInstance(rhs)));
        return ofBooleanExpression(getArrayInstance(lhs).eq(lhs, rhs));
      } else {
        throw new UnsupportedOperationException("eq: " + lhs + "=" + rhs);
      }
  */  }

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
  public Expression greaterThan(Expression lhs, Expression rhs) {
    return ofBoolean(greaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression greaterThan_(
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.greaterThan(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression signedGreaterThan(Expression lhs, Expression rhs) {
    return ofBoolean(signedGreaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThan_(
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.signedGreaterThan(ie.ofExpression(a), ie.ofExpression(b));
  }

  @Override
  public Expression greaterThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(greaterThanOrEqual_(getIntegerEncoding(), lhs,
        rhs));
  }

  private <T extends Expression> BooleanExpression greaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.greaterThanOrEqual(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression signedGreaterThanOrEqual(Expression lhs, Expression rhs) {
    return ofBoolean(signedGreaterThanOrEqual_(getIntegerEncoding(), lhs,
        rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.signedGreaterThanOrEqual(ie.ofExpression(a), ie.ofExpression(b));
  }

  @Override
  public Expression ifThenElse(Expression bool, Expression thenExpr, Expression elseExpr)
      {
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
      Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.lessThan(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  private <T extends Expression> BooleanExpression signedLessThan_(IntegerEncoding<T> ie,
      Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.signedLessThan(ie.ofExpression(a), ie.ofExpression(b));
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
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.lessThanOrEqual(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  private <T extends Expression> BooleanExpression signedLessThanOrEqual_(
      IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.signedLessThanOrEqual(ie.ofExpression(a), ie.ofExpression(b));
  }

  @Override
  public Expression minus(Expression lhs, Expression rhs) {
    return minus_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T minus_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.minus(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression times(Expression lhs, Expression rhs) {
    return times_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T times_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.times(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression divide(Expression lhs, Expression rhs) {
    return divide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T divide_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.divide(ie.ofExpression(a), ie.ofExpression(b));
  }

  @Override
  public Expression mod(Expression lhs, Expression rhs) {
    return mod_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T mod_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.mod(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression rem(Expression lhs, Expression rhs) {
    return rem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression rem_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.rem(bvIntEncoding.ofExpression(a), bvIntEncoding.ofExpression(b));
    } else {
      throw new UnsupportedOperationException("rem_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression signedRem(Expression lhs, Expression rhs) {
    return signedRem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedRem_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.signedRem(bvIntEncoding.ofExpression(a), bvIntEncoding.ofExpression(b));
    } else {
      throw new UnsupportedOperationException("signedRem_ is not supported in integer encoding.");
    }
  }
  
  @Override
  public Expression signedDivide(Expression lhs, Expression rhs) {
    return signedDivide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedDivide_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    if(ie instanceof BitVectorIntegerEncoding) {
      BitVectorIntegerEncoding bvIntEncoding = (BitVectorIntegerEncoding) ie;
      return bvIntEncoding.signedDivide(bvIntEncoding.ofExpression(a), bvIntEncoding.ofExpression(b));
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
  
  private <T extends Expression> T or_(BooleanEncoding<T> be, Expression lhs, Expression rhs) {
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

  private <T extends Expression> T plus_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.plus(ie.ofExpression(a), ie.ofExpression(b));
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
  public Expression unknown() {
    return getIntegerEncoding().unknown();
  }

  @Override
  public Expression updateArray(Expression array, Expression index, Expression newValue) {
    return updateArray_(getArrayEncoding(),array,index,newValue);
  }

  private <T extends Expression> Expression updateArray_(ArrayEncoding<T> ae, Expression array, Expression index, Expression newValue) {
    return ae.update(ae.ofExpression(array), index, newValue);
  }
  
  @Override
  public Expression variable(String name, IRType type, boolean fresh) {
    return encodingForType(type).variable(name, fresh);
  }

  @Override
  public Expression zero() {
    return getIntegerEncoding().zero();
  }
}