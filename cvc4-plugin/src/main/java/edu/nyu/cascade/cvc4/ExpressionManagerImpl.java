package edu.nyu.cascade.cvc4;

import java.util.List;
import java.util.Map;
import java.util.Vector;

import org.apache.commons.cli.Option;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.inject.internal.Maps;

import edu.nyu.acsys.CVC4.ArrayStoreAll;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.vectorType;

import edu.nyu.cascade.cvc4.InductiveTypeImpl.ConstructorImpl;
import edu.nyu.cascade.cvc4.InductiveTypeImpl.SelectorImpl;
import edu.nyu.cascade.fds.StateExpression;
import edu.nyu.cascade.prover.AbstractExpressionManager;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.Type.DomainType;
import edu.nyu.cascade.util.Identifiers;

/**
 * Implements the expression manager interface on top of cvc4.
 * 
 * [chris 9/23/2009] NOTE: I'm piece-wise moving towards the following
 * architecture: the implementation of Type is responsible for creating
 * expressions of its underlying type. This class just creates the Type
 * instances and delegates calls. See varExpression() and the boolean operation
 * methods (andExpression(), or(), etc.) for examples.
 * 
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 * @author <a href="mailto:mdeters@cs.nyu.edu">Morgan Deters</a>
 */
public class ExpressionManagerImpl extends AbstractExpressionManager {
  
  /** The integer type */
  private final IntegerTypeImpl integerType;
  
/*  @SuppressWarnings("unchecked")
  public static <D extends IType, R extends IType> UnaryFunctionExpression toFunctionExpression(
      IExpression> funExpr) {
    if( funExpr instanceof UnaryFunctionExpression ) {
      return (UnaryFunctionExpression)funExpr;
    } else {
      throw new UnsupportedOperationException("toCvc4Op(" + funExpr.getClass()
          + ")");
    }
  }*/
/*
  @SuppressWarnings("unchecked")
  public static <T extends IType> Type toType(IType type) {
    assert( type != null );
    if (type instanceof Type) {
      return (Type) type;
    } else {
      throw new UnsupportedOperationException("toType(" + type.getClass()
          + ")");
    }
  }  */
  
  /** The Boolean type */
  private final BooleanTypeImpl booleanType;

  /** The rational type */
  private final RationalTypeImpl rationalType;
  
  private final TheoremProverImpl theoremProver;
//  private final BooleanConstant ff, tt;
//  private final RationalExpression ratOne;
//  private final RationalExpression ratZero;

  /** Cache of previously created inductive datatypes. It's helpful
   * to have this around because datatypes are pretty much impossible
   * to reconstruct from the bottom up, e.g., in the case where a 
   * datatype value is passed back up from CVC4 in a counter-example.
   */
  private final Map<String,InductiveTypeImpl> inductiveTypeCache;
  
  ExpressionManagerImpl(TheoremProverImpl theoremProver)  {
    this.theoremProver = theoremProver;
    
    booleanType = new BooleanTypeImpl(this);
//    tt = new BooleanConstant(true, this);
//    ff = new BooleanConstant(false, this);

    integerType = IntegerTypeImpl.getInstance(this);
    rationalType = RationalTypeImpl.getInstance(this);

//    ratOne = rationalType.one();
//    ratZero = rationalType.zero();
    inductiveTypeCache = Maps.newHashMap();
  }

  void addToInductiveTypeCache(InductiveTypeImpl type) {
    Preconditions
        .checkArgument(!inductiveTypeCache.containsKey(type.getName()));
    inductiveTypeCache.put(type.getName(), type);
  }

  @Override
  public void addTrigger(Expression e, Expression p)
       {
    e.asBooleanExpression().addTrigger(p);
  }

  @Override
  public BooleanExpressionImpl and(Expression left,
      Expression right)  {
    return booleanType().and(left, right);
  }

  @Override
  public BooleanExpressionImpl and(Expression first,
      Expression... rest)  {
    return booleanType().and(Lists.asList(first, rest));
  }

  @Override
  public BooleanExpressionImpl and(
      Iterable<? extends Expression> subExpressions) {
    return booleanType().and(subExpressions);
  }
  
  public Expression applyExpr(
      Expression fun, Iterable<? extends Expression> args)
       {
    Preconditions.checkArgument(fun.isFunction());
    return fun.asFunctionExpression().apply(args);
  }
  
  public Expression applyExpr(
      Expression fun, Expression first, Expression... rest)
       {
    Preconditions.checkArgument(fun.isFunction());
    return fun.asFunctionExpression().apply(first, rest);
  }

  /** NOTE: CVC will not create arrays with boolean elements.
   *  TODO: Wrap ('a,boolean) arrays as ('a -> boolean) functions? */
  @Override
  public ArrayTypeImpl arrayType(
      Type index, Type elem)  {
    Preconditions.checkArgument(!DomainType.BOOLEAN
        .equals(elem.getDomainType()));
    return ArrayTypeImpl.create(this, index, elem);
  }
  
  @Override
  public ArrayVariableImpl arrayVar(
      String name, Type indexType, Type elementType, boolean fresh)  {
      ArrayTypeImpl t = ArrayTypeImpl.create(this, indexType, elementType);
      return t.variable(name,true);
  }
  
  @Override
  public ArrayBoundVariableImpl arrayBoundVar(
      String name, Type indexType, Type elementType, boolean fresh)  {
      ArrayTypeImpl t = ArrayTypeImpl.create(this, indexType, elementType);
      return t.boundVariable(name,true);
  }

  @Override 
  public ArrayExpressionImpl asArray(Expression e) {
    return ArrayExpressionImpl.valueOf(importExpression(e));
  }
  
  @Override
  public ArrayTypeImpl asArrayType(
      Type type) {
    return ArrayTypeImpl.valueOf(this, importType(type));
  }
  
  @Override
  public BitVectorExpressionImpl asBitVector(
      Expression expression)  {
    return BitVectorExpressionImpl.valueOf(this,importExpression(expression));
  }


  @Override
  public BitVectorTypeImpl asBitVectorType(
      Type t) {
    return BitVectorTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public BooleanExpressionImpl asBooleanExpression(
      Expression expression)  {
    return BooleanExpressionImpl.valueOf(this,importExpression(expression));
  }

  @Override
  public FunctionTypeImpl asFunctionType(Type t) {
    Preconditions.checkArgument(t.isFunction());
    return FunctionTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public IntegerExpressionImpl asIntegerExpression(
      Expression expression)  {
    return IntegerExpressionImpl.valueOf(this,importExpression(expression));
  }

  
  @Override
  public IntegerVariableImpl asIntegerVariable(
      Expression expression)  {
    return IntegerVariableImpl.valueOf(this,importExpression(expression));
  }
  

  
  @Override
  public RationalExpressionImpl asRationalExpression(
      Expression expression)  {
    return RationalExpressionImpl.valueOf(this,importExpression(expression));
  }
  
  @Override
  public RationalVariableImpl asRationalVariable(
      Expression expression)  {
    return RationalVariableImpl.valueOf(this,importExpression(expression));
  }
  
  @Override
  public TupleTypeImpl asTupleType(Type t) {
    return TupleTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public FunctionExpression asFunctionExpression(
      Expression expression) {
    return FunctionExpressionImpl.valueOf(this, importExpression(expression));
  }
  
  @Override
  public VariableExpressionImpl asVariable(
      Expression expression)  {
    Preconditions.checkArgument(expression.isVariable());
    return VariableExpressionImpl.valueOf(this,importExpression(expression));
  }

  @Override
  public BitVectorExpressionImpl bitVectorConstant(int n, int size) {
    return BitVectorExpressionImpl.mkConstant(this, size, n);
  }

  @Override
  public BitVectorExpressionImpl bitVectorConstant(String rep) {
    return BitVectorExpressionImpl.mkConstant(this, rep);
  }
  
  @Override
  public BitVectorExpression bitVectorPlus(int size,
      Iterable<? extends Expression> args) {
    return BitVectorExpressionImpl.mkPlus(this, size, args);
  }
  
  @Override
  public BitVectorExpression bitVectorMult(int size,
      Iterable<? extends Expression> args) {
    return BitVectorExpressionImpl.mkMult(this, size, args);
  }
  
  @Override
  public BitVectorTypeImpl bitVectorType(int size)  {
    return BitVectorTypeImpl.create(this, size);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorZero(int size) {
    return BitVectorExpressionImpl.mkConstant(this, size, 0);
  }

  @Override
  public BitVectorExpressionImpl bitwiseAnd(Expression a,
      Expression b)  {
    return BitVectorExpressionImpl.mkAnd(this, a,b);
  }
  
  @Override
  public BitVectorExpressionImpl bitwiseNand(Expression a,
      Expression b)  {
    return BitVectorExpressionImpl.mkNand(this, a,b);
  }
  
  @Override
  public BitVectorExpressionImpl bitwiseNor(Expression a,
      Expression b)  {
    return BitVectorExpressionImpl.mkNor(this, a,b);
  }
  
  @Override
  public BitVectorExpressionImpl bitwiseNot(Expression a)
       {
    return BitVectorExpressionImpl.mkNot(this, a);
  }
  

  @Override
  public BitVectorExpressionImpl bitwiseOr(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkOr(this, a, b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseXnor(Expression a,
      Expression b)  {
    return BitVectorExpressionImpl.mkXnor(this, a,b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseXor(Expression a,
      Expression b)  {
    return BitVectorExpressionImpl.mkXor(this, a,b);
  }
  
  /*
  @Override
  public Expression booleanConstant(boolean c)  {
    return new BooleanConstant(c, this);
  }
*/
  @Override
  public BooleanTypeImpl booleanType() {
    return booleanType;
  }

  @Override
  public BooleanVariableImpl booleanVar(String name, boolean fresh)  {
    return booleanType().variable(name, fresh);
  }
  
  @Override
  public BooleanBoundVariableImpl booleanBoundVar(String name, boolean fresh)  {
    return booleanType().boundVariable(name, fresh);
  }
  
  @Override
  public IntegerExpressionImpl constant(int c)  {
    return IntegerExpressionImpl.mkConstant(this, c);
  }

  @Override
  public InductiveExpression construct(Constructor constructor,
      Expression... args) {
    return constructor.apply(args);
  }

  @Override
  public InductiveExpression construct(Constructor constructor,
      Iterable<? extends Expression> args) {
    return constructor.apply(args);
  }

  @Override
  public ConstructorImpl constructor(String name, Selector... selectors) {
    return InductiveTypeImpl.constructor(this, Identifiers.uniquify(name), selectors);
  }
  
  @Override
  public InductiveType dataType(String name, Constructor... constructors)   {
    return InductiveTypeImpl.create(this, name, constructors);
  }
  
  /**
   * Create a set of mutually recursive datatypes. NOTE: This method violates
   * the contract of IExpressionManager.dataTypes. It will throw an exception if
   * one of the datatype names is not globally unique (i.e., every datatype name
   * must be unique).
   */
  /*
   * TODO: fix failure in the case of namespace collisions. Can we "patch up"
   * stubs in selectors after getting unique ids of the datatype names? Note that
   * datatypes are in a different namespace from variables. What about
   * constructors and selectors?
   */
  @Override
  public ImmutableList<? extends InductiveType> dataTypes(List<String> names,
      List<? extends Constructor>... constructorLists) {
    return InductiveTypeImpl.recursiveTypes(this, names, constructorLists);
  }
  
  @Override
  public  BooleanExpressionImpl distinct(
      Expression first, Expression second, Expression... rest)
       {
    return BooleanExpressionImpl.mkDistinct(this, first,second,rest);
  }

  @Override
  public  BooleanExpressionImpl distinct(
      Iterable<? extends Expression> children)  {
    Preconditions.checkArgument(Iterables.size(children) > 1);
    return BooleanExpressionImpl.mkDistinct(this, children);
  }

  @Override
  public BitVectorExpressionImpl divide(
      Expression numerator, Expression denominator) {
      return BitVectorExpressionImpl.mkDivide(this, numerator, denominator);
  }
  
  @Override
  public BitVectorExpressionImpl signedDivide(
      Expression numerator, Expression denominator) {
      return BitVectorExpressionImpl.mkSDivide(this, numerator, denominator);
  }
  
  @Override
  public BitVectorExpressionImpl rem(
      Expression numerator, Expression denominator) {
      return BitVectorExpressionImpl.mkRem(this, numerator, denominator);
  }
  
  @Override
  public BitVectorExpressionImpl signedRem(
      Expression numerator, Expression denominator) {
      return BitVectorExpressionImpl.mkSRem(this, numerator, denominator);
  }
  
  @Override
  public  BooleanExpressionImpl eq(Expression left, Expression right)  {
    return BooleanExpressionImpl.mkEq(this, left, right);
  }

  @Override
  public BooleanExpressionImpl exists(
      Iterable<? extends Expression> vars,
      Expression body)  {
    return booleanType().exists(vars, body);
  }

  @Override
  public BitVectorExpressionImpl extract(Expression bv, int low, int high) {
    return BitVectorTypeImpl.valueOf(this, bv.getType()).extract(bv, high, low);
  }

  @Override
  public BooleanExpressionImpl ff() {
   return booleanType().ff();
  }
  
  @Override
  public BooleanExpressionImpl forall(
      Iterable<? extends Expression> vars,
      Expression body)  {
    return booleanType().forall(vars, body);
  }
  
  @Override
  public BooleanExpressionImpl forall(
      Iterable<? extends Expression> vars,
      Expression body,
      Iterable<? extends Expression> triggers)
       {
    return booleanType().forall(vars, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rewriteRule(Iterable<? extends VariableExpression> vars,
		  Expression guard, Expression rule) {
    return booleanType().rewriteRule(vars, guard, rule);
  }
  
  @Override
  public BooleanExpressionImpl rrRewrite(Expression head, Expression body, Iterable<? extends Expression> triggers) {
    return booleanType().rrRewrite(head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrRewrite(Expression head, Expression body) {
    return booleanType().rrRewrite(head, body);
  }
  
  @Override
  public BooleanExpressionImpl rrReduction(Expression head, Expression body, Iterable<? extends Expression> triggers) {
    return booleanType().rrReduction(head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrReduction(Expression head, Expression body) {
    return booleanType().rrReduction(head, body);
  }
  
  @Override
  public BooleanExpressionImpl rrDeduction(Expression head, Expression body, Iterable<? extends Expression> triggers) {
    return booleanType().rrDeduction(head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrDeduction(Expression head, Expression body) {
    return booleanType().rrDeduction(head, body);
  }
  
  public FunctionTypeImpl functionType(
      Iterable<? extends Type> argTypes, Type range)
       {
    return FunctionTypeImpl.create(this, argTypes, range);
  }
  
  public FunctionVariableImpl functionVar(
      String name, Iterable<? extends Type> argTypes, Type range, boolean fresh)  {
      FunctionTypeImpl ftype = functionType(argTypes,range); 
      return ftype.variable(name, fresh);
  }
  
  public FunctionBoundVariableImpl functionBoundVar(
      String name, Iterable<? extends Type> argTypes, Type range, boolean fresh)  {
      FunctionTypeImpl ftype = functionType(argTypes,range); 
      return ftype.boundVariable(name, fresh);
  }
  
  public FunctionVariableImpl functionVar(
      String name, Type domain, Type range, boolean fresh)  {
      FunctionTypeImpl ftype = functionType(ImmutableList.of(domain), range);
      return ftype.variable(name,fresh);
  }
  
  public FunctionBoundVariableImpl functionBoundVar(
      String name, Type domain, Type range, boolean fresh)  {
      FunctionTypeImpl ftype = functionType(ImmutableList.of(domain), range);
      return ftype.boundVariable(name,fresh);
  }

  @Override
  public ImmutableList<Option> getOptions() {
    return theoremProver.getOptions();
  }

    
  /**
     * Get the theorem prover that is connected to this expression manager
     * 
     * @return the theorem prover
     */
  public TheoremProverImpl getTheoremProver() {
    return theoremProver;
  }
    
  @Override
  public BooleanExpressionImpl hasType(Expression expr, Type type) {
    throw new UnsupportedOperationException("hasType doesn't has cvc4 supported API.");
    /*return BooleanExpressionImpl.mkHasType(this, expr, type);*/
  }

  @Override
  public BooleanExpressionImpl iff(Expression left,
      Expression right)  {
      return booleanType().iff(left, right);
  }

  @Override
  public  Expression ifThenElse(
      Expression cond, Expression tt, Expression ff) {
    return booleanType().ifThenElse(cond, tt, ff);
  }
  
  @Override
  public BooleanExpressionImpl implies(Expression left,
      Expression right)  {
    return booleanType().implies(left, right);
  }
  
  @Override
  public ExpressionImpl importExpression(Expression expr) {
    Preconditions.checkNotNull(expr);
    if (expr instanceof ExpressionImpl
        && this.equals(expr.getExpressionManager())) {
      return (ExpressionImpl) expr;
    } else if (expr instanceof VariableExpression) {
      return VariableExpressionImpl.valueOf(this, expr);
    } else if (expr instanceof StateExpression) {
      // FIXME: Do we really need a special case for IStateExpression???
      return importExpression(((StateExpression) expr).toExpression());
    } else {
      return importType(expr.getType()).importExpression(expr);
    }
  }
  
  @Override
  public ExpressionImpl nullExpression() {
    return ExpressionImpl.mkNullExpr(this);
  }
  
  Iterable<ExpressionImpl> importExpressions(
      Iterable<? extends Expression> subExpressions) {
    return Iterables.transform(subExpressions,
        new Function<Expression, ExpressionImpl>() {

          @Override
          public ExpressionImpl apply(Expression from) {
            return importExpression(from);
          }
        });
  }

  @Override
  public TypeImpl importType(Type type) {
    if (type instanceof TypeImpl && this.equals( type.getExpressionManager() )) {
      return (TypeImpl) type;
    } else if ((Type)type instanceof ArrayType) {
      return (TypeImpl) asArrayType((Type)type);
    } else if ((Type)type instanceof BitVectorType) {
      return (TypeImpl) asBitVectorType((Type) type);
    } else if ((Type)type instanceof BooleanType) {
      return (TypeImpl) booleanType();
    } else if ((Type)type instanceof IntegerType) {
      return (TypeImpl) integerType();
    } else if ((Type)type instanceof FunctionType) {
      return (TypeImpl) asFunctionType((Type) type);
    } else if ((Type)type instanceof RationalType) {
      return (TypeImpl) rationalType();
    } else if ((Type)type instanceof TupleType) {
      return (TypeImpl) asTupleType((Type) type);
    } else {
      throw new UnsupportedOperationException("Unimplemented type conversion: " + type);
    }
  }

  @Override
  public Expression index(
      Expression array, Expression index) {
    Preconditions.checkArgument(array.isArray());
    return array.asArray().index(index);
  }

  @Override
  public Expression index(Expression tuple, int index) {
    Preconditions.checkArgument(tuple.isTuple());
    return tuple.asTuple().index(index);
  }

  @Override
  public InductiveTypeImpl inductiveType(String name) {
    return InductiveTypeImpl.stub(this, name);
  }

  @Override
  public IntegerRangeTypeImpl integerRangeType(Expression lowerBound,
      Expression upperBound)
 {
    Preconditions.checkArgument(lowerBound != null || upperBound != null);
    if (lowerBound == null) {
      return IntegerRangeTypeImpl.withUpperBound(this, lowerBound);
    } else if (upperBound == null) {
      return IntegerRangeTypeImpl.withLowerBound(this, lowerBound);
    } else {
      return IntegerRangeTypeImpl.create(this, lowerBound, upperBound);
    }
  }
  
  @Override
  public IntegerTypeImpl integerType() {
    return integerType;
  }

  @Override
  public IntegerVariableImpl integerVar(String name, boolean fresh)  {
    return integerType().variable(name, fresh);  
  }

  @Override
  public IntegerBoundVariableImpl integerBoundVar(String name, boolean fresh) {
    return integerType().boundVariable(name, fresh);
  }
  
  @Override
  public  FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars, Expression expr) {
    return importExpression(expr).lambda(vars);
  }
  
  public FunctionExpression lambda(BoundVariableListExpressionImpl vars,
      Expression expr) {
    return importExpression(expr).lambda(vars);
  }

  @Override
  public FunctionExpression lambda(
      VariableExpression var, Expression body) {
    return importExpression(body).lambda(var);
  }
  
  InductiveTypeImpl lookupInductiveType(String name) {
    return inductiveTypeCache.get(name);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorMinus(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkMinus(this, a, b);
  }

  @Override
  public BitVectorExpressionImpl mult(int size, Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkMult(this, size, a, b);

  }

  @Override
  public BooleanExpressionImpl not(Expression expr)  {
    return booleanType().not(expr);
  }
  
  @Override
  public BooleanExpressionImpl or(
      Expression... subExpressions)
       {
    return booleanType().or(subExpressions);
  }
  
  @Override
  public BooleanExpressionImpl or(Expression left,
      Expression right)  {
    return booleanType().or(left,right);
  }
  
  @Override
  public BooleanExpressionImpl or(
      Iterable<? extends Expression> subExpressions)
       {
    return booleanType().or(subExpressions);
  }

  @Override
  public BitVectorExpressionImpl plus(int size, Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkPlus(this, size, a, b);

  }

  @Override
  public BitVectorExpressionImpl plus(int size, Expression first,
      Expression... rest) {
    return BitVectorExpressionImpl.mkPlus(this, size, first, rest);
  }

  @Override
  public BitVectorExpressionImpl plus(int size,
      Iterable<? extends Expression> args) {
    return BitVectorExpressionImpl.mkPlus(this, size, args);
  }

  @Override
  public IntegerExpressionImpl integerPow(Expression x, Expression n) {
    return integerType().pow(x, n);
  }
  
  @Override
  public RationalExpressionImpl rationalPow(Expression x, Expression n) {
    return rationalType().pow(x,n);
  }

  @Override
  public RationalExpressionImpl rationalConstant(int numerator, int denominator)  {
    return rationalType.constant(numerator, denominator);
  }

  //  @Override
  public RationalRangeTypeImpl rationalRangeType(Expression lowerBound,
      Expression upperBound) {
    return new RationalRangeTypeImpl(this, lowerBound, upperBound);
  }
  
  @Override
  public RationalTypeImpl rationalType() {
    return rationalType;
  }

  @Override
  public RationalVariableImpl rationalVar(String name, boolean fresh)  {
    return rationalType().variable(name, fresh);
  }
  
  @Override
  public RationalBoundVariableImpl rationalBoundVar(String name, boolean fresh)  {
    return rationalType().boundVariable(name, fresh);
  }

  @Override
  public RationalExpressionImpl ratOne() {
    return rationalType.one();
  }
  
  @Override
  public RationalExpressionImpl ratZero() {
    return rationalType.zero();
  }
  
  @Override
  public Expression select(
      Selector selector, Expression val) {
    return selector.apply(val);
  }

  @Override
  public SelectorImpl selector(String name, Type type) {
    return InductiveTypeImpl.selector(this, name, type);
  }
  
  /**
   * Set implementation-specific properties, given as a set of key/value pairs
   * as Strings. Calls <code>setProperties</code> on the underlying
   * theorem prover as well.
   */
  @Override
  public
  void setPreferences()  {
    theoremProver.setPreferences();
  }

  @Override
  public void setTriggers(Expression e,
      Iterable<? extends Expression> triggers)
       {
    e.asBooleanExpression().setTriggers(triggers);
  }
 
  @Override
  public BitVectorExpressionImpl signExtend(
      Expression bv, int size)  {
    return BitVectorExpressionImpl.mkSignExtend(this, size, bv);
  }

  @Override
  public  Expression subst(Expression e,
      Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs)
       {
    return importExpression(e).subst(oldExprs, newExprs);
  }

  @Override
  public Expression succ(Expression op)  {
    return plus(op,one());
  }

  
  @Override
  public BooleanExpression testConstructor(Constructor constructor,
      Expression val) {
    Preconditions.checkArgument(val.isInductive());
    return val.asInductive().test(constructor);
  }
  
  @SuppressWarnings("unchecked")
  BooleanExpressionImpl toBooleanExpression(Expr e) throws TheoremProverException {
    // try {
    // IOUtils.debug().indent().incr().pln(">> toBooleanExpression(" +
    // e.toString() + ")");

    if (e.getKind() == edu.nyu.acsys.CVC4.Kind.NOT) {
      Preconditions.checkArgument(e.getNumChildren() == 1);
      return not(toBooleanExpression(e.getChild(0)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.LEQ || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLE ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULE) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, lessThanOrEqual((ExpressionImpl) toExpression(e
          .getChild(0)), (ExpressionImpl) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.LT || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLT ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULT) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, lessThan((ExpressionImpl) toExpression(e
          .getChild(0)), (ExpressionImpl) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.GEQ || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGE ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGE) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, greaterThanOrEqual((ExpressionImpl) toExpression(e
          .getChild(0)), (ExpressionImpl) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.GT || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGT ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGT) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, greaterThan((ExpressionImpl) toExpression(e
          .getChild(0)), (ExpressionImpl) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.EQUAL) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return eq((ExpressionImpl) toExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.AND) {
      return and(toBooleanExpressionList(e.getChildren()));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.OR) {
      return or(toBooleanExpressionList(e.getChildren()));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.XOR) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return xor(toBooleanExpression(e.getChild(0)), toBooleanExpression(e
          .getChild(1)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.IMPLIES) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return implies(toBooleanExpression(e.getChild(0)), toBooleanExpression(e
          .getChild(1)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.IFF) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return iff(toBooleanExpression(e.getChild(0)), toBooleanExpression(e
          .getChild(1)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BOOLEAN) {
      Preconditions.checkArgument(e.getNumChildren() == 0);
      if(e.equals(getTheoremProver().getCvc4ExprManager().mkConst(true)))
        return tt();
      else
        return ff();
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.FORALL) {
      vectorExpr childExpr = e.getChildren();
      Vector<VariableExpression> vars = new Vector();
      for(int i = 0; i < childExpr.size()-1; i++) 
        vars.add((VariableExpressionImpl) toExpression(e.getChild(i)));
      BooleanExpression body = toBooleanExpression(e.getChild(childExpr.size()-1));
      return forall(vars, body);
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.EXISTS) {
      vectorExpr childExpr = e.getChildren();
      Vector<VariableExpression> vars = new Vector();
      for(int i = 0; i < childExpr.size()-1; i++) 
        vars.add((VariableExpressionImpl) toExpression(e.getChild(i)));
      BooleanExpression body = toBooleanExpression(e.getChild(childExpr.size()-1));
      return exists(vars, body);
    } else // FIXME: LAMBDA Expr 
      if (/*e.getKind() == edu.nyu.acsys.CVC4.Kind.LAMBDA ||*/ 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.APPLY ) {
        return BooleanExpressionImpl.valueOf(this, (ExpressionImpl)toExpression(e));
/*      return BooleanExpression.valueOf(this, (Expression) lambda(
          (List<VariableExpression>) toExpressionList((List<Expr>) e
              .getVars()), toBooleanExpression(e.getBody())));
*/    
    } else if ("_IS_INTEGER".equals(e.getKind())) {
      /* TODO: e.isTypePred? */
      Preconditions.checkArgument(e.getNumChildren() == 1);
      return hasType(toExpression(e.getChild(0)), integerType());
    } else {
      // IOUtils.debug().indent().pln("NOT HANDLED--BOOL");
      throw new UnsupportedOperationException("Unexpected expression: " + e);
    }
    /*
     * } catch (Exception ex) { IOUtils.debug().indent().pln("EXCEPTION: " +
     * ex.getMessage()); throw ex; } catch (RuntimeException ex) {
     * IOUtils.debug().indent().pln("EXCEPTION: " + ex.getMessage()); throw ex;
     * } finally { IOUtils.debug().decr().indent().pln("<< toBooleanExpression("
     * + e.toString() + ")"); }
     */
  }

  /*  static class BooleanExpr extends Expression {
    BooleanExpr(ExpressionManager em, Expr e, boolean isConst, boolean isVar) {
      super(em, e);
      setConstant(isConst);
      setIsVariable(isVar);
    }
  }

  static class IntExpr extends Expression {
    IntExpr(ExpressionManager em, Expr e, boolean isConst, boolean isVar) {
      super(em, e);
      setConstant(isConst);
      setIsVariable(isVar);
    }
  }
*/  

  List<BooleanExpressionImpl> toBooleanExpressionList(vectorExpr var) {
    List<Expr> args = Lists.newArrayList();
    for(int i = 0; i < var.size(); i++) 
      args.add(var.get(i));
    return Lists.transform(args, new Function<Expr, BooleanExpressionImpl>() {
      @Override
      public BooleanExpressionImpl apply(Expr from) {
        return toBooleanExpression(from);
      }
    });
  }
  
  public Expr toCvc4Expr(Expression expr)  {
    return importExpression(expr).getCvc4Expression();
  }
  
  public List<Expr> toCvc4Exprs(
      Iterable<? extends Expression> subExpressions) {
    return Lists.newArrayList(Iterables.transform(subExpressions,
        new Function<Expression, Expr>() {
          public Expr apply(Expression child) {
              return toCvc4Expr(child);
          }
        }));
  }

  /*public static <D extends IType, R extends IType> Op toCvc4Op(
      IExpression> funExpr) {
    return toFunctionExpression(funExpr).getCvc4Op();
  }
*/
  edu.nyu.acsys.CVC4.Type toCvc4Type(Type type) {
    return importType(type).getCVC4Type();
  }
  
  edu.nyu.acsys.CVC4.DatatypeUnresolvedType toCvc4UnresolvedType(Type type) {
    return importType(type).getCVC4UnresolvedDatatype();
  }
  
  @SuppressWarnings("unchecked")
  ExpressionImpl toExpression(Expr e) throws TheoremProverException {
    // try {
    // IOUtils.debug().indent().incr().pln(">> toExpression(" + e.toString() +
    // ")");
    // IOUtils.debug().flush();

    if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.PLUS ) {
      return (ExpressionImpl) plus((List) toExpressionList(e.getChildren()));
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.MINUS ) {
      return (ExpressionImpl) minus(
          (ExpressionImpl) toExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)));
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.MULT ) {
      return (ExpressionImpl) mult(
          (ExpressionImpl) toExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)));
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.SKOLEM ) {
      return VariableExpressionImpl.valueOfSkolem(this, e, toType(e.getType()));
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.VARIABLE
        // FIXME: SYMBOL Expr is not supported
        /*|| e.getKind() == edu.nyu.acsys.CVC4.Kind.SYMBOL*/) {
      return VariableExpressionImpl.valueOfVariable(this, e, toType(e.getType()));
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_RATIONAL ) {
      // FIXME: Could be an actual rational!
      return new ExpressionImpl(this, Kind.CONSTANT, e, integerType());
    } else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.LAMBDA ) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      List<? extends ExpressionImpl> children = toExpressionList(e.getChildren());
      return (ExpressionImpl) lambda(children.get(0).asBoundVariableList(), 
          children.get(1));
    }
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.APPLY ) {
      /* ExprMut opExpr = e.getOpExpr(); */
      Expr opExpr = e.getOperator();
      return (ExpressionImpl) applyExpr((ExpressionImpl) toExpression(opExpr), 
          (List) toExpressionList(e.getChildren()));
    } else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS ) {
      BitVectorType type = BitVectorTypeImpl.valueOf(this,
          (TypeImpl) toType(e.getType()));
      return BitVectorExpressionImpl.mkPlus(this, type.getSize(),
          (List) toExpressionList(e.getChildren()));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT) { 
      BitVectorType type = BitVectorTypeImpl.valueOf(this,
          (TypeImpl) toType(e.getType()));
      return BitVectorExpressionImpl.mkMult(this, type.getSize(),
          (List) toExpressionList(e.getChildren())); 
    } else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_EXTRACT ) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      int high = (int) e.getChild(0).getConstBitVectorExtract().getHigh();
      int low = (int) e.getChild(0).getConstBitVectorExtract().getLow();
      return extract((Expression) toExpression(e.getChild(1)), low, high);
    } else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BOUND_VARIABLE ) {
      Type type = toType(e.getType());
      String name = e.toString();
      return (ExpressionImpl) boundVariable(name, type, true);
    } else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST ) {
      return (ExpressionImpl) boundVariableList(
          toExpressionList(e.getChildren()));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.SELECT) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return (ExpressionImpl) index((ExpressionImpl) toExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.STORE) {
      Preconditions.checkArgument(e.getNumChildren() == 3);
      return (ExpressionImpl) update((ExpressionImpl) toExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)), (ExpressionImpl) toExpression(e
              .getChild(2)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.ITE) {
      Preconditions.checkArgument(e.getNumChildren() == 3);
      return (ExpressionImpl) ifThenElse(toBooleanExpression(e.getChild(0)),
          (ExpressionImpl) toExpression(e.getChild(1)), (ExpressionImpl) toExpression(e
              .getChild(2)));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BOOLEAN) {
      return (ExpressionImpl) toBooleanExpression(e);
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BITVECTOR) {
/*      Rational val = getTheoremProver().getCvc4ExprManager().computeBVConst(e);
      edu.nyu.acsys.CVC4.Type t = e.getType();
      assert( t.isBitVector() );
      Expr typeExpr = t.getExpr();
      assert( typeExpr.getNumChildren() == 1 );
      Expr typeArg = typeExpr.getChild(0);
      assert( typeArg.isRational() );
      Rational size = typeArg.getRational();
      assert( size.isInteger() );
      return BitVectorExpressionImpl.mkConstant(this, val, size.getInteger());*/
      int val = e.getConstBitVector().getValue().getLong();
      int size = (int) e.getConstBitVector().getSize();
      return BitVectorExpressionImpl.mkConstant(this, size, val);
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_CONCAT) { 
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return importExpression(concat((Expression) toExpression(e.getChild(0)),
          (Expression) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULE) { 
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return importExpression(lessThan((Expression) toExpression(e.getChild(0)),
          (Expression) toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.TUPLE) {
      Vector<Expression> args = new Vector();
      for(int i = 0; i < e.getNumChildren(); i++)
        args.add((Expression) toExpression(e.getChild(i)));
      return (ExpressionImpl) tuple(args);
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.STORE_ALL) {
      ArrayStoreAll arrayStore = e.getConstArrayStoreAll();
      Expr expr = arrayStore.getExpr();
      edu.nyu.acsys.CVC4.Type type = arrayStore.getType();
      return (ExpressionImpl) storeAll(toExpression(expr), toType(type));
    } else if (e.getType().isBoolean()) {
      return toBooleanExpression(e);
    } else {
      // TODO: ExprMut is (_TUPLE_SELECT 0), how to get it?
      // IOUtils.debug().indent().pln("NOT HANDLED--INT");
      throw new UnsupportedOperationException("Unexpected expression with Kind: " + e.getKind() 
          + "\n expression " + e);
    }
    // } catch (Exception ex) {
    // IOUtils.debug().indent().pln("EXCEPTION: " + ex.getMessage());
    // throw new TheoremProverException(
    // "while converting a CVC4 expression to an IBooleanExpression", ex);
    // } catch (RuntimeException ex) {
    // IOUtils.debug().indent().pln("EXCEPTION: " + ex.getMessage());
    // throw ex;
    // } finally {
    // IOUtils.debug().decr().indent().pln("<< toExpression(" + e.toString() +
    // ")");
    // }
  }
  
  List<? extends ExpressionImpl> toExpressionList(vectorExpr var) {
    List<Expr> args = Lists.newArrayList();
    for(int i = 0; i < var.size(); i++)
      args.add(var.get(i));
    return Lists.transform(args, new Function<Expr, ExpressionImpl>() {
      @Override
      public ExpressionImpl apply(Expr from) {
        return toExpression(from);
      }
    });
  }
  
  TypeImpl toType(edu.nyu.acsys.CVC4.Type type) {
    if( type.isBoolean() ) {
      return booleanType();
    } else if( type.equals( integerType().getCVC4Type() )) {
      return integerType();
    } else if( type.equals( rationalType().getCVC4Type() )) {
      return rationalType();
    } else if (type.isArray()) {
      edu.nyu.acsys.CVC4.ArrayType arrayType = 
          new edu.nyu.acsys.CVC4.ArrayType(type);
      TypeImpl indexType = toType(arrayType.getIndexType());
      TypeImpl elemType = toType(arrayType.getConstituentType());
      return ArrayTypeImpl.create(this, indexType, elemType);
    } else if( type.isFunction() ) {
      edu.nyu.acsys.CVC4.FunctionType funcType = 
          new edu.nyu.acsys.CVC4.FunctionType(type);
      vectorType typeArgs = funcType.getArgTypes();
      List<TypeImpl> argTypes = Lists.newArrayList();
      for(int i = 0; i < typeArgs.size(); i++)
        argTypes.add(toType(typeArgs.get(i)));
      TypeImpl rangeType = toType(funcType.getRangeType());
      return functionType(argTypes, rangeType);
    } else if ( type.isBitVector() ) {
      edu.nyu.acsys.CVC4.BitVectorType bvType = 
          new edu.nyu.acsys.CVC4.BitVectorType(type);
      int size = (int) bvType.getSize();
      return bitVectorType(size);
    } else if ( type.isDatatype() ) {
      InductiveTypeImpl inductiveType = lookupInductiveType( type.toString() );
      if( inductiveType == null ) {
        throw new TheoremProverException("Unknown datatype: " + type.toString() );
      }
      return inductiveType;
    } 
    // FIXME: Any type and Sub type not supported in CVC4
/*    else if ( type.isAny() ) { 
      return universalType();
    } else if( type.isSubtype() ) {
      
       * This is a bit tortured, I know. A subtype looks like: TYPE(SUBTYPE(p :
       * D -> R)), where the SUBTYPE is an expression with a lambda as a child.
       

//      IOUtils.debug().pln("Predicate subtype: " + typeExpr);
//      IOUtils.debug().pln("supertype: " + typeExpr.getType());
//      IOUtils.debug().pln("arity: " + typeExpr.arity());

       Subtype's only child is the type predicate 
      assert( typeExpr.arity() == 1 );
      Expr pred = typeExpr.getChild(0);

//      IOUtils.debug().pln("predicate: " + pred);
      
      edu.nyu.acsys.CVC4.Type predType = pred.getType();

//      IOUtils.debug().pln("predicate type: " + predType);
//      IOUtils.debug().pln("arity: " + predType.arity());

       Predicate type's 2 children are domain and range 
      assert( predType.arity() == 2 );
      TypeImpl superType = toType(predType.getChild(0));
      return superType.subType(this,pred);
    }*/
    else {
      throw new UnsupportedOperationException("unexpected type: " + type);
    }
  }

  @Override
  public ArrayExpressionImpl storeAll(Expression expr, Type type) {
    return ArrayExpressionImpl.mkStoreAll(this, expr, type);
  }
  
  @Override
  public BooleanExpressionImpl tt() {
    return booleanType().tt();
  }
  
  public TupleExpressionImpl tuple(Expression first, Expression... rest) {
    Preconditions.checkArgument(rest.length > 0);
    return TupleExpressionImpl.create(this,first, rest);
  }
  
  public TupleExpressionImpl tuple(Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(Iterables.size(elements) >= 2);
    return TupleExpressionImpl.create(this,elements);
  }
  
  public BoundVariableListExpressionImpl asBoundVariableList(
      Expression expression)  {
    Preconditions.checkArgument(((ExpressionImpl)expression).isBoundVariableList());
    return BoundVariableListExpressionImpl.valueOf(this,importExpression(expression));
  }
  
  public BoundVariableListExpressionImpl boundVariableList(Expression first, 
      Expression... rest) {
    Preconditions.checkArgument(rest.length > 0);
    return BoundVariableListExpressionImpl.create(this,first, rest);
  }
  
  public BoundVariableListExpressionImpl boundVariableList(
      Expression element) {
    return BoundVariableListExpressionImpl.create(this,element);
  }
  
  public BoundVariableListExpressionImpl boundVariableList(
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(Iterables.size(elements) >= 1);
    return BoundVariableListExpressionImpl.create(this,elements);
  }

  public TupleTypeImpl tupleType(Iterable<? extends Type> elementTypes) {
    Preconditions.checkArgument(Iterables.size(elementTypes) >= 2);
    return TupleTypeImpl.create(this, elementTypes);
  }
  
  public TupleTypeImpl tupleType(Type firstType, Type... otherTypes) {
    Preconditions.checkArgument(otherTypes.length > 0);
    return TupleTypeImpl.create(this, firstType, otherTypes);
  }

  @Override
  public TypeImpl universalType() {
    throw new UnsupportedOperationException("AnyType() is not supported in CVC4.");
/*    return UniversalTypeImpl.getInstance(this);*/
  }
  
  @Override
  public ArrayExpressionImpl update(
      Expression array, Expression index, Expression value) {
    return ArrayExpressionImpl.mkUpdate(this, array, index, value);
  }

  @Override
  public TupleExpressionImpl update(Expression tuple, int i, Expression val) {
    return asTupleType(tuple.getType()).update(tuple, i, val);
  }

  @Override
  public BooleanExpressionImpl xor(Expression left,
      Expression right)  {
    return booleanType().xor(left, right);
  }

  @Override
  public BitVectorExpressionImpl zeroExtend(
      Expression bv, int size)  {
    Preconditions.checkArgument(bv.isBitVector());
    int bvSize = bv.asBitVector().getSize();
    
    if( bvSize == size ) {
      return asBitVector(bv);
    } else {
      int padding = size - bvSize;
      Expression zeroes = bitVectorConstant(0, padding);
      return asBitVector(concat(zeroes, bv));
    }
  }

  @Override
  public TupleExpression asTuple(Expression e) {
    return TupleExpressionImpl.valueOf(this,importExpression(e));
  }

  @Override
  public InductiveExpressionImpl asInductiveExpression(Expression e) {
    Preconditions.checkArgument(e.isInductive());
    return InductiveExpressionImpl.valueOf(importExpression(e));
  }
  
  @Override
  public int valueOfIntegerConstant(Expression e) {
    Preconditions.checkArgument(e.isConstant() && (e.isInteger() || e.isBitVector()));
    return toCvc4Expr(e).getConstBitVector().getValue().getLong();
  }
  
  @Override
  public boolean valueOfBooleanConstant(Expression e) {
    Preconditions.checkArgument(e.isConstant() && e.isBoolean());
    return toCvc4Expr(e).getConstBoolean();
  }

  @Override
  public Expression applyExpr(FunctionType func, Expression arg) {
    return func.apply(arg);
  }

  @Override
  public Expression applyExpr(FunctionType func,
      Iterable<? extends Expression> args) {
    return func.apply(args);
  }

  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> patterns) {
    return exists(vars, body, patterns);
  }

  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return exists(vars, body, patterns);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return forall(vars, body, patterns);
  }

  @Override
  public FunctionType functionType(String fname, Iterable<? extends Type> args,
      Type range) {
    return functionType(args, range);
  }

  @Override
  public VariableExpression functionVar(String fname, FunctionType func,
      boolean fresh) {
    return this.functionVar(fname, func.getArgTypes(), func.getRangeType(), fresh);
  }

  @Override
  public VariableExpression functionBoundVar(String fname, FunctionType func,
      boolean fresh) {
    return this.functionBoundVar(fname, func.getArgTypes(), func.getRangeType(), fresh);
  }

  @Override
  public Selector selector(String name, Type type, int ref) {
    return selector(name, type);
  }

  @Override
  public TupleExpression tuple(Type type, Expression first, Expression... rest) {
    return tuple(first, rest);
  }

  @Override
  public TupleExpression tuple(Type type,
      Iterable<? extends Expression> elements) {
    return tuple(elements);
  }

  @Override
  public TupleType tupleType(String tname, Iterable<? extends Type> elementTypes) {
    return tupleType(elementTypes);
  }

  @Override
  public TupleType tupleType(String tname, Type firstType, Type... elementTypes) {
    return tupleType(firstType, elementTypes);
  }

  @Override
  public Expression boundExpression(int index, Type type) {
    // TODO Auto-generated method stub
    return null;
  }
}
