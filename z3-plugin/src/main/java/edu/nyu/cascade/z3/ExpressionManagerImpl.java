package edu.nyu.cascade.z3;

import java.util.List;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import org.apache.commons.cli.Option;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.DatatypeExpr;
import com.microsoft.z3.DatatypeSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Pattern;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Sort;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.ArraySort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.TupleSort;
import com.microsoft.z3.UninterpretedSort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.fds.StateExpression;
import edu.nyu.cascade.prover.AbstractExpressionManager;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.Type.DomainType;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.z3.InductiveTypeImpl.ConstructorImpl;
import edu.nyu.cascade.z3.InductiveTypeImpl.SelectorImpl;

/**
 * Implements the expression manager interface on top of z3.
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
   * datatype value is passed back up from Z3 in a counter-example.
   */
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, TypeImpl>> typeCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, TypeImpl>>(){
            public ConcurrentMap<String, TypeImpl> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  private static final ConcurrentMap<Expr, ExpressionImpl> exprCache = new MapMaker().makeMap();
  
  ExpressionManagerImpl(TheoremProverImpl theoremProver)  {
    this.theoremProver = theoremProver;
    
    booleanType = new BooleanTypeImpl(this);
    integerType = IntegerTypeImpl.getInstance(this);
    rationalType = RationalTypeImpl.getInstance(this);
  }

  void addToTypeCache(TypeImpl type) {
    try {
      Preconditions.checkArgument(!typeCache.get(this).containsKey(type.getName()));
      typeCache.get(this).put(type.getName(), type);
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  @Override
  public void addTrigger(Expression e, Expression p) {
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

  @Override
  public Expression applyExpr(
      FunctionType fun, Expression arg) {
    return fun.apply(arg);
  }
  
  @Override
  public Expression applyExpr(
      FunctionType fun, Iterable<? extends Expression> args) {
    return fun.apply(args);
  }

  @Override
  public Expression applyExpr(
      FunctionType fun, Expression first, Expression... rest) {
    return fun.apply(first, rest);
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
  public VariableExpressionImpl arrayBoundVar(
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
  public FunctionDeclarator asFunctionType(Type t) {
    Preconditions.checkArgument(t.isFunction());
    return FunctionDeclarator.valueOf(this, importType(t));
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
  public RecordTypeImpl asRecordType(Type t) {
    return RecordTypeImpl.valueOf(this, importType(t));
  }
  
  @Override
  public FunctionExpression asFunctionExpression(
      Expression expression) {
    throw new UnsupportedOperationException("interpreted function expression is not supported in z3.");
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
  public VariableExpression booleanBoundVar(String name, boolean fresh)  {
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
      Expression body, 
      Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns)  {
    return booleanType().exists(vars, body, patterns, noPatterns);
  }
  
  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body) {
    return exists(vars, body, null, null);
  }

  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> patterns) {
    return exists(vars, body, patterns, null);
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
      Expression body,
      Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return booleanType().forall(vars, body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body) {
    return forall(vars, body, null, null);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> patterns) {
    return forall(vars, body, patterns, null);
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

  @Override
  public FunctionDeclarator functionType(String fname, Iterable<? extends Type> argTypes, 
      Type range) {
    return FunctionDeclarator.create(this, fname, argTypes, range);
  }

  @Override
  public VariableExpression functionVar(String name, FunctionType func, boolean fresh)  {
      return func.variable(name, fresh);
  }

  @Override
  public VariableExpression functionBoundVar(String name, FunctionType func, boolean fresh)  {
      return func.boundVariable(name, fresh);
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
    throw new UnsupportedOperationException("hasType doesn't has z3 supported API.");
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
  
  @Override
  public ExpressionImpl boundExpression(int index, Type type) {
    return ExpressionImpl.mkBound(this, index, type);
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
  
  ExpressionImpl rebuildExpression(Kind kind, Expr expr, Iterable<? extends ExpressionImpl> args) {
    ExpressionImpl res = null;
    try {
      Type type = toType(expr.Sort());
      res = new ExpressionImpl(this, kind, expr, type, args);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
    return res;
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
    } else if ((Type)type instanceof RecordType) {
      return (TypeImpl) asRecordType((Type) type);
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
  public IntegerTypeImpl integerType() {
    return integerType;
  }

  @Override
  public IntegerVariableImpl integerVar(String name, boolean fresh)  {
    return integerType().variable(name, fresh);  
  }

  @Override
  public VariableExpressionImpl integerBoundVar(String name, boolean fresh) {
    return integerType().boundVariable(name, fresh);
  }
  
  @Override
  public  FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars, Expression expr) {
    return importExpression(expr).lambda(vars);
  }

  @Override
  public FunctionExpression lambda(
      VariableExpression var, Expression body) {
    return importExpression(body).lambda(var);
  }
  
  TypeImpl lookupType(String name) {
    try {
      return typeCache.get(this).get(name);
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return null;
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
  
  @Override
  public RationalTypeImpl rationalType() {
    return rationalType;
  }

  @Override
  public RationalVariableImpl rationalVar(String name, boolean fresh)  {
    return rationalType().variable(name, fresh);
  }
  
  @Override
  public VariableExpressionImpl rationalBoundVar(String name, boolean fresh)  {
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
  public  Expression select(
      Selector selector, Expression val) {
    return selector.apply(val);
  }

  @Override
  public SelectorImpl selector(String name, Type type) {
    return InductiveTypeImpl.selector(this, name, type);
  }  
  
  @Override
  public SelectorImpl selector(String name, Type type, int ref) {
    return InductiveTypeImpl.selector(this, name, type, ref);
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
  
  BooleanExpressionImpl toBooleanExpression(Expr e) throws TheoremProverException {
    IOUtils.debug().indent().incr().pln(">> toBooleanExpression(" + e.toString() + ")");
    try {
    if (e.IsBVNOT() || e.IsNot()) {
      Preconditions.checkArgument(e.NumArgs() == 1);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.NOT, e, toExpressionList(e.Args())));
    } else if (e.IsLE() || e.IsBVSLE() || e.IsBVULE()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.LEQ, e, toExpressionList(e.Args())));
    } else if (e.IsLT() || e.IsBVSLT() || e.IsBVULT()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.LT, e, toExpressionList(e.Args())));
    } else if (e.IsGE() || e.IsBVSGE() || e.IsBVUGE()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.GEQ, e, toExpressionList(e.Args())));
    } else if (e.IsGT() || e.IsBVSGT() || e.IsBVUGT()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.GT, e, toExpressionList(e.Args())));
    } else if (e.IsEq()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.EQUAL, e, toExpressionList(e.Args())));
    } else if (e.IsAnd()) {
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.AND, e, toExpressionList(e.Args())));
    } else if (e.IsOr()) {
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.OR, e, toExpressionList(e.Args())));
    } else if (e.IsXor()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.XOR, e, toExpressionList(e.Args())));
    } else if (e.IsImplies()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.IMPLIES, e, toExpressionList(e.Args())));
    } else if (e.IsIff()) {
      Preconditions.checkArgument(e.NumArgs() == 2);
      return BooleanExpressionImpl.valueOf(this, rebuildExpression(Kind.IFF, e, toExpressionList(e.Args())));
    } else if (e.IsBool() && e.IsConst()) {
      Preconditions.checkArgument(e.NumArgs() == 0);
      if(e.equals(getTheoremProver().getZ3Context().MkTrue()))
        return tt();
      else
        return ff();
    } else if (e.IsQuantifier()) {
      Quantifier qtf = (Quantifier) e;
      int size = qtf.NumBound();
      boolean isForall = qtf.IsUniversal();
      Expr z3_body = qtf.Body();
      Symbol[] names = qtf.BoundVariableNames();
      Sort[] sorts = qtf.BoundVariableSorts();
      
      List<VariableExpression> vars = Lists.newArrayList();
      for(int i = 0; i < size; i++) {
        VariableExpression var = VariableExpressionImpl
            .valueOfVariable(this, names[i].toString(), toType(sorts[i])).asVariable();
        vars.add(var);
      }
      
      BooleanExpression body = toBooleanExpression(z3_body);
      
      List<Expression> triggers = null;     
      if(qtf.NumPatterns() > 0) {
        triggers = Lists.newArrayList();
        for(Pattern ptn : qtf.Patterns()) {
          Expr[] terms = ptn.Terms();
          for(Expr term : terms)
            triggers.add(toExpression(term));
        }
      }
      
      List<Expression> noTriggers = null;     
      if(qtf.NumNoPatterns() > 0) {
        noTriggers = Lists.newArrayList();
        for(Pattern nptn : qtf.NoPatterns()) {
          Expr[] terms = nptn.Terms();
          for(Expr term : terms)
            noTriggers.add(toExpression(term));
        }
      }
      
      if(isForall)  return forall(vars, body, triggers, noTriggers);
      else  return exists(vars, body, triggers, noTriggers);
      
    } else if ( e.FuncDecl().Name() != null
          /* e.getKind() == edu.nyu.acsys.Z3.Kind.LAMBDA || 
           * e.getKind() == edu.nyu.acsys.Z3.Kind.APPLY 
           */ ) {
      return BooleanExpressionImpl.valueOf(this, (ExpressionImpl)toExpression(e));  
    } else {
      throw new UnsupportedOperationException("Unexpected expression: " + e);
    }
    } catch (Z3Exception ex) {
      throw new TheoremProverException(ex);
    }
  }

  List<BooleanExpressionImpl> toBooleanExpressionList(Expr[] vars) {
    List<Expr> args = Lists.newArrayList(vars);
    return Lists.transform(args, new Function<Expr, BooleanExpressionImpl>() {
      @Override
      public BooleanExpressionImpl apply(Expr from) {
        return toBooleanExpression(from);
      }
    });
  }
  
  public Expr toZ3Expr(Expression expr)  {
    return importExpression(expr).getZ3Expression();
  }
  
  public List<Expr> toZ3Exprs(
      Iterable<? extends Expression> subExpressions) {
    return Lists.newArrayList(Iterables.transform(subExpressions,
        new Function<Expression, Expr>() {
          public Expr apply(Expression child) {
              return toZ3Expr(child);
          }
        }));
  }
  
  Sort toZ3Type(Type type) {
    return importType(type).getZ3Type();
  }
  
  ExpressionImpl toExpression(Expr e) throws TheoremProverException {
    IOUtils.debug().indent().incr().pln(">> toExpression(" + e.toString() + ")");
    
    if(exprCache.containsKey(e))  
      return exprCache.get(e);
    
    Expression res = null;
    
    try {
      if ( e.IsAdd() ) {
        res = rebuildExpression(Kind.PLUS, e, toExpressionList(e.Args()));
      } else if ( e.IsSub() ) {
        res = rebuildExpression(Kind.MINUS, e, toExpressionList(e.Args()));
      } else if ( e.IsMul() ) {
        res = rebuildExpression(Kind.MULT, e, toExpressionList(e.Args()));
      } else if ( e.IsConst() ) {
        res = VariableExpressionImpl.valueOfVariable(this, e, toType(e.Sort()));
      } else if ( e.IsRatNum() ) {
        // FIXME: Could be an actual rational!
        res = new ExpressionImpl(this, Kind.CONSTANT, e, integerType());
      } else if (e.IsBVNOT()) {
        Preconditions.checkArgument(e.NumArgs() == 1);
        res = rebuildExpression(Kind.BV_NOT, e, toExpressionList(e.Args()));
      } else if( e.IsBVAdd() ) {
        res = rebuildExpression(Kind.PLUS, e, toExpressionList(e.Args()));
      } else if (e.IsBVMul()) { 
        res = rebuildExpression(Kind.MULT, e, toExpressionList(e.Args()));
      } else if (e.IsSelect()) {
        Preconditions.checkArgument(e.NumArgs() == 2);
        res = rebuildExpression(Kind.ARRAY_INDEX, e, toExpressionList(e.Args()));
      } else if (e.IsStore()) {
        Preconditions.checkArgument(e.NumArgs() == 3);
        res = rebuildExpression(Kind.ARRAY_UPDATE, e, toExpressionList(e.Args()));
      } else if (e.IsITE()) {
        Preconditions.checkArgument(e.NumArgs() == 3);
        res = rebuildExpression(Kind.IF_THEN_ELSE, e, toExpressionList(e.Args()));
      } else if (e.IsConst() && e.IsBool()) {
        res = (ExpressionImpl) toBooleanExpression(e);
      } else if (e.IsBVNumeral()) {
        int val = ((BitVecNum) e).Int();
        int size = ((BitVecNum) e).SortSize();
        res = BitVectorExpressionImpl.mkConstant(this, size, val);
      } else if (e.IsIntNum()) {
        int val = ((IntNum) e).Int();
        res = IntegerExpressionImpl.mkConstant(this, val);
      } else if (e.IsBVConcat()) { 
        Preconditions.checkArgument(e.NumArgs() == 2);
        res = rebuildExpression(Kind.BV_CONCAT, e, toExpressionList(e.Args()));
      } else if (e.IsBVExtract()) {
        Preconditions.checkArgument(e.NumArgs() == 1);
        res = rebuildExpression(Kind.BV_EXTRACT, e, toExpressionList(e.Args()));
      } else if (e.IsBVULE()) { 
        Preconditions.checkArgument(e.NumArgs() == 2);
        res = rebuildExpression(Kind.LT, e, toExpressionList(e.Args()));
      } else if (e.IsBool()) {
        res = toBooleanExpression(e);
      } else if (e instanceof DatatypeExpr) {
        Type type = toType(((DatatypeExpr) e).Sort());
        if(type instanceof TupleTypeImpl) {
          res = rebuildExpression(Kind.TUPLE, e, toExpressionList(e.Args()));
        } 
      } else if (e.FuncDecl() != null) { 
        FuncDecl func = e.FuncDecl();
        if(func != null) { // func apply expression
          Sort[] domains = func.Domain();
          String funcName = func.Name().toString();
          if(domains.length == 1 // tuple-index expression
              && funcName.startsWith(domains[0].Name().toString())) {
            Expression tupleExpr = toExpression(e.Args()[0]);
            int idx = Integer.parseInt(funcName.substring(funcName.lastIndexOf("_") + 1));
            res = ((TupleExpressionImpl) tupleExpr.asTuple()).index(idx);
          } else {
            throw new UnsupportedOperationException("Unexpected expression: " + e
                + "\n expression " + e);
          }
        } else {
          throw new UnsupportedOperationException("Unexpected expression: " + e
              + "\n expression " + e);
        }
      }
      
      exprCache.put(e, (ExpressionImpl) res);
      return (ExpressionImpl) res;
      
    } catch (Z3Exception ex) {
      throw new TheoremProverException(ex);
    }
  }
  
  List<? extends ExpressionImpl> toExpressionList(Expr[] vars) {
    List<Expr> args = Lists.newArrayList(vars);
    return Lists.transform(args, new Function<Expr, ExpressionImpl>() {
      @Override
      public ExpressionImpl apply(Expr from) {
        return toExpression(from);
      }
    });
  }
  
  TypeImpl toType(Sort sort) {
    try {
      if( sort instanceof BoolSort) {
        return booleanType();
      } else if( sort instanceof com.microsoft.z3.IntSort) {
        return integerType();
      } else if( sort instanceof com.microsoft.z3.RealSort) {
        return rationalType();
      } else if ( sort instanceof com.microsoft.z3.ArraySort) {
        ArraySort arraySort = (ArraySort) sort;
        TypeImpl indexType = toType(arraySort.Domain());
        TypeImpl elemType = toType(arraySort.Range());
        return ArrayTypeImpl.create(this, indexType, elemType);
      } else if ( sort instanceof com.microsoft.z3.BitVecSort) {
        BitVecSort bvSort = (BitVecSort) sort;
        int size = (int) bvSort.Size();
        return bitVectorType(size);
      } else if ( sort instanceof DatatypeSort) {
        TypeImpl resType = lookupType( sort.Name().toString() );
        if( resType == null ) {
          throw new TheoremProverException("Unknown datatype: " + sort.Name().toString() );
        }
        return resType;
      } else if ( sort instanceof UninterpretedSort) {
        TypeImpl resType = lookupType( sort.Name().toString() );
        if( resType == null ) {
//          return UninterpretedTypeImpl.create(this, sort.Name().toString());
          throw new TheoremProverException("Unknown datatype: " + sort.Name().toString() );
        }
        return resType;
      } else if ( sort instanceof TupleSort) {
        TypeImpl resType = lookupType( sort.Name().toString() );
        if( resType == null ) {
//        TupleSort tupleSort = (TupleSort) sort;
//        List<FuncDecl> funcs = Lists.newArrayList(tupleSort.FieldDecls());
//        List<Type> types = Lists.transform(funcs, new Function<FuncDecl, Type>() {
//          @Override
//          public Type apply(FuncDecl func) {
//            try {
//              return toType(func.Range());
//            } catch (Z3Exception e) {
//              throw new TheoremProverException(e);
//            }
//          }
//        });
//        return TupleTypeImpl.create(this, tupleSort.Name().toString(), types);
          throw new TheoremProverException("Unknown datatype: " + sort.Name().toString() );
        }
        return resType;
      } else {
        throw new UnsupportedOperationException("unexpected sort: " + sort);
      }
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  FunctionDeclarator toFunctionDeclarator(FuncDecl func) {
    return FunctionDeclarator.create(this, func);
  }
  
  @Override
  public BooleanExpressionImpl tt() {
    return booleanType().tt();
  }

  @Override
  public TupleExpressionImpl tuple(Type type, Expression first, Expression... rest) {
    Preconditions.checkArgument(rest.length > 0);
    return TupleExpressionImpl.create(this, type, first, rest);
  }
  
  @Override
  public UninterpretedTypeImpl uninterpretedType(String name) {
    return UninterpretedTypeImpl.create(this, name);
  }

  @Override
  public TupleExpressionImpl tuple(Type type, Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(Iterables.size(elements) >= 2);
    return TupleExpressionImpl.create(this, type, elements);
  }
  
  @Override
  public TupleTypeImpl tupleType(String tname, Iterable<? extends Type> elementTypes) {
    Preconditions.checkArgument(Iterables.size(elementTypes) >= 2);
    return TupleTypeImpl.create(this, tname, elementTypes);
  }

  @Override
  public TupleTypeImpl tupleType(String tname, Type firstType, Type... otherTypes) {
    Preconditions.checkArgument(otherTypes.length > 0);
    return TupleTypeImpl.create(this, tname, firstType, otherTypes);
  }
  
  @Override
  public RecordTypeImpl recordType(String tname) {
    return RecordTypeImpl.create(this, tname);
  }

  @Override
  public RecordTypeImpl recordType(String tname, Iterable<String> elemenNames, 
      Iterable<? extends Type> elementTypes) {
    Preconditions.checkArgument(Iterables.size(elementTypes) == Iterables.size(elemenNames));
    return RecordTypeImpl.create(this, tname, elemenNames, elementTypes);
  }
  
  @Override
  public RecordType recordType(String tname, String elemName, Type elemType) {
    return RecordTypeImpl.create(this, tname, elemName, elemType);
  }
  
  @Override
  public TypeImpl universalType() {
    throw new UnsupportedOperationException("universalType() is not supported in Z3.");
  }
  
  @Override
  public ArrayExpressionImpl update(
      Expression array, Expression index, Expression value) {
    return ArrayExpressionImpl.mkUpdate(this, array, index, value);
  }

  @Override
  public TupleExpressionImpl update(Expression tuple, int i, Expression val) {
    return TupleExpressionImpl.mkUpdate(this, tuple, i, val);
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
  public InductiveExpressionImpl asInductive(Expression e) {
    Preconditions.checkArgument(e.isInductive());
    return InductiveExpressionImpl.valueOf(importExpression(e));
  }
  
  @Override
  public int valueOfIntegerConstant(Expression e) {
    Preconditions.checkArgument(e.isConstant() && (e.isInteger() || e.isBitVector()));
    return ((BitVecNum) toZ3Expr(e)).BigInteger().intValue();
  }
  
  @Override
  public boolean valueOfBooleanConstant(Expression e) {
    Preconditions.checkArgument(e.isConstant() && e.isBoolean());
    try {
      int value = toZ3Expr(e).BoolValue().toInt();
      if(value == 0) return true;
      else    return false;
    } catch (Z3Exception ex) {
      throw new TheoremProverException(ex);
    }
  }

  @Override
  public ArrayExpressionImpl storeAll(Expression expr, Type type) {
    return ArrayExpressionImpl.mkStoreAll(this, expr, type);
  }

  @Override
  public IntegerType integerRangeType(Expression lBound, Expression uBound) {
    throw new UnsupportedOperationException("range type is not supported in z3.");
  }

  @Override
  public RationalType rationalRangeType(Expression lBound, Expression uBound) {
    throw new UnsupportedOperationException("range type is not supported in z3.");
  }

  @Override
  public Expression applyExpr(Expression fun,
      Iterable<? extends Expression> args) {
    return fun.getType().asFunction().apply(args);
  }

  @Override
  public Expression applyExpr(Expression fun, Expression first,
      Expression... rest) {
    return fun.getType().asFunction().apply(first, rest);
  }

  @Override
  public RecordExpression record(Type type, Iterable<? extends Expression> args) {
    return RecordExpressionImpl.create(this, type, args);
  }

  @Override
  public RecordExpression record(Type type, Expression arg) {
    return RecordExpressionImpl.create(this, type, arg);
  }
  
  @Override
  public RecordExpression record(Type type, Expression first, Expression... rest) {
    return RecordExpressionImpl.create(this, type, first, rest);
  }

  @Override
  public RecordExpression update(Expression record, String fieldName,
      Expression val) {
    return RecordExpressionImpl.mkUpdate(this, record, fieldName, val);
  }

  @Override
  public RecordExpression asRecord(Expression e) {
    return RecordExpressionImpl.valueOf(this, importExpression(e));
  }

  @Override
  public UninterpretedExpression asUninterpreted(Expression e) {
    return UninterpretedExpressionImpl.valueOf(this,importExpression(e));
  }
}
