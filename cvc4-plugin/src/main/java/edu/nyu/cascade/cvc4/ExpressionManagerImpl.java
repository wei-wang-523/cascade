package edu.nyu.cascade.cvc4;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import org.apache.commons.cli.Option;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.acsys.CVC4.ArrayStoreAll;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.cvc4.InductiveTypeImpl.ConstructorImpl;
import edu.nyu.cascade.cvc4.InductiveTypeImpl.SelectorImpl;
import edu.nyu.cascade.prover.AbstractExpressionManager;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.BoundExpression;
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
import edu.nyu.cascade.prover.type.UninterpretedType;
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
  
  /** The Boolean type */
  private final BooleanTypeImpl booleanType;

  /** The rational type */
  private final RationalTypeImpl rationalType;
  
  private final TheoremProverImpl theoremProver;

  /** Cache of previously created inductive datatypes. It's helpful
   * to have this around because datatypes are pretty much impossible
   * to reconstruct from the bottom up, e.g., in the case where a 
   * datatype value is passed back up from CVC4 in a counter-example.
   */
  private final Map<String,InductiveTypeImpl> inductiveTypeCache;
  
  protected ExpressionManagerImpl(TheoremProverImpl theoremProver)  {
    this.theoremProver = theoremProver;
    
    booleanType = new BooleanTypeImpl(this);

    integerType = IntegerTypeImpl.getInstance(this);
    rationalType = RationalTypeImpl.getInstance(this);

    inductiveTypeCache = Maps.newHashMap();
  }

  /** NOTE: CVC will not create arrays with boolean elements.
   *  TODO: Wrap ('a,boolean) arrays as ('a -> boolean) functions? */
  @Override
  public ArrayTypeImpl arrayType(Type index, Type elem)  {
    Preconditions.checkArgument(!DomainType.BOOLEAN.equals(elem.getDomainType()));
    return ArrayTypeImpl.create(this, index, elem);
  }
  
  @Override 
  public ArrayExpressionImpl asArray(Expression e) {
    return ArrayExpressionImpl.valueOf(importExpression(e));
  }
  
  @Override
  public ArrayTypeImpl asArrayType(Type type) {
    return ArrayTypeImpl.valueOf(this, importType(type));
  }
  
  @Override
  public BitVectorExpressionImpl asBitVector(Expression expression)  {
    return BitVectorExpressionImpl.valueOf(this,importExpression(expression));
  }

  @Override
  public BitVectorTypeImpl asBitVectorType(Type t) {
    return BitVectorTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public BooleanExpressionImpl asBooleanExpression(Expression expression)  {
    return BooleanExpressionImpl.valueOf(this,importExpression(expression));
  }

  @Override
  public FunctionTypeImpl asFunctionType(Type t) {
    Preconditions.checkArgument(t.isFunction());
    return FunctionTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public IntegerExpressionImpl asIntegerExpression(Expression expression)  {
    return IntegerExpressionImpl.valueOf(this,importExpression(expression));
  }
  
  @Override
  public RationalExpressionImpl asRationalExpression(Expression expression)  {
    return RationalExpressionImpl.valueOf(this,importExpression(expression));
  }
  
  @Override
  public TupleTypeImpl asTupleType(Type t) {
    return TupleTypeImpl.valueOf(this, importType(t));
  }

  @Override
  public FunctionExpression asFunctionExpression(Expression expression) {
    return FunctionExpressionImpl.valueOf(this, importExpression(expression));
  }
  
  @Override
  public VariableExpressionImpl asVariable(Expression expression)  {
    Preconditions.checkArgument(expression.isVariable());
    return VariableExpressionImpl.valueOf(this,importExpression(expression));
  }
  
  @Override
  public BoundVariableExpressionImpl asBoundExpression(Expression expression)  {
    Preconditions.checkArgument(expression.isBound());
    return BoundVariableExpressionImpl.valueOf(this,importExpression(expression));
  }

  @Override
  public BitVectorExpressionImpl bitVectorConstant(int n, int size) {
    return BitVectorExpressionImpl.mkConstant(this, size, n);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorConstant(BigInteger n, int size) {
    return BitVectorExpressionImpl.mkConstant(this, size, n);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorConstant(int n) {
    return BitVectorExpressionImpl.mkConstant(this, n);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorConstant(long n) {
    return BitVectorExpressionImpl.mkConstant(this, n);
  }
  
  @Override
  public BitVectorExpressionImpl bitVectorConstant(BigInteger n) {
    return BitVectorExpressionImpl.mkConstant(this, n);
  }

  @Override
  public BitVectorExpressionImpl bitVectorConstant(String rep) {
    return BitVectorExpressionImpl.mkConstant(this, rep);
  }
  
  @Override
  public BitVectorTypeImpl bitVectorType(int size)  {
    return BitVectorTypeImpl.create(this, size);
  }
  
  @Override
  public BooleanTypeImpl booleanType() {
    return booleanType;
  }

  @Override
  public IntegerExpressionImpl constant(int c)  {
    return IntegerExpressionImpl.mkConstant(this, c);
  }

  @Override
  public IntegerExpressionImpl constant(long c)  {
    return IntegerExpressionImpl.mkConstant(this, c);
  }
  
  @Override
  public IntegerExpressionImpl constant(BigInteger c)  {
    return IntegerExpressionImpl.mkConstant(this, c);
  }
  
  @Override
  public ConstructorImpl constructor(String name, Selector... selectors) {
    return InductiveTypeImpl.constructor(this, Identifiers.uniquify(name), selectors);
  }
  
  @Override
  public InductiveType dataType(String name, Constructor... constructors)   {
    return InductiveTypeImpl.createInductiveType(this, name, constructors);
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
  public ImmutableList<Option> getOptions() {
    return theoremProver.getOptions();
  }
 
  /**
   * Get the theorem prover that is connected to this expression manager
   * 
   * @return the theorem prover
   */
  @Override
  public TheoremProverImpl getTheoremProver() {
    return theoremProver;
  }

  @Override
  public InductiveTypeImpl inductiveType(String name) {
    return InductiveTypeImpl.stub(this, name);
  }

  @Override
  public IntegerRangeTypeImpl integerRangeType(Expression lowerBound,
      Expression upperBound) {
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
  public RationalRangeTypeImpl rationalRangeType(Expression lowerBound,
      Expression upperBound) {
    return new RationalRangeTypeImpl(this, lowerBound, upperBound);
  }
  
  @Override
  public RationalTypeImpl rationalType() {
    return rationalType;
  }

  @Override
  public SelectorImpl selector(String name, Type type) {
    return InductiveTypeImpl.selector(this, name, type);
  }  
  
  @Override
  public SelectorImpl selector(String name, Type type, int ref) {
    return InductiveTypeImpl.selector(this, name, type);
  }
  
  /**
   * Set implementation-specific properties, given as a set of key/value pairs
   * as Strings. Calls <code>setProperties</code> on the underlying
   * theorem prover as well.
   */
  @Override
  public void setPreferences()  {
    theoremProver.setPreferences();
  }

  @Override
  public void setTriggers(Expression e,
      Iterable<? extends Expression> triggers) {
    e.asBooleanExpression().setTriggers(triggers);
  }

  @Override
  public TupleExpression asTuple(Expression e) {
    return TupleExpressionImpl.valueOf(this,importExpression(e));
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
  public FunctionType functionType(Iterable<? extends Type> args,
      Type range) {
    return FunctionTypeImpl.create(this, args, range);
  }

  @Override
	public BitVectorExpressionImpl bitVectorConstant(long n, int size) {
	  return BitVectorExpressionImpl.mkConstant(this, size, n);
	}

	@Override
  public TupleExpression tuple(Type type, Expression first, Expression... rest) {
    Preconditions.checkArgument(rest.length > 0);
    return TupleExpressionImpl.create(this, type, first, rest);
  }

  @Override
  public TupleExpression tuple(Type type,
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(Iterables.size(elements) >= 2);
    return TupleExpressionImpl.create(this, type, elements);
  }

  @Override
  public TupleTypeImpl tupleType(String tname, Iterable<? extends Type> elementTypes) {
    return TupleTypeImpl.create(this, tname, elementTypes);
  }

  @Override
  public TupleTypeImpl tupleType(String tname, Type firstType, Type... elementTypes) {
    return TupleTypeImpl.create(this, tname, firstType, elementTypes);
  }

  @Override
  public RecordType asRecordType(Type t) {
    return RecordTypeImpl.valueOf(this, importType(t));
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
  public RecordTypeImpl recordType(String tname, Iterable<String> elementNames,
      Iterable<? extends Type> elementTypes) {
    return RecordTypeImpl.create(this, tname, elementNames, elementTypes);
  }

  @Override
  public RecordTypeImpl recordType(String tname, String elementName, Type elementType) {
    return RecordTypeImpl.create(this, tname, elementName, elementType);
  }
  
  @Override
  public RecordTypeImpl recordType(String tname) {
    return RecordTypeImpl.create(this, tname);
  }

  @Override
  public UninterpretedType uninterpretedType(String name) {
    return UninterpretedTypeImpl.create(this, name);
  }

  @Override
  public RecordExpression asRecord(Expression e) {
    return RecordExpressionImpl.valueOf(this, importExpression(e));
  }

  @Override
  public InductiveExpression asInductive(Expression e) {
    return InductiveExpressionImpl.valueOf(this, importExpression(e));
  }

  @Override
  public UninterpretedExpression asUninterpreted(Expression e) {
    return UninterpretedExpressionImpl.valueOf(this, importExpression(e));
  }

  @Override
  public RecordExpression record(Type r1, Expression first, Expression... rest) {
    Preconditions.checkArgument(rest.length > 0);
    return RecordExpressionImpl.create(this, r1, first, rest);
  }

	@Override
  public ArrayType asArrayType(Type indexType, Type elementType) {
	  return ArrayTypeImpl.create(this, indexType, elementType);
  }
  
  protected void addToInductiveTypeCache(InductiveTypeImpl type) {
	  Preconditions
	      .checkArgument(!inductiveTypeCache.containsKey(type.getName()));
	  inductiveTypeCache.put(type.getName(), type);
	}

	private BooleanExpressionImpl toBooleanExpression(Expr e) throws TheoremProverException {
    if (e.getKind() == edu.nyu.acsys.CVC4.Kind.NOT) {
      Preconditions.checkArgument(e.getNumChildren() == 1);
      return BooleanExpressionImpl.valueOf(this, 
      		not(toBooleanExpression(e.getChild(0))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.LEQ || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLE ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULE) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		lessThanOrEqual(
      				toExpression(e.getChild(0)), toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.LT || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLT ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULT) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		lessThan(
      				toExpression(e.getChild(0)), toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.GEQ || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGE ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGE) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		greaterThanOrEqual(
      				toExpression(e.getChild(0)), toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.GT || 
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGT ||
        e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGT) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		greaterThan(
      				toExpression(e.getChild(0)), toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.EQUAL) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this,
      		eq(
      				toExpression(e.getChild(0)), toExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.AND) {
      return BooleanExpressionImpl.valueOf(this, and(toBooleanExpressionList(e.getChildren())));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.OR) {
      return BooleanExpressionImpl.valueOf(this, or(toBooleanExpressionList(e.getChildren())));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.XOR) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		xor(
      				toBooleanExpression(e.getChild(0)), 
      				toBooleanExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.IMPLIES) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		implies(
      				toBooleanExpression(e.getChild(0)), 
      				toBooleanExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.IFF) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return BooleanExpressionImpl.valueOf(this, 
      		iff(
      				toBooleanExpression(e.getChild(0)), 
      				toBooleanExpression(e.getChild(1))));
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BOOLEAN) {
      Preconditions.checkArgument(e.getNumChildren() == 0);
      if(e.equals(getTheoremProver().getCvc4ExprManager().mkConst(true)))
        return BooleanExpressionImpl.valueOf(this, tt());
      else
        return BooleanExpressionImpl.valueOf(this, ff());
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.FORALL) {
      vectorExpr childExpr = e.getChildren();
      
      Vector<BoundExpression> bounds = new Vector<BoundExpression>();
      for(int i = 0; i < childExpr.size()-1; i++) {
      	Expression var = toExpression(e.getChild(i));
      	BoundVariableExpressionImpl bound = BoundVariableExpressionImpl.valueOf(this, var);
      	bounds.add(bound);
      }
      BooleanExpression body = toBooleanExpression(e.getChild(childExpr.size()-1));
      return BooleanExpressionImpl.valueOf(this, forall(bounds, body));
      
    } else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.EXISTS) {
      vectorExpr childExpr = e.getChildren();
      
      Vector<BoundExpression> bounds = new Vector<BoundExpression>();
      for(int i = 0; i < childExpr.size()-1; i++) {
      	Expression var = toExpression(e.getChild(i));
      	BoundVariableExpressionImpl bound = BoundVariableExpressionImpl.valueOf(this, var);
      	bounds.add(bound);
      }
      
      BooleanExpression body = toBooleanExpression(e.getChild(childExpr.size()-1));
      return BooleanExpressionImpl.valueOf(this, exists(bounds, body));
      
    } else 
    	if (e.getKind() == edu.nyu.acsys.CVC4.Kind.APPLY ) {
    		return BooleanExpressionImpl.valueOf(this, toExpression(e));
    	} else {
    		throw new UnsupportedOperationException("Unexpected expression: " + e);
    	}
  }

	private List<BooleanExpressionImpl> toBooleanExpressionList(vectorExpr var) {
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
  
	FunctionExpression lambda(
      Collection<BoundExpression> args, Expression body) {
    return FunctionExpressionImpl.create(this, args, body);
  }
	
	FunctionExpression lambda(
      BoundExpression arg, Expression body) {
    return FunctionExpressionImpl.create(this, Collections.singletonList(arg), body);
  }
	
	ExpressionImpl importExpression(Expression expr) {
	  Preconditions.checkNotNull(expr);
	  if (expr instanceof ExpressionImpl
	      && this.equals(expr.getExpressionManager())) {
	    return (ExpressionImpl) expr;
	  } else if (expr instanceof VariableExpression) {
	    return VariableExpressionImpl.valueOf(this, expr);
	  } else {
	    return importType(expr.getType()).importExpression(expr);
	  }
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

	TypeImpl importType(Type type) {
	  if (type instanceof TypeImpl && this.equals( type.getExpressionManager() )) {
	    return (TypeImpl) type;
	  } else if (type instanceof ArrayType) {
	    return asArrayType((Type)type);
	  } else if (type instanceof BitVectorType) {
	    return asBitVectorType((Type) type);
	  } else if (type instanceof BooleanType) {
	    return booleanType();
	  } else if (type instanceof IntegerType) {
	    return integerType();
	  } else if (type instanceof FunctionType) {
	    return asFunctionType((Type) type);
	  } else if (type instanceof RationalType) {
	    return rationalType();
	  } else if (type instanceof TupleType) {
	    return asTupleType((Type) type);
	  } else {
	    throw new UnsupportedOperationException("Unimplemented type conversion: " + type);
	  }
	}

	Expr toCvc4Expr(Expression expr)  {
    return importExpression(expr).getCvc4Expression();
  }
  
	List<Expr> toCvc4Exprs(
      Iterable<? extends Expression> subExpressions) {
    return Lists.newArrayList(Iterables.transform(subExpressions,
        new Function<Expression, Expr>() {
          public Expr apply(Expression child) {
              return toCvc4Expr(child);
          }
    }));
  }

	edu.nyu.acsys.CVC4.Type toCvc4Type(Type type) {
    return importType(type).getCVC4Type();
  }
  
	edu.nyu.acsys.CVC4.DatatypeUnresolvedType toCvc4UnresolvedType(Type type) {
    return importType(type).getCVC4UnresolvedDatatype();
  }
  
	ExpressionImpl toExpression(Expr e) throws TheoremProverException {
    if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.PLUS ) {
      return 
      		importExpression(
      				plus(
      						toExpressionList(e.getChildren())));
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.MINUS ) {
      return 
      		importExpression(
      				minus(
      						toExpression(e.getChild(0)), 
      						toExpression(e.getChild(1))));
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.MULT ) {
      return 
      		importExpression(
      				mult(
      						toExpression(e.getChild(0)), 
      						toExpression(e.getChild(1))));
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.SKOLEM ) {
      return VariableExpressionImpl.valueOfSkolem(
      		this, e, toType(e.getType()));
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.VARIABLE) {
      return VariableExpressionImpl.valueOfVariable(
      		this, e, toType(e.getType()));
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_RATIONAL ) {
      // FIXME: Could be an actual rational!
      return new ExpressionImpl(this, Kind.CONSTANT, e, integerType());
    } 
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.LAMBDA ) {
    	Collection<BoundExpression> args = Lists.newArrayList();
    	for(int i = 0; i < e.getNumChildren()-1; i++)
    		args.add(BoundVariableExpressionImpl.valueOf(this, toExpression(e.getChild(i))));
      Expression body = toExpression(e.getChild((int) e.getNumChildren()-1));
      return 
      		importExpression(lambda(args, body));
    }
    else if ( e.getKind() == edu.nyu.acsys.CVC4.Kind.APPLY ) {
      /* ExprMut opExpr = e.getOpExpr(); */
      Expr opExpr = e.getOperator();
      return
      		importExpression(
      				applyExpr(
      						toExpression(opExpr), 
      						toExpressionList(e.getChildren())));
    } 
    else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS ) {
      BitVectorType type = BitVectorTypeImpl.valueOf(this, toType(e.getType()));
      return 
      		importExpression(
      				bitVectorPlus(
      						type.getSize(),
      						toExpression(e.getChild(0)), 
      						toExpression(e.getChild(1))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT) { 
      BitVectorType type = BitVectorTypeImpl.valueOf(this, toType(e.getType()));
      return 
      		importExpression(
      				bitVectorMult(
      						type.getSize(),
      						toExpression(e.getChild(0)), 
      						toExpression(e.getChild(1))));
    } 
    else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_EXTRACT ) {
      Preconditions.checkArgument(e.getNumChildren() == 2);
      int high = (int) e.getChild(0).getConstBitVectorExtract().getHigh();
      int low = (int) e.getChild(0).getConstBitVectorExtract().getLow();
      return 
      		importExpression(
      				extract(
      						toExpression(e.getChild(1)), 
      						low, 
      						high));
    } 
    else if( e.getKind() == edu.nyu.acsys.CVC4.Kind.BOUND_VARIABLE ) {
      Type type = toType(e.getType());
      String name = e.toString();
      return 
      		importExpression(
      				BoundVariableExpressionImpl.create(this, name, type, true));
    }
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.SELECT) {
    	Preconditions.checkArgument(e.getNumChildren() == 2);
      return 
      		importExpression(
      				index(
      						toExpression(e.getChild(0)),
      						toExpression(e.getChild(1))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.STORE) {
      Preconditions.checkArgument(e.getNumChildren() == 3);
      return 
      		importExpression(
      				update(
      						toExpression(e.getChild(0)),
      						toExpression(e.getChild(1)), 
      						toExpression(e.getChild(2))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.ITE) {
      Preconditions.checkArgument(e.getNumChildren() == 3);
      return
      		importExpression(
      				ifThenElse(
      						toBooleanExpression(e.getChild(0)),
      						toExpression(e.getChild(1)), 
      						toExpression(e.getChild(2))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BOOLEAN) {
      return toBooleanExpression(e);
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.CONST_BITVECTOR) {
      Integer val = e.getConstBitVector().getValue();
      int size = (int) e.getConstBitVector().getSize();
      return BitVectorExpressionImpl.mkConstant(this, size, val);
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_CONCAT) { 
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return 
      		importExpression(
      				concat(
      						toExpression(e.getChild(0)),
      						toExpression(e.getChild(1))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULE) { 
      Preconditions.checkArgument(e.getNumChildren() == 2);
      return 
      		importExpression(
      				lessThan(
      						toExpression(e.getChild(0)),
      						toExpression(e.getChild(1))));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.TUPLE) {
      Vector<Expression> args = new Vector<Expression>();
      for(int i = 0; i < e.getNumChildren(); i++)
        args.add(toExpression(e.getChild(i)));
      return 
      		importExpression(
      				tuple(
      						toType(e.getType()), 
      						args));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.RECORD) {
      Vector<Expression> args = new Vector<Expression>();
      for(int i = 0; i < e.getNumChildren(); i++)
        args.add(toExpression(e.getChild(i)));
      return 
      		importExpression(
      				record(
      						toType(e.getType()), 
      						args));
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.STORE_ALL) {
      ArrayStoreAll arrayStore = e.getConstArrayStoreAll();
      Expr expr = arrayStore.getExpr();
      return 
      		importExpression(
      				storeAll(
      						toExpression(expr), 
      						toType(arrayStore.getType())));
    } 
    else if (e.getType().isBoolean()) {
      return toBooleanExpression(e);
    } 
    else if (e.getKind() == edu.nyu.acsys.CVC4.Kind.UNINTERPRETED_CONSTANT) { 
    	return new ExpressionImpl(this, Kind.UNINTERPRETED, e, uninterpretedType(e.getType().toString()));
    }
    else {
      throw new UnsupportedOperationException("Unexpected expression with Kind: " + e.getKind() 
          + "\n expression " + e);
    }
  }
  
	List<? extends ExpressionImpl> toExpressionList(vectorExpr var) {
    List<Expr> args = Lists.newArrayList();
    for(int i = 0; i < var.size(); i++)
      args.add(var.get(i));
    return Lists.transform(args, 
    		new Function<Expr, ExpressionImpl>() {
    	@Override
      public ExpressionImpl apply(Expr from) {
        return toExpression(from);
      }
    });
  }
  
	TypeImpl toType(edu.nyu.acsys.CVC4.Type type) {
    if( type.isBoolean() ) {
      return booleanType();
    } 
    else if( type.equals( integerType().getCVC4Type() )) {
      return integerType();
    } 
    else if( type.equals( rationalType().getCVC4Type() )) {
      return rationalType();
    } 
    else if (type.isArray()) {
    	edu.nyu.acsys.CVC4.ArrayType arrayType = 
          new edu.nyu.acsys.CVC4.ArrayType(type);
      TypeImpl indexType = toType(arrayType.getIndexType());
      TypeImpl elemType = toType(arrayType.getConstituentType());
      return ArrayTypeImpl.create(this, indexType, elemType);
    } 
    else if( type.isFunction() ) {
    	edu.nyu.acsys.CVC4.FunctionType funcType = 
          new edu.nyu.acsys.CVC4.FunctionType(type);
      vectorType typeArgs = funcType.getArgTypes();
      List<TypeImpl> argTypes = Lists.newArrayList();
      for(int i = 0; i < typeArgs.size(); i++)
        argTypes.add(toType(typeArgs.get(i)));
      TypeImpl rangeType = toType(funcType.getRangeType());
      return FunctionTypeImpl.create(this, argTypes, rangeType);
    }
    else if ( type.isBitVector() ) {
      edu.nyu.acsys.CVC4.BitVectorType bvType = 
          new edu.nyu.acsys.CVC4.BitVectorType(type);
      int size = (int) bvType.getSize();
      return bitVectorType(size);
    } 
    else if ( type.isRecord() ) {
    	edu.nyu.acsys.CVC4.RecordType recordType = 
    			new edu.nyu.acsys.CVC4.RecordType(type);
    	edu.nyu.acsys.CVC4.Record record = recordType.getRecord();
    	long size = record.getNumFields();
    	Collection<String> fieldNames = Lists.newArrayList();
    	Collection<Type> fieldTypes = Lists.newArrayList();
    	for(int i = 0; i < size; i++) {
    		Object[] field = record.getField(i);
    		fieldNames.add((String) field[0]);
    		fieldTypes.add(toType((edu.nyu.acsys.CVC4.Type) field[1]));
    	}
    	return RecordTypeImpl.create(this, "cvc4_record", fieldNames, fieldTypes);
    }
    else if ( type.isDatatype() ) {
      InductiveTypeImpl inductiveType = inductiveTypeCache.get( type.toString() );
      if( inductiveType == null ) {
        throw new TheoremProverException("Unknown datatype: " + type.toString() );
      }
      return inductiveType;
    }
    else {
      throw new UnsupportedOperationException("unexpected type: " + type);
    }
  }

	@Override
  public FunctionExpression functionDeclarator(String name,
      FunctionType functionType, boolean fresh) {
	  return FunctionDeclarator.create(this, name, functionType, fresh);
  }
}
