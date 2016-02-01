package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import xtc.type.Type;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.ir.type.IRUnknownType;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

/** An abstract implementation of the <code>ExpressionEncoding</code> interface,
 * with convenience implementations of several methods. 
 * 
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 * @author <a href="mailto:wwang1109@cs.nyu.edu">Wei Wang</a>
 *
 * @param <Expression> The underlying expression encoding
 */

public abstract class AbstractExpressionEncoding implements ExpressionEncoding {
  
  protected final IntegerEncoding<? extends Expression> integerEncoding;

  protected final BooleanEncoding<? extends Expression> booleanEncoding;

  protected final ArrayEncoding<? extends Expression> arrayEncoding;
  
  protected final PointerEncoding<? extends Expression> pointerEncoding;
  
  protected final Collection<BooleanExpression> assumptions;
  
  private final ExpressionManager exprManager;
  
  private final CType cTypeAnalyzer = CType.getInstance();
  
  protected AbstractExpressionEncoding(ExpressionManager exprManager,
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding) {
    this(integerEncoding,booleanEncoding,
    		UnimplementedArrayEncoding.<Expression>create(),
    		new UnimplementedPointerEncoding<Expression>());
  }
  
  protected AbstractExpressionEncoding(ExpressionManager exprManager,
      IntegerEncoding<? extends Expression> integerEncoding,
      BooleanEncoding<? extends Expression> booleanEncoding,
      ArrayEncoding<? extends Expression> arrayEncoding) {
    this(integerEncoding,booleanEncoding,arrayEncoding,
    		new UnimplementedPointerEncoding<Expression>());
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
    this.assumptions = Sets.newHashSet();
    
    this.integerEncoding = integerEncoding;
    this.booleanEncoding = booleanEncoding;
    this.arrayEncoding = arrayEncoding;
    this.pointerEncoding = pointerEncoding;
  }
  
  @Override
  public boolean addAssumption(BooleanExpression assumption) {
  	return assumptions.add(assumption);
  }
  
  @Override
  public void clearAssumptions() {
  	assumptions.clear();
  }

  @Override
  public Expression and(Expression... conjuncts) {
    return and(Arrays.asList(conjuncts));
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
    return ImmutableSet.copyOf(assumptions);
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return exprManager;
  }
  
	@Override
	public CType getCTypeAnalyzer() {
		return cTypeAnalyzer;
	}

  /** {@inheritDoc}
   * 
   * Default implementation: encoding using <code>plus()</code> and
   * <code>one()</code>.
   */
  @Override
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
  public Expression or(Expression... disjuncts) {
    return or(Arrays.asList(disjuncts));
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
  public Expression bitwiseOr(Expression a, Expression b) {
    return bitwiseOr_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> T bitwiseOr_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.bitwiseOr(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  @Override
  public Expression bitwiseNegate(Expression a) {
  	return bitwiseNegate_(getIntegerEncoding(), a);
  }
  
  private <T extends Expression> T bitwiseNegate_(IntegerEncoding<T> ie, Expression a) {
    Preconditions.checkArgument(isInteger(a));
    return ie.bitwiseNegate(ie.ofExpression(a));
  }
  
  @Override
  public Expression bitwiseXor(Expression a, Expression b) {
    return bitwiseXor_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> T bitwiseXor_(IntegerEncoding<T> ie, Expression a, Expression b) {
    Preconditions.checkArgument(isInteger(a));
    Preconditions.checkArgument(isInteger(b));
    return ie.bitwiseXor(ie.ofExpression(a), ie.ofExpression(b));
  }
  
  /** {@inheritDoc}
	 * 
	 * Default implementation: encoding using <code>minus()</code> and
	 * <code>one()</code>.
	 */
	@Override
	public Expression decr(Expression expr) {
		Preconditions.checkArgument(isInteger(expr) || isPointer(expr));
		if(isInteger(expr)) {
			return decr_(getIntegerEncoding(), expr);
		} else {
			return decr_(getPointerEncoding(), expr);
		}
	}

	private <T extends Expression> T decr_(IntegerEncoding<T> ie, Expression expr) {
		Preconditions.checkArgument(isInteger(expr));
		return ie.decr(ie.ofExpression(expr));
	}
	
	private <T extends Expression> T decr_(PointerEncoding<T> pe, Expression expr) {
		Preconditions.checkArgument(isPointer(expr));
		return pe.decr(pe.ofExpression(expr));
	}

	@Override
  public Expression lshift(Expression a, Expression b) {
    return lshift_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> Expression lshift_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.lshift(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression rshift(Expression a, Expression b) {
    return rshift_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> Expression rshift_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.rshift(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression signedRshift(Expression a, Expression b) {
    return signedRshift_(getIntegerEncoding(), a, b);
  }

  private <T extends Expression> Expression signedRshift_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.signedRshift(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression castToBoolean(Expression expr) {
    return isBoolean(expr) 
        ? expr 
        : isInteger(expr)
        	? ofBoolean(castToBoolean_(getIntegerEncoding(),expr))
        			: ofBoolean(castToBoolean_(getPointerEncoding(), expr));
  }
  
  private <T extends Expression> BooleanExpression castToBoolean_(IntegerEncoding<T> ie, Expression a) {
    Preconditions.checkArgument(isInteger(a));
    return ie.toBoolean(ie.ofExpression(a));
  }
  
  private <T extends Expression> BooleanExpression castToBoolean_(PointerEncoding<T> pe, Expression a) {
    Preconditions.checkArgument(isPointer(a));
    return pe.toBoolean(pe.ofExpression(a));
  }
  
  @Override
  public BooleanExpression toBoolean(Expression expr) {
    Preconditions.checkArgument(isBoolean(expr));
    return toBoolean_(getBooleanEncoding(),expr);
  }

  /* expr should be the type of expression created by the BooleanEncoding. */
  private <T extends Expression> BooleanExpression toBoolean_(
      BooleanEncoding<T> be, Expression e) {
    return be.toBoolean(be.ofExpression(e));
  }
  
  @Override
  public Expression castToInteger(Expression expr) {
  	Preconditions.checkArgument(isInteger(expr) || isBoolean(expr));
    return isInteger(expr)
        ? expr
        		: getIntegerEncoding().ofBoolean(toBoolean(getBooleanEncoding(),expr));
  }
  
  @Override
  public Expression castToInteger(Expression expr, int size) {
  	return castToInteger(expr, size, true);
  }
  
  @Override
  public Expression castToInteger(Expression expr, int size, boolean signed) {
  	Preconditions.checkArgument(isInteger(expr) || isBoolean(expr));
  	IntegerEncoding<? extends Expression> ie = getIntegerEncoding();
    return toInteger_(ie, 
    		isInteger(expr) ? 
    				expr : ie.ofBoolean(toBoolean(getBooleanEncoding(),expr)), 
    				size,
    				signed);
  }
  
  private <T extends Expression> Expression toInteger_(
  		IntegerEncoding<T> ie, Expression e, int size, boolean signed) {
  	return ie.ofInteger(ie.ofExpression(e ), size, signed);
  }
  
  @Override
  public Expression castToPointer(Expression expr) {
  	return isPointer(expr)
  			? expr
  			:	getPointerEncoding().getNullPtr();
  }

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
	
	private TypeEncoding<? extends Expression> encodingForType(IRType type) {
    switch (type.getKind()) {
    case BOOLEAN:
      return getBooleanEncoding();
      
    case INTEGER:
    case RANGE:
      return getIntegerEncoding();
    
    case ARRAY:
    case STRUCT:
    case UNION:
    case POINTER:
      return getPointerEncoding();
    
		default:
			throw new ExpressionFactoryException("Unsupported type: " + type);
    }
  }

  @Override
  public Expression eq(Expression lhs, Expression rhs) {
  	if(lhs.getType().equals(rhs.getType()))
  		return getBooleanEncoding().ofBooleanExpression( lhs.eq(rhs) );
  	
  	if(lhs.isBitVector() && rhs.isBitVector()) {
			BitVectorExpression lhsBV = lhs.asBitVector();
			BitVectorExpression rhsBV = rhs.asBitVector();
			int size = Math.max(lhsBV.getSize(), rhsBV.getSize());
			if(lhsBV.getSize() < size) lhs = lhsBV.signExtend(size);
			else if(rhsBV.getSize() < size) rhs = rhsBV.signExtend(size);
			return getBooleanEncoding().ofBooleanExpression( lhs.eq(rhs) );
		}
  	
  	if(isPointer(lhs) && !isPointer(rhs)) {
  		return getBooleanEncoding().ofBooleanExpression(lhs.eq(
  				getPointerEncoding().getNullPtr()));
  	}
  
  	if(!isPointer(lhs) && isPointer(rhs)) {
  		return getBooleanEncoding().ofBooleanExpression(rhs.eq(
  				getPointerEncoding().getNullPtr()));
  	}
  	
  	throw new IllegalArgumentException("Inconsistent types: " + lhs.getType() + ", " + rhs.getType());
  }
  
  @Override
	public Expression ff() {
	  return getBooleanEncoding().ff();
	}

	@Override
	public Expression tt() {
	  return getBooleanEncoding().tt();
	}

	@Override
  public Expression exists(Expression var, Expression p) {
    Preconditions.checkArgument(var.isBound());
    return exists_(getBooleanEncoding(), Lists.newArrayList(var), p);
  }
  
  @Override
  public Expression exists(Expression var1, Expression var2, Expression p) {
    Preconditions.checkArgument(var1.isBound());
    Preconditions.checkArgument(var2.isBound());
    return exists_(getBooleanEncoding(), Lists.newArrayList(var1, var2), p);
  }
  
  @Override
  public Expression exists(Expression var1, Expression var2, Expression var3, Expression p) {
    Preconditions.checkArgument(var1.isBound());
    Preconditions.checkArgument(var2.isBound());
    Preconditions.checkArgument(var3.isBound());
    return exists_(getBooleanEncoding(), Lists.newArrayList(var1, var2, var3), p);
  }
  
  @Override
  public Expression exists(Iterable<? extends Expression> vars, Expression p) {
    Preconditions.checkArgument(Iterables.all(vars, new Predicate<Expression>(){
			@Override
			public boolean apply(Expression var) {
				return var.isBound();
			}  	
    }));
    return exists_(getBooleanEncoding(), vars, p);
  }
  
  private <T extends Expression> T exists_(BooleanEncoding<T> be, Iterable<? extends Expression> vars, Expression p) {
    Preconditions.checkArgument(isBoolean(p));
    
    Iterable<BoundExpression> vars_ = Iterables.transform(vars, 
    		new Function<Expression, BoundExpression>(){
					@Override
					public BoundExpression apply(Expression input) {
						return input.asBound();
					}
    });
    
    return be.exists(vars_, be.ofExpression(p));
  }

  @Override
  public Expression forall(Expression var, Expression p) {
    Preconditions.checkArgument(var.isBound());
    return forall_(getBooleanEncoding(), Lists.newArrayList(var), p);
  }
  
  @Override
  public Expression forall(Expression var1, Expression var2, Expression p) {
    Preconditions.checkArgument(var1.isBound());
    Preconditions.checkArgument(var2.isBound());
    return forall_(getBooleanEncoding(), Lists.newArrayList(var1, var2), p);
  }
  
  @Override
  public Expression forall(Expression var1, Expression var2, Expression var3, Expression p) {
    Preconditions.checkArgument(var1.isBound());
    Preconditions.checkArgument(var2.isBound());
    Preconditions.checkArgument(var3.isBound());
    return forall_(getBooleanEncoding(), Lists.newArrayList(var1, var2, var3), p);
  }
  
  @Override
  public Expression forall(Iterable<? extends Expression> vars, Expression p) {
    Preconditions.checkArgument(Iterables.all(vars, new Predicate<Expression>(){
			@Override
			public boolean apply(Expression var) {
				return var.isBound();
			}  	
    }));
    return forall_(getBooleanEncoding(), vars, p);
  }
  
  private <T extends Expression> T forall_(BooleanEncoding<T> be, Iterable<? extends Expression> vars, Expression p) {
    Preconditions.checkArgument(isBoolean(p));
    
    Iterable<BoundExpression> vars_ = Iterables.transform(vars, 
    		new Function<Expression, BoundExpression>(){
					@Override
					public BoundExpression apply(Expression input) {
						return input.asBound();
					}
    });
    
    return be.forall(vars_, be.ofExpression(p));
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
	public boolean isPointer(Expression expr) {
		return getPointerEncoding().isEncodingFor(expr);
	}

	@Override
	public boolean isVariable(Expression expr) {
	  return expr.isVariable();
	}

	@Override
  public Expression greaterThan(Expression lhs, Expression rhs) {
		return ofBoolean(greaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression greaterThan_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.greaterThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
	@Override
  public Expression pointerGreaterThan(Expression lhs, Expression rhs) {
		return ofBoolean(pointerGreaterThan_(getPointerEncoding(), lhs, rhs));
  }
  
  private <T extends Expression> BooleanExpression pointerGreaterThan_(
      PointerEncoding<T> pe, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isPointer(lhs));
    Preconditions.checkArgument(isPointer(rhs));
    return pe.greaterThan(pe.ofExpression(lhs), pe.ofExpression(rhs));
  }
  
  @Override
  public Expression signedGreaterThan(Expression lhs, Expression rhs) {
  	return ofBoolean(signedGreaterThan_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThan_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.signedGreaterThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression greaterThanOrEqual(Expression lhs, Expression rhs) {
  	return ofBoolean(greaterThanOrEqual_(getIntegerEncoding(), lhs, rhs));
  }

  private <T extends Expression> BooleanExpression greaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.greaterThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression pointerGreaterThanOrEqual(Expression lhs, Expression rhs) {
  	 return ofBoolean(pointerGreaterThanOrEqual_(getPointerEncoding(), lhs, rhs));
  }
  
  private <T extends Expression> BooleanExpression pointerGreaterThanOrEqual_(
      PointerEncoding<T> pe, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isPointer(lhs));
    Preconditions.checkArgument(isPointer(rhs));
    return pe.greaterThanOrEqual(pe.ofExpression(lhs), pe.ofExpression(rhs));
  }
  
  @Override
  public Expression signedGreaterThanOrEqual(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ofBoolean(signedGreaterThanOrEqual_(getIntegerEncoding(), lhs,
        rhs));
  }

  private <T extends Expression> BooleanExpression signedGreaterThanOrEqual_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.signedGreaterThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
	public Expression lessThan(Expression lhs, Expression rhs) {
  	return ofBoolean(lessThan_(getIntegerEncoding(), lhs, rhs));
	}

	private <T extends Expression> BooleanExpression lessThan_(IntegerEncoding<T> ie,
	    Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isInteger(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return ie.lessThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
	@Override
	public Expression pointerLessThan(Expression lhs, Expression rhs) {
		return ofBoolean(pointerLessThan_(getPointerEncoding(), lhs, rhs));
	}
	
	private <T extends Expression> BooleanExpression pointerLessThan_(PointerEncoding<T> pe,
	    Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isPointer(rhs));
	  return pe.lessThan(pe.ofExpression(lhs), pe.ofExpression(rhs));
	}

	@Override
	public Expression signedLessThan(Expression lhs, Expression rhs) {
	  return ofBoolean(signedLessThan_(getIntegerEncoding(), lhs, rhs));
	}

	private <T extends Expression> BooleanExpression signedLessThan_(IntegerEncoding<T> ie,
	    Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isInteger(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return ie.signedLessThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}

	@Override
	public Expression lessThanOrEqual(Expression lhs, Expression rhs) {
		return ofBoolean(lessThanOrEqual_(getIntegerEncoding(), lhs, rhs));
	}

	private <T extends Expression> BooleanExpression lessThanOrEqual_(
	    IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
		Preconditions.checkArgument(isInteger(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return ie.lessThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}

	@Override
	public Expression pointerLessThanOrEqual(Expression lhs, Expression rhs) {
		return ofBoolean(pointerLessThanOrEqual_(getPointerEncoding(), lhs, rhs));
	}
	
	private <T extends Expression> BooleanExpression pointerLessThanOrEqual_(
	    PointerEncoding<T> pe, Expression lhs, Expression rhs) {
		Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isPointer(rhs));
	  return pe.lessThanOrEqual(pe.ofExpression(lhs), pe.ofExpression(rhs));
	}

	@Override
	public Expression signedLessThanOrEqual(Expression lhs, Expression rhs) {
	  return ofBoolean(signedLessThanOrEqual_(getIntegerEncoding(), lhs, rhs));
	}

	private <T extends Expression> BooleanExpression signedLessThanOrEqual_(
	    IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
		Preconditions.checkArgument(isInteger(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return ie.signedLessThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}

	@Override
  public Expression ifThenElse(Expression bool, Expression thenExpr, Expression elseExpr) {
  	Preconditions.checkArgument((isInteger(thenExpr) && isInteger(elseExpr))
  			|| (isBoolean(thenExpr) && isBoolean(elseExpr))
  			|| (isPointer(thenExpr) && isPointer(elseExpr)));
  	if(isBoolean(thenExpr))
  		return ifThenElse_(getBooleanEncoding(), toBoolean(getBooleanEncoding(),
        bool), thenExpr, elseExpr);
  	else if(isInteger(thenExpr))
  		return ifThenElse_(getIntegerEncoding(), toBoolean(getBooleanEncoding(),
        bool), thenExpr, elseExpr);
  	else
  		return ifThenElse_(getPointerEncoding(), toBoolean(getBooleanEncoding(),
          bool), thenExpr, elseExpr);
  }
	
  private <T extends Expression> T ifThenElse_(BooleanEncoding<T> be,
      BooleanExpression b, Expression thenExpr, Expression elseExpr) {
    return be.ifThenElse(b, be.ofExpression(thenExpr), be
        .ofExpression(elseExpr));
  }

  private <T extends Expression> T ifThenElse_(IntegerEncoding<T> ie,
      BooleanExpression b, Expression thenExpr, Expression elseExpr) {
    return ie.ifThenElse(b, ie.ofExpression(thenExpr), ie
        .ofExpression(elseExpr));
  }
  
  private <T extends Expression> T ifThenElse_(PointerEncoding<T> pe,
      BooleanExpression b, Expression thenExpr, Expression elseExpr) {
    return pe.ifThenElse(b, pe.ofExpression(thenExpr), pe
        .ofExpression(elseExpr));
  }
  
  @Override
  public Expression implies(Expression lhs, Expression rhs) {
  	return implies_(getBooleanEncoding(), lhs, rhs);
  }
  
  private <T extends Expression> T implies_(BooleanEncoding<T> be,
  		Expression lhs, Expression rhs) {
  	return be.implies(be.ofExpression(lhs), be.ofExpression(rhs));
  }
  
  @Override
  public Expression indexArray(Expression array, Expression index) {
    return indexArray_(getArrayEncoding(),array,index);
  }

  private <T extends Expression> Expression indexArray_(ArrayEncoding<T> ae, 
  		Expression array, Expression index) {
    return ae.index(ae.ofExpression(array), index);
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
  public Expression integerConstant(int c) {
    return getIntegerEncoding().constant(c);
  }
	
	@Override
  public Expression integerConstant(long c) {
    return getIntegerEncoding().constant(c);
  }
	
	@Override
  public Expression characterConstant(int c) {
    return getIntegerEncoding().characterConstant(c);
  }
	
	@Override
  public Expression integerConstant(BigInteger c) {
    return getIntegerEncoding().constant(c);
  }
	
  @Override
	public Expression one() {
	  return getIntegerEncoding().one();
	}

	@Override
	public Expression zero() {
	  return getIntegerEncoding().zero();
	}
	
	@Override
	public Expression plus(Expression first, Expression... rest) {
	  return plus_(getIntegerEncoding(), first, Lists.newArrayList(rest));
	}
	
	@Override
	public Expression plus(Expression lhs, Expression rhs) {
		return plus_(getIntegerEncoding(), lhs, rhs);
	}
	
	@Override
	public Expression plus(Expression first, Iterable<? extends Expression> rest) {
		return plus_(getIntegerEncoding(), first, rest);
	}

	private <T extends Expression> T plus_(final IntegerEncoding<T> ie, Expression first,
	    Iterable<? extends Expression> rest) {
	  Iterable<T> iTerms = Iterables.transform(rest, new Function<Expression, T>() {
			@Override
			public T apply(Expression t) {
				Preconditions.checkArgument(isInteger(t));
				return ie.ofExpression(t);
			}
	  });
	  return ie.plus(ie.ofExpression(first), iTerms);
	}
	
	private <T extends Expression> T plus_(
	    IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isInteger(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
    			
	  return ie.plus(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
	@Override
	public Expression pointerPlus(Expression lhs, Expression rhs) {
		return pointerPlus_(getPointerEncoding(), getIntegerEncoding(), lhs, rhs);
	}
	
	private <T extends Expression> T pointerPlus_(PointerEncoding<T> pe, 
			IntegerEncoding<?> ie, Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return pe.plus(pe.ofExpression(lhs), ie.ofExpression(rhs));
	}

  @Override
  public Expression minus(Expression lhs, Expression rhs) {
  	return minus_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T minus_(
    IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.minus(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression pointerMinus(Expression lhs, Expression rhs) {
		return pointerMinus_(getPointerEncoding(), getIntegerEncoding(), lhs, rhs);
  }
  
  private <T extends Expression> T pointerMinus_(
      PointerEncoding<T> pe, IntegerEncoding<?> ie, Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isInteger(rhs));
	  return pe.minus(pe.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression times(Expression lhs, Expression rhs) {
    return times_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T times_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.times(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression divide(Expression lhs, Expression rhs) {
    return divide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T divide_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.divide(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

  @Override
  public Expression mod(Expression lhs, Expression rhs) {
    return mod_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> T mod_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.mod(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression rem(Expression lhs, Expression rhs) {
    return rem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression rem_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.rem(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
	public Expression uminus(Expression expr) {
		return uminus_(getIntegerEncoding(), expr);
	}

	private <T extends Expression> Expression uminus_(
	    IntegerEncoding<T> ie, Expression lhs) {
		Preconditions.checkArgument(isInteger(lhs));
    			
		return ie.uminus(ie.ofExpression(lhs));
	}
	
  @Override
	public Expression uplus(Expression expr) {
		return uplus_(getIntegerEncoding(), expr);
	}

	private <T extends Expression> Expression uplus_(
	    IntegerEncoding<T> ie, Expression lhs) {
		Preconditions.checkArgument(isInteger(lhs));
    			
		return ie.uplus(ie.ofExpression(lhs));
	}

	@Override
  public Expression signedRem(Expression lhs, Expression rhs) {
    return signedRem_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedRem_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    return ie.signedRem(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }
  
  @Override
  public Expression signedDivide(Expression lhs, Expression rhs) {
    return signedDivide_(getIntegerEncoding(), lhs, rhs);
  }

  private <T extends Expression> Expression signedDivide_(
      IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
  	Preconditions.checkArgument(isInteger(lhs));
    Preconditions.checkArgument(isInteger(rhs));
    			
    return ie.signedDivide(ie.ofExpression(lhs), ie.ofExpression(rhs));
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
	  return be.or(bDisjs);
	}
	
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
  public Expression ofPointer(Expression expr) {
  	return getPointerEncoding().ofExpression(expr);
  }
  
  @Override
  public Expression variable(String name, IRType type, boolean fresh) {
  	try {
  		return encodingForType(type).variable(name, type, fresh);
  	} catch (ExpressionFactoryException e) {
  		
      IOUtils.err()
      .println(
          "APPROX: Treating unexpected type " + type + " variable as unknown" );
      
  		if(type.getKind().equals(IRType.Kind.UNKNOWN)) {
  			Type xtcType = ((IRUnknownType) type).getXtcType();
  			return unknown(xtcType);
  		}
  		
  		return getIntegerEncoding().unknown();
  	}
  }

	@Override
  public Expression boundVar(String name, IRType type, boolean fresh) {
		try {
			return encodingForType(type).boundVar(name, type, fresh);
		} catch (ExpressionFactoryException e) {
			
      IOUtils.err()
      .println(
          "APPROX: Treating unexpected type " + type + " bound variable as unknown" );
      
  		if(type.getKind().equals(IRType.Kind.UNKNOWN)) {
  			Type xtcType = ((IRUnknownType) type).getXtcType();
  			return unknown(xtcType);
  		}
  		
  		return getIntegerEncoding().unknown();
  	}
  }
	
	@Override
  public Expression boundExpression(String name, int index, IRType type, boolean fresh) {
		try {
			return encodingForType(type).boundExpression(name, index, type, fresh);
		} catch (ExpressionFactoryException e) {
  		
      IOUtils.err()
      .println(
          "APPROX: Treating unexpected type " + type + " bound expression as unknown" );
      
  		if(type.getKind().equals(IRType.Kind.UNKNOWN)) {
  			Type xtcType = ((IRUnknownType) type).getXtcType();
  			return unknown(xtcType);
  		}
  		
  		return getIntegerEncoding().unknown();
  	}
  }
  
  @Override
  public Expression notOverflow(Expression base, Expression size) {
  	Preconditions.checkArgument(isInteger(base) && isInteger(size));
  	return greaterThanOrEqual(plus(base, size), base);
  }
  
  @Override
  public Expression disjoint(Expression base1, Expression size1, Expression base2, Expression size2) {
  	Preconditions.checkArgument((isInteger(base1) && isInteger(base2)) || (isPointer(base1) && isPointer(base2)));
  	if(isInteger(base1)) {
    	Expression baseBound1 = plus(base1, size1);
    	Expression baseBound2 = plus(base2, size2);
    	return or(lessThan(baseBound1, base2), lessThan(baseBound2, base1));
  	} else {
    	return base1.neq(base2);
  	}
  }
  
  @Override
  public Expression disjoint(Expression base1, Expression size1, Expression base2) {
  	Preconditions.checkArgument((isInteger(base1) && isInteger(base2)) || (isPointer(base1) && isPointer(base2)));
  	if(isInteger(base1)) {
  		Expression baseBound1 = plus(base1, size1);
  		return or(lessThan(baseBound1, base2), lessThan(base2, base1));
  	} else {
    	return base1.neq(base2);
  	}
  }
  
  @Override
  public Expression within(Expression base1, Expression size1, Expression base2, Expression size2) {
  	Preconditions.checkArgument((isInteger(base1) && isInteger(base2)) || (isPointer(base1) && isPointer(base2)));
  	if(isInteger(base1)) {
  		Expression baseBound1 = plus(base1, size1);
  		Expression baseBound2 = plus(base2, size2);
  		return and(lessThanOrEqual(base1, base2), lessThan(baseBound2, baseBound1));
  	} else {
  		PointerEncoding<? extends Expression> pe = getPointerEncoding();
  		IntegerEncoding<? extends Expression> ie = getIntegerEncoding();
  		Expression baseBound1 = pointerPlus_(pe, ie, base1, size1);
  		Expression baseBound2 = pointerPlus_(pe, ie, base2, size2);
  		return and(pointerLessThanOrEqual_(pe, base1, base2), pointerLessThan_(pe, baseBound2, baseBound1));
  	}
  }
  
  @Override
  public Expression within(Expression base1, Expression size1, Expression base2) {
  	Preconditions.checkArgument((isInteger(base1) && isInteger(base2)) || (isPointer(base1) && isPointer(base2)));
  	if(isInteger(base1)) {
  		Expression baseBound1 = plus(base1, size1);
  		return and(lessThanOrEqual(base1, base2), lessThan(base2, baseBound1));
  	} else {
  		PointerEncoding<? extends Expression> pe = getPointerEncoding();
  		IntegerEncoding<? extends Expression> ie = getIntegerEncoding();
  		Expression baseBound1 = pointerPlus_(pe, ie, base1, size1);
  		return and(pointerLessThanOrEqual_(pe, base1, base2), pointerLessThan_(pe, base2, baseBound1));
  	}
  }
  
  @Override
  public Expression unknown(Type type) {
    type = type.resolve();
    
    if(type.isPointer())	return getPointerEncoding().unknown();
    
    if(type.isBoolean())	return getBooleanEncoding().unknown();
    
    long size = cTypeAnalyzer.getWidth(type);
  	return getIntegerEncoding().unknown(size);
  }
  
  @Override
	public Pair<Expression, Expression> arithTypeConversion(Expression lhs, Expression rhs,
			Type lhsType, Type rhsType) {

		lhs = castToInteger(lhs);	rhs = castToInteger(rhs);
		IntegerEncoding<?> ie = getIntegerEncoding();
		
		if(ie.getType().isInteger())	return Pair.of(lhs, rhs);
		
		Type targetType = cTypeAnalyzer.convert(lhsType, rhsType);
		int size = (int) cTypeAnalyzer.getWidth(targetType);
		
	  Expression lhsPrime = toInteger_(ie, lhs, size, !CType.isUnsigned(lhsType));
	  Expression rhsPrime = toInteger_(ie, rhs, size, !CType.isUnsigned(rhsType));
	  			
	  return Pair.of(lhsPrime, rhsPrime);
	}
}
