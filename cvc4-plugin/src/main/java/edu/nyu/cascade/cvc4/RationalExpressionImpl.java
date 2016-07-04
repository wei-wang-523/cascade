package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.POW;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.Type;

class RationalExpressionImpl extends ExpressionImpl implements
    RationalExpression {

	static RationalExpressionImpl mkConstant(ExpressionManagerImpl em,
	    final int numerator, final int denominator) {
		RationalExpressionImpl e = new RationalExpressionImpl(em, CONSTANT,
		    new NullaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em) {
				    return em.mkConst(new Rational(numerator, denominator));
			    }
		    });
		return e;
	}

	static RationalExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
	    Expression numerator, Expression denominator) {
		Preconditions.checkArgument(isRatOrInt(numerator));
		Preconditions.checkArgument(isRatOrInt(denominator));
		return new RationalExpressionImpl(exprManager, DIVIDE,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right) {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.DIVISION, left, right);
			    }
		    }, numerator, denominator);
	}

	static RationalExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new RationalExpressionImpl(exprManager, MINUS,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.MINUS, left, right);
			    }
		    }, a, b);
	}

	static RationalExpressionImpl mkMult(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new RationalExpressionImpl(exprManager, MULT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.MULT, left, right);
			    }
		    }, a, b);
	}

	static RationalExpressionImpl mkMult(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> terms) {
		Preconditions.checkArgument(!Iterables.isEmpty(terms));
		return new RationalExpressionImpl(exprManager, MULT,
		    new NaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				    Expr result = null;
				    for (Expr arg : args) {
					    if (result == null) {
						    result = arg;
					    } else {
						    result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.MULT, arg, result);
					    }
				    }
				    return result;
			    }

		    }, terms);
	}

	static RationalExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new RationalExpressionImpl(exprManager, PLUS,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.PLUS, left, right);
			    }
		    }, a, b);
	}

	static RationalExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> args) {
		Preconditions.checkArgument(!Iterables.isEmpty(args));
		return new RationalExpressionImpl(exprManager, PLUS,
		    new NaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				    Expr result = null;
				    for (Expr arg : args) {
					    if (result == null) {
						    result = arg;
					    } else {
						    result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.PLUS, arg, result);
					    }
				    }
				    return result;
			    }
		    }, args);
	}

	static RationalExpressionImpl mkPow(ExpressionManagerImpl exprManager,
	    Expression base, Expression exp) {
		return new RationalExpressionImpl(exprManager, POW,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.POW, left, right);
			    }
		    }, base, exp);
	}

	static RationalExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
	    Expression a) {
		return new RationalExpressionImpl(exprManager, UNARY_MINUS,
		    new UnaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left) throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.UMINUS, left);
			    }
		    }, a);
	}

	private static <T extends Type> boolean isRatOrInt(Expression e) {
		Type t = e.getType();
		return ((Type) t instanceof RationalType
		    || (Type) t instanceof IntegerType);
	}

	/*
	 * static RationalExpression mkDivideIntRat(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 * 
	 * static RationalExpression mkDivideRatInt(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 * 
	 * static RationalExpression mkDivideIntInt(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 */

	private RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    UnaryConstructionStrategy strategy, Expression a) {
		super(exprManager, kind, strategy, a);
	}

	private RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NullaryConstructionStrategy strategy) {
		super(exprManager, kind, strategy);
		setType(exprManager.rationalType());
	}

	private RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinaryConstructionStrategy strategy, Expression left, Expression right) {
		super(exprManager, kind, strategy, left, right);
		setType(getExpressionManager().rationalType());
	}

	private RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NaryConstructionStrategy strategy, Iterable<? extends Expression> args) {
		super(exprManager, kind, strategy, args);
		setType(getExpressionManager().rationalType());
	}

	private RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    Expr expr, RationalType type,
	    Iterable<? extends ExpressionImpl> children) {
		super(exprManager, kind, expr, type);
	}

	static RationalExpressionImpl create(ExpressionManagerImpl exprManager,
	    Kind kind, Expr expr, RationalType type,
	    Iterable<? extends ExpressionImpl> children) {
		return new RationalExpressionImpl(exprManager, kind, expr, type, children);
	}

	/*
	 * static RationalExpression mkDivideIntRat(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 * 
	 * static RationalExpression mkDivideRatInt(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 * 
	 * static RationalExpression mkDivideIntInt(IExpression numerator, IExpression
	 * denominator) { return new RationalExpression(DIVIDE, DIVIDE_STRATEGY,
	 * numerator, denominator); }
	 */

	@Override
	public RationalTypeImpl getType() {
		return getExpressionManager().rationalType();
	}

	public static RationalExpressionImpl valueOf(
	    ExpressionManagerImpl exprManager, Expression e) {
		if (e instanceof RationalExpressionImpl) {
			return (RationalExpressionImpl) e;
		} else {
			throw new IllegalArgumentException("RationalExpression.valueOf: " + e);
		}
	}

	@Override
	public RationalExpressionImpl divide(Expression e) {
		return getType().divide(this, e);
	}

	@Override
	public BooleanExpressionImpl gt(Expression e) {
		return getType().gt(this, e);
	}

	@Override
	public BooleanExpressionImpl geq(Expression e) {
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpressionImpl lt(Expression e) {
		return getType().lt(this, e);
	}

	@Override
	public BooleanExpressionImpl leq(Expression e) {
		return getType().leq(this, e);
	}

	@Override
	public RationalExpressionImpl mult(Expression e) {
		return getType().mult(this, e);
	}

	@Override
	public RationalExpressionImpl pow(Expression exp) {
		return getType().pow(this, exp);
	}

	@Override
	public RationalExpressionImpl minus(Expression e) {
		return getType().subtract(this, e);
	}

	@Override
	public RationalExpressionImpl plus(Expression e) {
		return getType().add(this, e);
	}

	/*
	 * public static RationalExpression mkMult( List<? extends IExpression> terms)
	 * { return new RationalExpression(MULT, new NaryConstructionStrategy() {
	 * 
	 * @Override public Expr apply(ExprManager em, List<Expr> args) throws
	 * Exception { return em.multExpr(args); } }, terms); }
	 */
}
