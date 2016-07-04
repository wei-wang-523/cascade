package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.BV_AND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_CONCAT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_EXTRACT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NAND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NEG;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_OR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_SIGN_EXTEND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_ZERO_EXTEND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_LSHIFT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_RSHIFT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_XNOR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_XOR;
import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.SDIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.REM;
import static edu.nyu.cascade.prover.Expression.Kind.SREM;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;

import java.math.BigInteger;
import java.util.Collections;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.Pair;

final class BitVectorExpressionImpl extends ExpressionImpl implements
    BitVectorExpression {
	static final LoadingCache<ExpressionManagerImpl, LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl>> cache = CacheBuilder
	    .newBuilder().build(
	        new CacheLoader<ExpressionManagerImpl, LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl>>() {
		        public LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl> load(
	              final ExpressionManagerImpl exprManager) {
			        return CacheBuilder.newBuilder().build(
	                new CacheLoader<Pair<String, Integer>, BitVectorExpressionImpl>() {
		                public BitVectorExpressionImpl load(
	                      Pair<String, Integer> pair) {
			                return new BitVectorExpressionImpl(exprManager, pair
	                        .fst(), pair.snd());
		                }
	                });
		        }
	        });

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    int size, int value) {
		Preconditions.checkArgument(size >= 0);
		try {
			String decimalRep = Integer.toString(value);
			return cache.get(exprManager).get(Pair.of(decimalRep, size));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    int size, long value) {
		Preconditions.checkArgument(size >= 0);
		try {
			String decimalRep = Long.toString(value);
			return cache.get(exprManager).get(Pair.of(decimalRep, size));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    int size, BigInteger value) {
		Preconditions.checkArgument(size >= 0);
		try {
			String decimalRep = value.toString();
			return cache.get(exprManager).get(Pair.of(decimalRep, size));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    int c) {
		try {
			String decimalRep = Integer.toString(c);
			int len = Integer.toBinaryString(c).length();
			return cache.get(exprManager).get(Pair.of(decimalRep, len));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    long c) {
		try {
			String decimalRep = Long.toString(c);
			int len = Long.toBinaryString(c).length();
			return cache.get(exprManager).get(Pair.of(decimalRep, len));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    BigInteger c) {
		try {
			return cache.get(exprManager).get(Pair.of(c.toString(), c.bitLength()));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
	    String binaryRep) {
		try {
			return cache.get(exprManager).get(Pair.of(binaryRep, binaryRep.length()));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	static BitVectorExpressionImpl mkConcat(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_CONCAT, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkConcat((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	/* TODO: AND, OR, XOR have n-ary variants */
	static BitVectorExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_AND, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVAND((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkZeroExtend(ExpressionManagerImpl exprManager,
	    final int size, Expression arg) {
		Preconditions.checkArgument(arg.isBitVector());
		Preconditions.checkArgument(size >= arg.asBitVector().getSize());
		final int argSize = arg.asBitVector().getSize();

		if (argSize == size)
			return valueOf(exprManager, arg);

		return mkUnary(exprManager, BV_ZERO_EXTEND,
		    new UnaryConstructionStrategy() {
			    @Override
			    public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				    return ctx.mkZeroExt(size - argSize, (BitVecExpr) arg);
			    }
		    }, arg, size);
	}

	static BitVectorExpressionImpl mkExtract(ExpressionManagerImpl exprManager,
	    Expression arg, final int high, final int low) {
		Preconditions.checkArgument(arg.isBitVector());
		Preconditions.checkArgument(0 <= low);
		Preconditions.checkArgument(low <= high);
		Preconditions.checkArgument(high < arg.asBitVector().getSize());

		int size = high - low + 1;
		return mkUnary(exprManager, BV_EXTRACT, new UnaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				return ctx.mkExtract(high, low, (BitVecExpr) arg);
			}
		}, arg, size);
	}

	static BitVectorExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, MINUS, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVSub((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkMult(final ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());

		return mkBinary(exprManager, MULT, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVMul((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkMult(final ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> args) {
		Preconditions.checkArgument(!Iterables.isEmpty(args));
		return mkNary(exprManager, MULT, new NaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
				BitVecExpr result = null;
				for (Expr arg : args) {
					BitVecExpr bvArg = (BitVecExpr) arg;
					if (result == null) {
						result = bvArg;
					} else {
						result = ctx.mkBVMul(result, bvArg);
					}
				}
				return result;
			}
		}, args);
	}

	static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
	    Expression first, Expression... rest) {
		return mkMult(exprManager, Lists.asList(first, rest));
	}

	static BitVectorExpressionImpl mkSDivide(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, SDIVIDE, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVSDiv((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	/* TODO: AND, OR, XOR have n-ary variants */

	static BitVectorExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, DIVIDE, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVUDiv((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkSRem(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, SREM, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVSRem((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkRem(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, REM, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVURem((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkNand(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_NAND, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVNAND((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkNor(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_NOR, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVNOR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkNot(ExpressionManagerImpl exprManager,
	    Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		int size = a.asBitVector().getSize();
		return mkUnary(exprManager, BV_NOT, new UnaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				return ctx.mkBVNot((BitVecExpr) arg);
			}
		}, a, size);
	}

	static BitVectorExpressionImpl mkNegate(ExpressionManagerImpl exprManager,
	    Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		int size = a.asBitVector().getSize();
		return mkUnary(exprManager, BV_NEG, new UnaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				return ctx.mkBVNeg((BitVecExpr) arg);
			}
		}, a, size);
	}

	static BitVectorExpressionImpl mkOr(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_OR, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVOR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkPlus(final ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> args) {
		Preconditions.checkArgument(!Iterables.isEmpty(args));

		return mkNary(exprManager, PLUS, new NaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
				Expr result = null;
				for (Expr arg : args) {
					if (result == null) {
						result = arg;
					} else {
						result = ctx.mkBVAdd((BitVecExpr) result, (BitVecExpr) arg);
					}
				}
				return result;
			}
		}, args);
	}

	static BitVectorExpressionImpl mkSignExtend(ExpressionManagerImpl exprManager,
	    final int size, Expression arg) {
		Preconditions.checkArgument(arg.isBitVector());
		Preconditions.checkArgument(size >= arg.asBitVector().getSize());
		final int argSize = arg.asBitVector().getSize();

		if (argSize == size)
			return valueOf(exprManager, arg);

		return mkUnary(exprManager, BV_SIGN_EXTEND,
		    new UnaryConstructionStrategy() {
			    @Override
			    public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				    return ctx.mkSignExt(size - argSize, (BitVecExpr) arg);
			    }
		    }, arg, size);
	}

	static BitVectorExpressionImpl mkPlus(final ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return mkBinary(exprManager, PLUS, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVAdd((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
	    Expression first, Expression... rest) {
		return mkPlus(exprManager, Lists.asList(first, rest));
	}

	static BitVectorExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
	    Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		int size = a.asBitVector().getSize();
		return mkUnary(exprManager, UNARY_MINUS, new UnaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr arg) throws Z3Exception {
				return ctx.mkBVNeg((BitVecExpr) arg);
			}
		}, a, size);
	}

	static BitVectorExpressionImpl mkXnor(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_XNOR, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVXNOR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkXor(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_XOR, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVXOR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	/* TODO: AND, OR, XOR have n-ary variants */

	static BitVectorExpressionImpl mkLShift(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_LSHIFT, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVSHL((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkRShift(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_RSHIFT, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVLSHR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl mkSRShift(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		return mkBinary(exprManager, BV_RSHIFT, new BinaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
				return ctx.mkBVASHR((BitVecExpr) left, (BitVecExpr) right);
			}
		}, a, b);
	}

	static BitVectorExpressionImpl valueOf(ExpressionManagerImpl exprManager,
	    Expression e) {
		if (exprManager.equals(e.getExpressionManager())) {
			if (e instanceof BitVectorExpressionImpl) {
				return (BitVectorExpressionImpl) e;
			} else if (e instanceof ExpressionImpl) {
				return new BitVectorExpressionImpl((ExpressionImpl) e);
			}
		}
		throw new UnsupportedOperationException();
	}

	static BitVectorExpressionImpl typeConversion(
	    ExpressionManagerImpl exprManager, int size, Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		BitVectorExpression bv = a.asBitVector();

		int exprSize = bv.getSize();
		if (exprSize == size)
			return valueOf(exprManager, bv);

		if (exprSize > size)
			return mkExtract(exprManager, bv, size - 1, 0);

		return mkSignExtend(exprManager, size, bv);
	}

	private static BitVectorExpressionImpl mkBinary(
	    ExpressionManagerImpl exprManager, Kind kind,
	    BinaryConstructionStrategy strategy, Expression a, Expression b) {

		BitVectorType aType = a.asBitVector().getType();
		BitVectorType bType = b.asBitVector().getType();

		int size = 0;

		Expression lhs, rhs;
		switch (kind) {
		case BV_AND:
		case BV_NAND:
		case BV_NOR:
		case BV_OR:
		case BV_XOR:
		case PLUS:
		case DIVIDE:
		case SDIVIDE:
		case MINUS:
		case MULT:
		case REM:
		case SREM:
		case BV_LSHIFT:
		case BV_RSHIFT: {
			size = Math.max(aType.getSize(), bType.getSize());
			lhs = typeConversion(exprManager, size, a);
			rhs = typeConversion(exprManager, size, b);
			break;
		}
		case BV_CONCAT: {
			size = aType.getSize() + bType.getSize();
			lhs = a;
			rhs = b;
			break;
		}
		default:
			throw new IllegalArgumentException("Unknown kind " + kind);
		}

		BitVectorExpressionImpl expr = new BitVectorExpressionImpl(exprManager,
		    kind, strategy, lhs, rhs);
		expr.setType(exprManager.bitVectorType(size));
		return expr;
	}

	private static BitVectorExpressionImpl mkNary(
	    final ExpressionManagerImpl exprManager, final Kind kind,
	    NaryConstructionStrategy strategy, Iterable<? extends Expression> args) {
		int maxSize = 0;
		for (Expression arg : args) {
			assert arg.isBitVector();
			maxSize = Math.max(maxSize, arg.asBitVector().getSize());
		}

		final int size = maxSize;
		Iterable<? extends Expression> argsPrime = Iterables.transform(args,
		    new Function<Expression, Expression>() {
			    @Override
			    public Expression apply(Expression input) {
				    switch (kind) {
				    case BV_AND:
				    case BV_NAND:
				    case BV_NOR:
				    case BV_OR:
				    case BV_XOR:
				    case PLUS:
				    case MULT: {
					    return typeConversion(exprManager, size, input);
				    }
				    default:
					    throw new IllegalArgumentException("Unknown kind " + kind);
				    }
			    }
		    });

		BitVectorExpressionImpl expr = new BitVectorExpressionImpl(exprManager,
		    kind, strategy, argsPrime);
		expr.setType(exprManager.bitVectorType(size));
		return expr;
	}

	private static BitVectorExpressionImpl mkUnary(
	    ExpressionManagerImpl exprManager, Kind kind,
	    UnaryConstructionStrategy strategy, Expression a, int size) {
		Preconditions.checkArgument(a.isBitVector());
		BitVectorExpressionImpl expr = new BitVectorExpressionImpl(exprManager,
		    kind, strategy, a);
		expr.setType(exprManager.bitVectorType(size));
		return expr;
	}

	static BitVectorExpressionImpl create(ExpressionManagerImpl em, Kind kind,
	    Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
		Preconditions.checkArgument(type.isBitVectorType());
		return new BitVectorExpressionImpl(em, kind, expr, type.asBitVectorType(),
		    children);
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinaryConstructionStrategy strategy, Expression a, Expression b) {
		super(exprManager, kind, strategy, a, b);
	}

	private BitVectorExpressionImpl(ExpressionImpl bv) {
		super(bv);
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager,
	    Expression e) {
		super(exprManager, e);
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager,
	    final String decimalRep, final int len) {
		super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
			@Override
			public Expr apply(Context ctx) throws Z3Exception {
				return ctx.mkBV(decimalRep, len);
			}
		});
		setType(BitVectorTypeImpl.create(exprManager, len));
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl em, Kind kind,
	    Expr expr, BitVectorType type,
	    Iterable<? extends ExpressionImpl> children) {
		super(em, kind, expr, type, children);
	}

	/* TODO: AND, OR, XOR have n-ary variants */

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NaryConstructionStrategy strategy, Expression first, Expression[] rest) {
		super(exprManager, kind, strategy, first, rest);
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    UnaryConstructionStrategy strategy, Expression a) {
		super(exprManager, kind, strategy, a);
		setType(a.getType());
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NaryConstructionStrategy strategy, Iterable<? extends Expression> args) {
		super(exprManager, kind, strategy, args);
	}

	private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    TernaryConstructionStrategy strategy, Expression arg1, Expression arg2,
	    Expression arg3) {
		super(exprManager, kind, strategy, arg1, arg2, arg3);
	}

	@Override
	public BitVectorExpressionImpl and(Expression a) {
		return mkAnd(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl concat(Expression a) {
		return mkConcat(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl extract(int i, int j) {
		return mkExtract(getExpressionManager(), this, i, j);

	}

	@Override
	public int getSize() {
		return getType().getSize();
	}

	@Override
	public BitVectorType getType() {
		return super.getType().asBitVectorType();
	}

	@Override
	public BitVectorExpressionImpl minus(Expression a) {
		return mkMinus(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl nand(Expression a) {
		return mkNand(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl nor(Expression a) {
		return mkNor(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl not() {
		return mkNot(getExpressionManager(), this);
	}

	@Override
	public BitVectorExpressionImpl neg() {
		return mkNegate(getExpressionManager(), this);
	}

	@Override
	public BitVectorExpressionImpl or(Expression a) {
		return mkOr(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl plus(Expression a) {
		return mkPlus(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl plus(Expression... args) {
		return mkPlus(getExpressionManager(), this, args);
	}

	@Override
	public BitVectorExpressionImpl plus(Iterable<? extends Expression> args) {
		return mkPlus(getExpressionManager(), Iterables.concat(Collections
		    .singletonList(this), args));
	}

	@Override
	public BitVectorExpressionImpl times(Expression a) {
		return mkMult(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpression times(Expression... args) {
		return mkMult(getExpressionManager(), this, args);
	}

	@Override
	public BitVectorExpression times(Iterable<? extends Expression> args) {
		return mkMult(getExpressionManager(), Iterables.concat(Collections
		    .singletonList(this), args));
	}

	@Override
	public BitVectorExpressionImpl divides(Expression a) {
		return mkDivide(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl signedDivides(Expression a) {
		return mkSDivide(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl rems(Expression a) {
		return mkRem(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl signedRems(Expression a) {
		return mkSRem(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl xnor(Expression a) {
		return mkXnor(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl xor(Expression a) {
		return mkXor(getExpressionManager(), this, a);
	}

	@Override
	public BooleanExpression greaterThan(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().gt(this, e);
	}

	@Override
	public BooleanExpression greaterThanOrEqual(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpression lessThan(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().lt(this, e);
	}

	@Override
	public BooleanExpression lessThanOrEqual(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().leq(this, e);
	}

	@Override
	public BitVectorExpressionImpl lshift(Expression a) {
		Preconditions.checkArgument(a.isInteger() || a.isBitVector());
		return mkLShift(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl rshift(Expression a) {
		Preconditions.checkArgument(a.isInteger() || a.isBitVector());
		return mkRShift(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl signedRshift(Expression a) {
		Preconditions.checkArgument(a.isInteger() || a.isBitVector());
		return mkSRShift(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl zeroExtend(int size) {
		return mkZeroExtend(getExpressionManager(), size, this);
	}

	@Override
	public BitVectorExpressionImpl signExtend(int size) {
		return mkSignExtend(getExpressionManager(), size, this);
	}

	@Override
	public BitVectorExpressionImpl uminus() {
		return mkUminus(getExpressionManager(), this);
	}
}
