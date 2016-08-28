package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.APPLY;
import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.VARIABLE;
import static edu.nyu.cascade.prover.Expression.Kind.IF_THEN_ELSE;

import java.util.List;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.util.Identifiers;

/**
 * Base class encapsulating the z3 expressions.
 * 
 * @author dejan, wei
 */
class ExpressionImpl implements Expression {

	static interface BinaryConstructionStrategy {
		Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception;
	}

	static interface ArrayStoreAllConstructionStrategy {
		Expr apply(Context ctx, Sort type, Expr expr) throws Z3Exception;
	}

	static interface FuncApplyConstructionStrategy {
		Expr apply(Context ctx, FuncDecl func, Expr[] expr);
	}

	static interface BinderTriggersConstructionStrategy {
		Expr apply(Context ctx, Expr[] names, Expr body, Expr[] pattern,
				Expr[] noPatter, Symbol quantifierID, Symbol skolemID)
				throws Z3Exception;
	}

	static interface BinderTriggersDeBruijnConstructionStrategy {
		Expr apply(Context ctx, Sort[] sorts, Symbol[] names, Expr body,
				Expr[] pattern, Expr[] noPatter, Symbol quantifierID, Symbol skolemID)
				throws Z3Exception;
	}

	static interface NaryConstructionStrategy {
		Expr apply(Context ctx, Expr[] args) throws Z3Exception;
	}

	static interface NullaryConstructionStrategy {
		Expr apply(Context ctx) throws Z3Exception;
	}

	static interface TernaryConstructionStrategy {
		Expr apply(Context ctx, Expr arg1, Expr arg2, Expr arg3) throws Z3Exception;
	}

	static interface UnaryConstructionStrategy {
		Expr apply(Context ctx, Expr arg) throws Z3Exception;
	}

	static interface VariableConstructionStrategy {
		Expr apply(Context ctx, String name, Sort type) throws Z3Exception;
	}

	static interface BoundVariableConstructionStrategy {
		Expr apply(Context ctx, String name, Sort type) throws Z3Exception;
	}

	static interface ConstantConstructionStrategy {
		Expr apply(Context ctx, String name, Sort type);
	}

	static ExpressionImpl mkFunApply(final ExpressionManagerImpl exprManager,
			FunctionExpression fun, Iterable<? extends Expression> args) {
		Preconditions.checkArgument(fun.isFunction());
		Preconditions.checkArgument(fun.getArity() == Iterables.size(args));
		FunctionDeclarator funcDeclarator = (FunctionDeclarator) fun;
		final FuncDecl func = funcDeclarator.getFunc();
		ExpressionImpl result = new ExpressionImpl(exprManager, APPLY,
				new NaryConstructionStrategy() {
					@Override
					public Expr apply(Context ctx, Expr[] args) {
						try {
							return ctx.mkApp(func, args);
						} catch (Z3Exception e) {
							throw new TheoremProverException(e);
						}
					}
				}, args);
		result.setType(funcDeclarator.getRange());
		return result;
	}

	static ExpressionImpl mkFunApply(ExpressionManagerImpl exprManager,
			FunctionExpression fun, Expression firstArg, Expression... restArgs) {
		return mkFunApply(exprManager, fun, Lists.asList(firstArg, restArgs));
	}

	static ExpressionImpl mkIte(ExpressionManagerImpl exprManager,
			Expression cond, Expression thenPart, Expression elsePart) {
		Preconditions.checkArgument(cond.isBoolean());
		Preconditions.checkArgument(thenPart.getType().equals(elsePart.getType()));

		ExpressionImpl e = new ExpressionImpl(exprManager, IF_THEN_ELSE,
				new TernaryConstructionStrategy() {
					@Override
					public Expr apply(Context ctx, Expr arg1, Expr arg2, Expr arg3) {
						try {
							return ctx.mkITE((BoolExpr) arg1, arg2, arg3);
						} catch (Z3Exception e) {
							throw new TheoremProverException(e);
						}
					}
				}, cond, thenPart, elsePart);
		e.setType(thenPart.getType());
		return e;
	}

	static ExpressionImpl mkSubst(final ExpressionManagerImpl exprManager,
			final Expression expr, Iterable<? extends Expression> oldExprs,
			Iterable<? extends Expression> newExprs) {
		Preconditions
				.checkArgument(Iterables.size(oldExprs) == Iterables.size(newExprs));

		/* Don't bother to SUBST a constant */
		if (CONSTANT.equals(expr.getKind())) {
			return exprManager.importExpression(expr);
		}

		if (VARIABLE.equals(expr.getKind())) {
			if (!Iterables.contains(oldExprs, expr)) {
				return exprManager.importExpression(expr);
			}
		}

		Expr[] oldArgs = Iterables.toArray(
				Iterables.transform(oldExprs, new Function<Expression, Expr>() {
					@Override
					public Expr apply(Expression expr) {
						return exprManager.importExpression(expr).getZ3Expression();
					}
				}), Expr.class);

		Expr[] newArgs = Iterables.toArray(
				Iterables.transform(newExprs, new Function<Expression, Expr>() {
					@Override
					public Expr apply(Expression expr) {
						return exprManager.importExpression(expr).getZ3Expression();
					}
				}), Expr.class);

		try {
			Expr res = exprManager.toZ3Expr(expr).substitute(oldArgs, newArgs);
			return exprManager.importType(expr.getType()).createExpression(res, expr,
					exprManager.importExpressions(newExprs));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	/** The expression manager we are using. */
	private final ExpressionManagerImpl exprManager;

	/** The z3 expression we are using */
	private Expr z3_expr;

	/** The vector of children to return on request (read only) */
	private ImmutableList<? extends ExpressionImpl> children;

	/**
	 * A field to remember constant status at construction.
	 */
	private boolean constant;

	private boolean isVariable;

	private boolean isBound;

	private boolean isHoareLogic;

	private TypeImpl type;

	/**
	 * The name of a variable expression. <code>null</code> if the expression is
	 * not a variable.
	 */
	private String name;

	private final Kind kind;

	private ExpressionImpl(ExpressionManagerImpl em, Kind kind) {
		this.exprManager = em;
		this.kind = kind;
		init();
	}

	/* Copy constructor. */
	protected ExpressionImpl(ExpressionImpl e) {
		this.kind = e.getKind();
		init();
		exprManager = e.getExpressionManager();

		setZ3Expression(e.getZ3Expression());
		if (!e.getChildren().isEmpty()) {
			initChildren(e.getChildren());
		} else {
			children = ImmutableList.of();
		}
		setType(e.getType());
	}

	/*
	 * protected void setChildren(List<? extends Expression> children) {
	 * this.children = ImmutableList.copyOf(children); }
	 */

	/*
	 * NOTE: This constructor does not set z3_expr! The sub-class will be
	 * responsible for making sure it gets set!
	 */
	protected ExpressionImpl(final ExpressionManagerImpl exprManager,
			Expression expr) {
		this.exprManager = exprManager;
		this.kind = expr.getKind();
		init();

		children = ImmutableList.copyOf(Lists.transform(expr.getChildren(),
				new Function<Expression, ExpressionImpl>() {
					@Override
					public ExpressionImpl apply(Expression from) {
						return exprManager.importExpression(from);
					}
				}));
		setType(expr.getType());
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			ArrayStoreAllConstructionStrategy strategy, Type arrayType,
			Expression expr) {
		this(em, kind, arrayType);
		init(expr);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprManager != null);
		assert (exprs.length == 1);

		// Get the body z3 expressions
		Expr body_expr = exprs[0];

		try {
			// Get the z3 expression manager
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();

			// Create the new expression
			Sort atype = type.getZ3Type();
			setZ3Expression(strategy.apply(z3_ctx, atype, body_expr));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			BinaryConstructionStrategy strategy, Expression left, Expression right) {
		this(em, kind);
		init(left, right);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprManager != null);
		assert (exprs.length == 2);

		// Get the left and right z3 expressions
		Expr left_expr = exprs[0];
		Expr right_expr = exprs[1];

		try {
			// Get the z3 expression manager
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();

			// Create the new expression
			setZ3Expression(strategy.apply(z3_ctx, left_expr, right_expr));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(final ExpressionManagerImpl em,
			FuncApplyConstructionStrategy strategy, FunctionDeclarator funcDecl,
			Expression var) {
		this(em, APPLY, funcDecl.getRange());
		init(var);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprs.length == 1);

		try {
			final Context z3_ctx = getExpressionManager().getTheoremProver()
					.getZ3Context();

			FuncDecl func = funcDecl.getFunc();

			// Call the construct method for quantification
			setZ3Expression(strategy.apply(z3_ctx, func, exprs));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(final ExpressionManagerImpl em,
			FuncApplyConstructionStrategy strategy, FunctionDeclarator funcDecl,
			Iterable<? extends Expression> vars) {
		this(em, APPLY, funcDecl.getRange());
		init(vars);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprs.length >= 1);

		try {
			final Context z3_ctx = getExpressionManager().getTheoremProver()
					.getZ3Context();

			FuncDecl func = funcDecl.getFunc();

			// Call the construct method for quantification
			setZ3Expression(strategy.apply(z3_ctx, func, exprs));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(final ExpressionManagerImpl em, Kind kind,
			BinderTriggersConstructionStrategy strategy,
			Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns) {
		this(em, kind);
		init(body);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprs.length == 1);

		Expr z3_body = exprs[0];

		try {
			Function<Expression, Expr> toZ3Expr = new Function<Expression, Expr>() {
				@Override
				public Expr apply(Expression expr) {
					return em.toZ3Expr(expr);
				}
			};

			final Context z3_ctx = em.getTheoremProver().getZ3Context();

			Expr[] z3_vars = null;
			if (vars != null)
				z3_vars = Iterables.toArray(Iterables.transform(vars, toZ3Expr),
						Expr.class);

			Expr[] z3_pattern = null;
			if (patterns != null)
				z3_pattern = Iterables.toArray(Iterables.transform(patterns, toZ3Expr),
						Expr.class);

			Expr[] z3_no_pattern = null;
			if (noPatterns != null)
				z3_no_pattern = Iterables
						.toArray(Iterables.transform(noPatterns, toZ3Expr), Expr.class);

			// String quantifierID = Identifiers.uniquify("Q").replace("_", "");
			// String skolemID = Identifiers.uniquify("skid").replace("_", "");
			//
			// Symbol z3_qid = z3_ctx.mkSymbol(quantifierID);
			// Symbol z3_skid = z3_ctx.mkSymbol(skolemID);

			// Don't set quantifier id and skolem id
			setZ3Expression(strategy.apply(z3_ctx, z3_vars, z3_body, z3_pattern,
					z3_no_pattern, null, null));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(final ExpressionManagerImpl em, Kind kind,
			BinderTriggersDeBruijnConstructionStrategy strategy,
			Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns) {
		this(em, kind);
		init(body);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprs.length == 1);

		Expr z3_body = exprs[0];

		try {
			final Context z3_ctx = em.getTheoremProver().getZ3Context();

			Symbol[] z3_names = null;
			Sort[] z3_sorts = null;

			if (vars != null) {
				z3_names = Iterables.toArray(
						Iterables.transform(vars, new Function<Expression, Symbol>() {
							@Override
							public Symbol apply(Expression expr) {
								return ((BoundExpressionImpl) expr.asBound()).getSymbol();
							}
						}), Symbol.class);

				z3_sorts = Iterables.toArray(
						Iterables.transform(vars, new Function<Expression, Sort>() {
							@Override
							public Sort apply(Expression expr) {
								return em.toZ3Type(expr.getType());
							}
						}), Sort.class);
			}

			Function<Expression, Expr> toZ3Expr = new Function<Expression, Expr>() {
				@Override
				public Expr apply(Expression expr) {
					return em.toZ3Expr(expr);
				}
			};

			Expr[] z3_pattern = null;
			if (patterns != null)
				z3_pattern = Iterables.toArray(Iterables.transform(patterns, toZ3Expr),
						Expr.class);

			Expr[] z3_no_pattern = null;
			if (noPatterns != null)
				z3_no_pattern = Iterables
						.toArray(Iterables.transform(noPatterns, toZ3Expr), Expr.class);

			// String quantifierID = Identifiers.uniquify("Q").replace("_", "");
			// String skolemID = Identifiers.uniquify("skid").replace("_", "");
			//
			// Symbol z3_qid = z3_ctx.mkSymbol(quantifierID);
			// Symbol z3_skid = z3_ctx.mkSymbol(skolemID);

			// Don't set quantifier id and skolem id
			setZ3Expression(strategy.apply(z3_ctx, z3_sorts, z3_names, z3_body,
					z3_pattern, z3_no_pattern, null, null));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind, Expr e,
			Type type) {
		this(em, kind, type);
		setZ3Expression(e);
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind, Expr expr,
			Type type, Iterable<? extends ExpressionImpl> children) {
		this(em, kind, expr, type);
		initChildren(children);
	}

	/**
	 * Constructs the expression by just setting the expression manager. The
	 * inheriting class is responsible for setting up the other properties of the
	 * expression, specially the z3_expr and the children list. Use with care.
	 * 
	 * @param em
	 *          the expression manager.
	 */
	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind, Type type) {
		this(em, kind);
		setType(type);
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			NaryConstructionStrategy strategy, Expression first, Expression... rest) {
		this(em, kind, strategy, Lists.asList(first, rest));
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			NaryConstructionStrategy strategy, Expression first, Expression second,
			Expression... rest) {
		this(em, kind, strategy, Lists.asList(first, second, rest));
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			NaryConstructionStrategy strategy,
			Iterable<? extends Expression> subExpressions) {
		this(em, kind);
		init(subExpressions);
		Expr[] exprs = convertChildrenToExpr();

		try {
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();
			setZ3Expression(strategy.apply(z3_ctx, exprs));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			NullaryConstructionStrategy strategy) {
		this(em, kind);

		try {
			// Get the z3 expression manager
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();
			setZ3Expression(strategy.apply(z3_ctx));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			TernaryConstructionStrategy strategy, Expression arg1, Expression arg2,
			Expression arg3) {
		this(em, kind);
		init(arg1, arg2, arg3);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprManager != null);
		assert (exprs.length == 3);

		// Get the left and right z3 expressions
		Expr expr1 = exprs[0];
		Expr expr2 = exprs[1];
		Expr expr3 = exprs[2];

		try {
			// Get the z3 expression manager
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();

			// Create the new expression
			Expr expr = strategy.apply(z3_ctx, expr1, expr2, expr3);
			setZ3Expression(expr);

			Sort sort = expr.getSort();
			setType(exprManager.toType(sort));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
			UnaryConstructionStrategy strategy, Expression subExpression) {
		this(em, kind);
		init(subExpression);
		Expr[] exprs = convertChildrenToExpr();

		assert (exprManager != null);
		assert (exprs.length == 1);

		// Get the subexpression
		Expr expr = exprs[0];

		try {
			// Get the z3 expression manager
			Context z3_ctx = exprManager.getTheoremProver().getZ3Context();

			// Create the new expression
			setZ3Expression(strategy.apply(z3_ctx, expr));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	/*
	 * TODO: Should probably move uniquify out of this package entirely. It has to
	 * be up to clients to make sure their identifiers don't collide. Otherwise,
	 * augment current variable creation functions with "fresh" variants.
	 */
	protected ExpressionImpl(ExpressionManagerImpl em,
			VariableConstructionStrategy strategy, String name, Type itype,
			boolean uniquify) {
		this(em, Kind.VARIABLE, itype);
		assert (type != null);

		String actualName = uniquify ? Identifiers.uniquify(name) : name;

		this.name = actualName;

		try {
			// Get the z3 expression manager
			Context z3_ctx = em.getTheoremProver().getZ3Context();

			// Create the new expression
			setZ3Expression(strategy.apply(z3_ctx, actualName, type.getZ3Type()));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em,
			BoundVariableConstructionStrategy strategy, String name, Type itype,
			boolean uniquify) {
		this(em, Kind.BOUND, itype);
		assert (type != null);

		String actualName = uniquify ? Identifiers.uniquify(name) : name;
		this.name = actualName;

		try {
			Context z3_ctx = em.getTheoremProver().getZ3Context();
			setZ3Expression(strategy.apply(z3_ctx, actualName, type.getZ3Type()));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	protected ExpressionImpl(ExpressionManagerImpl em,
			ConstantConstructionStrategy strategy, String name, Type itype,
			boolean uniquify) {
		this(em, Kind.CONSTANT, itype);
		assert (type != null);

		String actualName = uniquify ? Identifiers.uniquify(name) : name;

		this.name = actualName;

		try {
			// Get the z3 expression manager
			Context z3_ctx = em.getTheoremProver().getZ3Context();

			// Create the new expression
			setZ3Expression(strategy.apply(z3_ctx, actualName, type.getZ3Type()));
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	Expr getZ3Expression() {
		return z3_expr;
	}

	public String getName() {
		return name;
	}

	private void setConstant(boolean constant) {
		this.constant = constant;
	}

	private void setConstantFromChildren() {
		setConstant(Iterables.all(children, new Predicate<ExpressionImpl>() {
			public boolean apply(ExpressionImpl expr) {
				return expr.isConstant();
			}
		}));
	}

	private void setIsVariable(boolean b) {
		this.isVariable = b;
	}

	private void setIsBound(boolean b) {
		this.isBound = b;
	}

	void setZ3Expression(Expr z3_expr) {
		this.z3_expr = z3_expr;
	}

	void setName(String name) {
		this.name = name;
	}

	void setType(Type type) {
		this.type = getExpressionManager().importType(type);
	}

	private void init() {
		z3_expr = null;
		children = ImmutableList.of();
		setConstant(kind.equals(Kind.CONSTANT));
		setIsVariable(kind.equals(Kind.VARIABLE));
		setIsBound(kind.equals(Kind.BOUND));
	}

	private void init(Expression first, Expression... rest) {
		init(Lists.asList(first, rest));
	}

	private void init(Iterable<? extends Expression> subExpressions) {
		initChildren(subExpressions);
		setConstantFromChildren();
	}

	private void initChildren(Iterable<? extends Expression> subExpressions) {
		/*
		 * TODO: Is there a reason we won't take an empty Iterable here? See
		 * BooleanExpression for an example of why this is annoying [chris 1/7/10]
		 * I'm guessing no. I think the old reason was, we needed one of the
		 * children to provide the ExpressionManager, but now we're passing in the
		 * ExpressionManager in the constructors.
		 */
		// checkArgument(!Iterables.isEmpty(subExpressions));
		children = new ImmutableList.Builder<ExpressionImpl>()
				.addAll(getExpressionManager().importExpressions(subExpressions))
				.build();
	}

	private Expr[] convertChildrenToExpr() {
		Expr[] res = new Expr[children.size()];

		for (int i = 0; i < res.length; i++) {
			res[i] = children.get(i).getZ3Expression();
		}
		return res;
	}

	@Override
	public BitVectorExpressionImpl asBitVector() {
		Preconditions.checkState(isBitVector());
		return getExpressionManager().asBitVector(this);
	}

	@Override
	public BooleanExpressionImpl asBooleanExpression() {
		Preconditions.checkState(isBoolean());
		return getExpressionManager().asBooleanExpression((ExpressionImpl) this);
	}

	@Override
	public IntegerExpressionImpl asIntegerExpression() {
		Preconditions.checkState(isInteger());
		return getExpressionManager().asIntegerExpression(this);
	}

	@Override
	public RationalExpressionImpl asRationalExpression() {
		Preconditions.checkState(isRational());
		return getExpressionManager().asRationalExpression(this);
	}

	@Override
	public FunctionExpression asFunctionExpression() {
		Preconditions.checkState(isFunction());
		return getExpressionManager().asFunctionExpression(this);
	}

	@Override
	public VariableExpressionImpl asVariable() {
		Preconditions.checkState(isVariable());
		return getExpressionManager().asVariable(this);
	}

	@Override
	public BoundExpression asBound() {
		Preconditions.checkState(isBound());
		return getExpressionManager().asBoundExpression(this);
	}

	@Override
	public BooleanExpressionImpl eq(Expression e) {
		ExpressionManagerImpl exprManager = getExpressionManager();
		return exprManager.asBooleanExpression(exprManager.eq(this, e));
	}

	@Override
	public boolean equals(Object obj) {
		Preconditions.checkNotNull(z3_expr);
		if (obj instanceof Expression) {
			Expr z3_expr_that = getExpressionManager()
					.importExpression((Expression) obj).getZ3Expression();
			if (z3_expr_that == null)
				return false;
			return z3_expr.equals(z3_expr_that);

		}
		return super.equals(obj);
	}

	@Override
	public int getArity() {
		return children.size();
	}

	@Override
	public Expression getChild(int i) {
		Preconditions.checkArgument(i >= 0 && i < getArity());
		return getChildren().get(i);
	}

	@Override
	public ImmutableList<? extends ExpressionImpl> getChildren() {
		return children;
	}

	@Override
	public ExpressionManagerImpl getExpressionManager() {
		return exprManager;
	}

	@Override
	public Kind getKind() {
		return kind;
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public int hashCode() {
		return getZ3Expression().hashCode();
	}

	@Override
	public final boolean isConstant() {
		return constant;
	}

	@Override
	public final boolean isVariable() {
		return isVariable;
	}

	@Override
	public final boolean isBound() {
		return isBound;
	}

	@Override
	public BooleanExpression neq(Expression e) {
		return getExpressionManager().neq(this, e);
	}

	@Override
	public Expression subst(Expression oldExpr, Expression newExpr) {
		List<Expression> oldExprs = Lists.newArrayList();
		oldExprs.add(oldExpr);
		List<Expression> newExprs = Lists.newArrayList();
		newExprs.add(newExpr);
		return subst(oldExprs, newExprs);
	}

	@Override
	public Expression subst(Iterable<? extends Expression> oldExprs,
			Iterable<? extends Expression> newExprs) {
		return mkSubst(getExpressionManager(), this, oldExprs, newExprs);
	}

	@Override
	public Expression simplify() {
		try {
			Expr z3_expr_simp = z3_expr.simplify();
			return new ExpressionImpl(getExpressionManager(), kind, z3_expr_simp,
					type);
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public void setHoareLogic(boolean bool) {
		this.isHoareLogic = bool;
	}

	@Override
	public boolean isHoareLogic() {
		return isHoareLogic;
	}

	@Override
	public String toString() {
		return getZ3Expression().toString();
	}

	@Override
	public boolean isBoolean() {
		return getType().equals(getExpressionManager().booleanType());
	}

	@Override
	public ArrayExpression asArray() {
		Preconditions.checkArgument(isArray());
		return ArrayExpressionImpl.valueOf(this);
	}

	/*
	 * @SuppressWarnings("unchecked")
	 * 
	 * @Override public ArrayExpression asArray(Type indexType) {
	 * Preconditions.checkArgument(isArray(indexType)); return (ArrayExpression)
	 * this; }
	 * 
	 * @SuppressWarnings("unchecked")
	 * 
	 * @Override public <I extends Type, E extends Type> ArrayExpression asArray(
	 * I indexType, E elementType) {
	 * Preconditions.checkArgument(isArray(indexType,elementType)); return
	 * (ArrayExpression) this; }
	 */

	@Override
	public boolean isArray() {
		return getType() instanceof ArrayType;
	}

	/*
	 * @Override public <I extends Type> boolean isArray(I indexType) { return
	 * isArray() && ((ArrayType)getType()).getIndexType().equals(indexType); }
	 * 
	 * @Override public boolean isArray(Expression indexType, Expression
	 * elementType) { return isArray(indexType) &&
	 * ((ArrayType)getType()).getElementType().equals(elementType); }
	 */
	@Override
	public boolean isBitVector() {
		return getType() instanceof BitVectorType;
	}

	@Override
	public boolean isInteger() {
		return getType() instanceof IntegerType;
	}

	@Override
	public boolean isRational() {
		return getType() instanceof RationalType;
	}

	@Override
	public boolean isFunction() {
		return getType() instanceof FunctionType;
	}

	@Override
	public InductiveExpression asInductive() {
		Preconditions.checkState(isInductive());
		return getExpressionManager().asInductive(this);
	}

	@Override
	public boolean isInductive() {
		return getType() instanceof InductiveType;
	}

	@Override
	public TupleExpression asTuple() {
		Preconditions.checkState(isTuple());
		return getExpressionManager().asTuple(this);
	}

	@Override
	public boolean isTuple() {
		return getType() instanceof TupleType;
	}

	@Override
	public RecordExpression asRecord() {
		Preconditions.checkState(isRecord());
		return getExpressionManager().asRecord(this);
	}

	@Override
	public boolean isRecord() {
		return getType() instanceof RecordType;
	}

	@Override
	public UninterpretedExpression asUninterpreted() {
		return getExpressionManager().asUninterpreted(this);
	}

	@Override
	public boolean isUninterpreted() {
		return getType() instanceof UninterpretedType;
	}
}
