package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.TUPLE;
import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_INDEX;
import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_UPDATE;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.TupleSelect;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

final class TupleExpressionImpl extends ExpressionImpl implements
		TupleExpression {
	static TupleExpressionImpl create(ExpressionManagerImpl exprManager,
			Type type, Expression first, Expression... rest) {
		return new TupleExpressionImpl(exprManager, type, Lists.asList(first,
				rest));
	}

	static TupleExpressionImpl create(ExpressionManagerImpl exprManager,
			Type type, Iterable<? extends Expression> elements) {
		Preconditions.checkArgument(!Iterables.isEmpty(elements));
		return new TupleExpressionImpl(exprManager, type, elements);
	}

	static TupleExpressionImpl create(ExpressionManagerImpl exprManager,
			Kind kind, Expr expr, TupleType type,
			Iterable<? extends ExpressionImpl> children) {
		return new TupleExpressionImpl(exprManager, kind, expr, type, children);
	}

	static TupleExpressionImpl valueOf(ExpressionManagerImpl exprManager,
			ExpressionImpl expr) {
		Preconditions.checkArgument(expr.isTuple());
		if (exprManager.equals(expr.getExpressionManager())) {
			if (expr instanceof TupleExpressionImpl) {
				return (TupleExpressionImpl) expr;
			} else {
				return new TupleExpressionImpl((ExpressionImpl) expr);
			}
		}

		switch (expr.getKind()) {
		default:
			throw new UnsupportedOperationException();
		}
	}

	static ExpressionImpl mkTupleIndex(ExpressionManagerImpl exprManager,
			Expression tuple, final int index) {
		ExpressionImpl result = new ExpressionImpl(exprManager, TUPLE_INDEX,
				new UnaryConstructionStrategy() {
					@Override
					public Expr apply(ExprManager em, Expr tuple) {
						Expr indexExpr = em.mkConst(new TupleSelect(index));
						return em.mkExpr(edu.nyu.acsys.CVC4.Kind.TUPLE_SELECT, indexExpr,
								tuple);
					}
				}, tuple);
		result.setType(tuple.getType().asTuple().getElementTypes().get(index));
		return result;
	}

	static TupleExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
			Expression tuple, final int index, Expression val) {
		Preconditions.checkArgument(tuple.isTuple());
		Preconditions.checkArgument(0 <= index && index < tuple.asTuple().size());
		Preconditions.checkArgument(val.getType().equals(tuple.asTuple().getType()
				.getElementTypes().get(index)));

		return new TupleExpressionImpl(exprManager, TUPLE_UPDATE,
				new BinaryConstructionStrategy() {

					@Override
					public Expr apply(ExprManager em, Expr tuple, Expr val) {
						Expr indexExpr = em.mkConst(new Rational(index));
						return em.mkExpr(edu.nyu.acsys.CVC4.Kind.TUPLE_UPDATE, tuple,
								indexExpr, val);
					}
				}, tuple, val, tuple.getType());
	}

	private TupleExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
			BinaryConstructionStrategy strategy, Expression left, Expression right,
			Type t) {
		super(exprManager, kind, strategy, left, right);
		setType(TupleTypeImpl.valueOf(exprManager, t));
	}

	private TupleExpressionImpl(ExpressionManagerImpl exprManager, Type type,
			Iterable<? extends Expression> elements) {
		super(exprManager, TUPLE, new NaryConstructionStrategy() {
			@Override
			public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				vectorExpr argsExpr = new vectorExpr();
				for (Expr arg : args)
					argsExpr.add(arg);
				return em.mkExpr(edu.nyu.acsys.CVC4.Kind.TUPLE, argsExpr);
			}
		}, elements);
		setType(type);
	}

	private TupleExpressionImpl(ExpressionImpl tuple) {
		super(tuple);
	}

	private TupleExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
			Expr expr, TupleType type, Iterable<? extends ExpressionImpl> children) {
		super(exprManager, kind, expr, type);
	}

	@Override
	public TupleTypeImpl getType() {
		return (TupleTypeImpl) super.getType();
	}

	@Override
	public Expression index(int i) {
		return mkTupleIndex(getExpressionManager(), this, i);
	}

	@Override
	public int size() {
		return getType().size();
	}

	@Override
	public TupleExpressionImpl update(int index, Expression val) {
		return mkUpdate(getExpressionManager(), this, index, val);
	}
}
