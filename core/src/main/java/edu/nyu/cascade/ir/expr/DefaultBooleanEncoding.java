package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.ExpressionManager;

public class DefaultBooleanEncoding extends
		AbstractTypeEncoding<BooleanExpression> implements
		BooleanEncoding<BooleanExpression> {
	private static final String UNKNOWN_VARIABLE_NAME = "bool_encoding_unknown";

	public DefaultBooleanEncoding(ExpressionManager exprManager) {
		super(exprManager, exprManager.booleanType());
	}

	@Override
	public BooleanExpression and(BooleanExpression lhs, BooleanExpression rhs) {
		return lhs.and(rhs);
	}

	@Override
	public BooleanExpression and(
			Iterable<? extends BooleanExpression> conjuncts) {
		return getExpressionManager().and(conjuncts);
	}

	@Override
	public BooleanExpression ff() {
		return getExpressionManager().ff();
	}

	@Override
	public BooleanExpression forall(Iterable<? extends BoundExpression> ids,
			BooleanExpression expr) {
		return expr.forall(ids);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends BoundExpression> ids,
			BooleanExpression expr) {
		return expr.exists(ids);
	}

	@Override
	public BooleanExpression iff(BooleanExpression lhs, BooleanExpression rhs) {
		return lhs.iff(rhs);
	}

	@Override
	public BooleanExpression implies(BooleanExpression lhs,
			BooleanExpression rhs) {
		return lhs.implies(rhs);
	}

	@Override
	public BooleanExpression not(BooleanExpression arg) {
		return arg.not();
	}

	@Override
	public BooleanExpression ofBooleanExpression(BooleanExpression b) {
		return b;
	}

	@Override
	public BooleanExpression or(BooleanExpression lhs, BooleanExpression rhs) {
		return lhs.or(rhs);
	}

	@Override
	public BooleanExpression or(Iterable<? extends BooleanExpression> disjuncts) {
		return getExpressionManager().or(disjuncts);
	}

	@Override
	public BooleanExpression toBoolean(BooleanExpression b) {
		return b;
	}

	@Override
	public BooleanExpression tt() {
		return getExpressionManager().tt();
	}

	@Override
	public BooleanExpression xor(BooleanExpression lhs, BooleanExpression rhs) {
		return lhs.xor(rhs);
	}

	@Override
	public BooleanExpression ofExpression(Expression x) {
		Preconditions.checkArgument(x.isBoolean());
		return x.asBooleanExpression();
	}

	@Override
	public boolean isEncodingFor(Expression x) {
		return x.isBoolean();
	}

	@Override
	public BooleanExpression unknown() {
		return getType().asBooleanType().variable(UNKNOWN_VARIABLE_NAME, true);
	}

	@Override
	public BooleanExpression ifThenElse(BooleanExpression b,
			BooleanExpression thenExpr, BooleanExpression elseExpr) {
		return getExpressionManager().ifThenElse(b, thenExpr, elseExpr)
				.asBooleanExpression();
	}
}
