package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.UninterpretedExpression;

public class DefaultUninterpretedEncoding extends
    AbstractTypeEncoding<UninterpretedExpression> implements
    UninterpretedEncoding<UninterpretedExpression> {
	private static final String UNKNOWN_VARIABLE_NAME = "uninterpreted_encoding_unknown";

	public DefaultUninterpretedEncoding(ExpressionManager exprManager,
	    String typeName) {
		super(exprManager, exprManager.uninterpretedType(typeName));
	}

	@Override
	public UninterpretedExpression ofExpression(Expression x) {
		Preconditions.checkArgument(x.isUninterpreted());
		return x.asUninterpreted();
	}

	@Override
	public BooleanExpression distinct(
	    Iterable<? extends UninterpretedExpression> exprs) {
		return getExpressionManager().distinct(exprs);
	}

	@Override
	public BooleanExpression eq(UninterpretedExpression lhs,
	    UninterpretedExpression rhs) {
		return lhs.eq(rhs);
	}

	@Override
	public BooleanExpression neq(UninterpretedExpression lhs,
	    UninterpretedExpression rhs) {
		return lhs.neq(rhs);
	}

	@Override
	public UninterpretedExpression ifThenElse(BooleanExpression b,
	    UninterpretedExpression thenExpr, UninterpretedExpression elseExpr) {
		return b.ifThenElse(thenExpr, elseExpr).asUninterpreted();
	}

	@Override
	public UninterpretedExpression unknown() {
		return getExpressionManager().variable(UNKNOWN_VARIABLE_NAME, getType(),
		    true).asUninterpreted();
	}
}
