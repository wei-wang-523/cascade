package edu.nyu.cascade.z3;

import java.util.Arrays;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.BooleanType;

final class BooleanTypeImpl extends TypeImpl implements BooleanType {
	@Override
	public BooleanExpressionImpl importExpression(Expression expression) {
		switch (expression.getKind()) {
		case EQUAL:
			assert (expression.getArity() == 2);
			return BooleanExpressionImpl.mkEq(getExpressionManager(),
					(Expression) expression.getChild(0),
					(Expression) expression.getChild(1));

		default:
			return super.importExpression(expression).asBooleanExpression();
		}
	}

	BooleanTypeImpl(ExpressionManagerImpl expressionManager) {
		super(expressionManager);
		try {
			setZ3Type(
					expressionManager.getTheoremProver().getZ3Context().mkBoolSort());
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.BOOLEAN;
	}

	@Override
	public BooleanVariableImpl variable(String name, boolean fresh) {
		return BooleanVariableImpl.create(getExpressionManager(), name, fresh);
	}

	@Override
	public String getName() {
		return "BOOLEAN";
	}

	@Override
	public BooleanExpressionImpl and(Expression a, Expression b) {
		return BooleanExpressionImpl.mkAnd(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl and(Expression first, Expression... rest) {
		return BooleanExpressionImpl.mkAnd(getExpressionManager(),
				Lists.asList(first, rest));
	}

	@Override
	public BooleanExpressionImpl and(
			Iterable<? extends Expression> subExpressions) {
		// TODO: Check for proper typing
		ImmutableList<? extends Expression> subList = ImmutableList
				.copyOf(subExpressions);
		if (!subList.isEmpty()) {
			// Create the and expression
			return BooleanExpressionImpl.mkAnd(getExpressionManager(), subList);
		}
		return tt();
	}

	@Override
	public BooleanExpressionImpl iff(Expression a, Expression b) {
		// TODO: Check for proper typing
		return BooleanExpressionImpl.mkIff(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl implies(Expression a, Expression b) {
		// Create the and expression
		return BooleanExpressionImpl.mkImplies(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl not(Expression a) {
		return BooleanExpressionImpl.mkNot(getExpressionManager(), a);
	}

	@Override
	public BooleanExpressionImpl or(Expression a, Expression b) {
		return BooleanExpressionImpl.mkOr(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl or(
			Iterable<? extends Expression> subExpressions) {
		if (subExpressions.iterator().hasNext()) {
			return BooleanExpressionImpl.mkOr(getExpressionManager(), subExpressions);
		}
		return ff();
	}

	@Override
	public BooleanExpressionImpl or(Expression... subExpressions) {
		return or(Arrays.asList(subExpressions));
	}

	@Override
	public BooleanExpressionImpl xor(Expression a, Expression b) {
		return BooleanExpressionImpl.mkXor(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl ff() {
		return BooleanExpressionImpl.mkFalse(getExpressionManager());
	}

	@Override
	public BooleanExpressionImpl tt() {
		return BooleanExpressionImpl.mkTrue(getExpressionManager());
	}

	@Override
	public void addTrigger(Expression e, Expression p) {
		BooleanExpressionImpl e2 = BooleanExpressionImpl
				.valueOf(getExpressionManager(), e);
		e2.addTrigger(p);
	}

	@Override
	public void setTriggers(Expression e,
			Iterable<? extends Expression> triggers) {
		BooleanExpressionImpl e2 = BooleanExpressionImpl
				.valueOf(getExpressionManager(), e);
		e2.setTriggers(triggers);
	}

	@Override
	public ImmutableList<ImmutableList<? extends Expression>> getTriggers(
			Expression e) {
		BooleanExpressionImpl e2 = BooleanExpressionImpl
				.valueOf(getExpressionManager(), e);
		return e2.getTriggers();
	}

	@Override
	public Expression ifThenElse(Expression cond, Expression thenPart,
			Expression elsePart) {
		return ExpressionImpl.mkIte(getExpressionManager(), cond, thenPart,
				elsePart);
	}

	@Override
	public BooleanBoundExpressionImpl boundVar(String name, boolean fresh) {
		return BooleanBoundExpressionImpl.create(getExpressionManager(), name,
				fresh);
	}

	@Override
	public BooleanBoundExpressionImpl boundExpression(String name, int index,
			boolean fresh) {
		return BooleanBoundExpressionImpl.create(getExpressionManager(), name,
				index, fresh);
	}

	@Override
	public BooleanExpressionImpl distinct(
			Iterable<? extends Expression> children) {
		Preconditions.checkArgument(Iterables.size(children) > 1);
		return BooleanExpressionImpl.mkDistinct(getExpressionManager(), children);
	}

	@Override
	public BooleanExpressionImpl distinct(Expression first, Expression second,
			Expression... rest) {
		return BooleanExpressionImpl.mkDistinct(getExpressionManager(), first,
				second, rest);
	}

	@Override
	public BooleanExpressionImpl eq(Expression left, Expression right) {
		return BooleanExpressionImpl.mkEq(getExpressionManager(), left, right);
	}

	@Override
	BooleanExpressionImpl createExpression(Expr res, Expression oldExpr,
			Iterable<? extends ExpressionImpl> children) {
		return BooleanExpressionImpl.create(getExpressionManager(),
				oldExpr.getKind(), res, oldExpr.getType(), children);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
			Expression body) {
		return exists(vars, body, null);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
			Expression body, Iterable<? extends Expression> triggers) {
		return exists(vars, body, triggers, null);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
			Expression body, Iterable<? extends Expression> triggers,
			Iterable<? extends Expression> noTriggers) {
		final ExpressionManagerImpl em = getExpressionManager();

		boolean isVar = Iterables.all(vars, new Predicate<Expression>() {
			@Override
			public boolean apply(Expression var) {
				try {
					return em.toZ3Expr(var).isVar();
				} catch (Z3Exception e) {
					throw new TheoremProverException(e);
				}
			}
		});

		if (isVar)
			return BooleanExpressionImpl.mkExists(em, vars, body, triggers,
					noTriggers);
		else
			return BooleanExpressionImpl.mkExistsConst(em, vars, body, triggers,
					noTriggers);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
			Expression body) {
		return forall(vars, body, null);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
			Expression body, Iterable<? extends Expression> triggers) {
		return forall(vars, body, triggers, null);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
			Expression body, Iterable<? extends Expression> triggers,
			Iterable<? extends Expression> noTriggers) {
		final ExpressionManagerImpl em = getExpressionManager();

		boolean isVar = Iterables.all(vars, new Predicate<Expression>() {
			@Override
			public boolean apply(Expression var) {
				try {
					return em.toZ3Expr(var).isVar();
				} catch (Z3Exception e) {
					throw new TheoremProverException(e);
				}
			}
		});

		if (isVar)
			return BooleanExpressionImpl.mkForall(em, vars, body, triggers,
					noTriggers);
		else
			return BooleanExpressionImpl.mkForallConst(em, vars, body, triggers,
					noTriggers);
	}

	@Override
	public BooleanExpression rewriteRule(Iterable<? extends Expression> vars,
			Expression guard, Expression body) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrRewrite(Expression head, Expression body,
			Iterable<? extends Expression> triggers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrRewrite(Expression head, Expression body) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrReduction(Expression head, Expression body,
			Iterable<? extends Expression> triggers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrReduction(Expression head, Expression body) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrDeduction(Expression head, Expression body,
			Iterable<? extends Expression> triggers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression rrDeduction(Expression head, Expression body) {
		// TODO Auto-generated method stub
		return null;
	}
}
