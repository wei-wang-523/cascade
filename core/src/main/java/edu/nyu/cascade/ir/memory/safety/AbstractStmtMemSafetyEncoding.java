package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.AbstractStmtMemSafetyEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;

public abstract class AbstractStmtMemSafetyEncoding implements
    IRMemSafetyEncoding {

	protected final static String ptrVarName = "ptrVar";
	protected final static String sizeVarName = "sizeVar";

	final static class SafetyPredicate {
		enum Kind {
			VALID_ACCESS, VALID_ACCESS_RANGE, STACK_ORDERED, HEAP_ORDERED, DISJOINT, PRE_DISJOINT
		}

		static Kind parse(Expression key) {
			Preconditions.checkArgument(key.isFunction() || key.isBoolean());
			String name = key.isFunction() ? key.asFunctionExpression().getName()
			    : key.asVariable().getName();

			if (name.equals(Kind.VALID_ACCESS_RANGE.name()))
				return Kind.VALID_ACCESS_RANGE;

			if (name.equals(Kind.VALID_ACCESS.name()))
				return Kind.VALID_ACCESS;

			if (name.equals(Kind.DISJOINT.name()))
				return Kind.DISJOINT;

			if (name.equals(Kind.STACK_ORDERED.name()))
				return Kind.STACK_ORDERED;

			if (name.equals(Kind.HEAP_ORDERED.name()))
				return Kind.HEAP_ORDERED;

			if (name.equals(Kind.PRE_DISJOINT.name()))
				return Kind.PRE_DISJOINT;

			throw new IllegalArgumentException("Invalid predicate " + name);
		}
	}

	protected final IRDataFormatter formatter;
	protected final ExpressionEncoding encoding;

	protected AbstractStmtMemSafetyEncoding(ExpressionEncoding encoding,
	    IRDataFormatter formatter) {
		this.formatter = formatter;
		this.encoding = encoding;
	}

	public static IRMemSafetyEncoding getInstance(ExpressionEncoding encoding,
	    IRDataFormatter formatter, Strategy strategy) {
		switch (strategy) {
		case ORDER:
			return OrderStmtLinearMemSafetyEncoding.create(encoding, formatter);
		default:
			return SoundStmtLinearMemSafetyEncoding.create(encoding, formatter);
		}
	}

	@Override
	public PredicateClosure suspend(final Expression func, final Expression expr,
	    final Expression... vars) {
		return new PredicateClosure() {

			@Override
			public String toString() {
				return new StringBuilder().append("\n\tfunc: ").append(func).append(
		        "\n\texpr: ").append(expr).toString();
			}

			@Override
			public Expression getUninterpretedFunc() {
				return func;
			}

			@Override
			public Expression eval(Expression... args) {
				return expr.subst(Lists.newArrayList(vars), Lists.newArrayList(args));
			}

			@Override
			public Expression getBodyExpr() {
				return expr;
			}

			@Override
			public Expression[] getVars() {
				return vars;
			}
		};
	}

	@Override
	public Expression applyUpdatedPredicate(SingleLambdaStateExpression state,
	    FunctionExpression func, Collection<Expression> args) {
		String funcName = func.getName();
		PredicateClosure predicateClosure = state.getSafetyPredicateClosure(
		    funcName);
		Expression[] argsArray = new Expression[args.size()];
		argsArray = args.toArray(argsArray);
		state.registerPredicate(predicateClosure.getUninterpretedFunc(), argsArray);
		return predicateClosure.eval(argsArray);
	}

	@Override
	public PredicateClosure getValidAccess(SingleLambdaStateExpression state) {
		return state.getSafetyPredicateClosure(Kind.VALID_ACCESS.name());
	}

	@Override
	public PredicateClosure getValidAccessRange(
	    SingleLambdaStateExpression state) {
		return state.getSafetyPredicateClosure(Kind.VALID_ACCESS_RANGE.name());
	}

	@Override
	public BooleanExpression getPreDisjoint(SingleLambdaStateExpression state) {
		return state.getSafetyPredicate(Kind.PRE_DISJOINT.name());
	}

	@Override
	public void propagateSafetyPredicates(SingleLambdaStateExpression fromState,
	    SingleLambdaStateExpression toState) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<BooleanExpression> getAssumptions() {
		return Collections.emptyList();
	}

	final void initSafetyPredicate(Kind kind, SingleLambdaStateExpression state,
	    Expression ptrVar, Expression sizeVar) {
		ExpressionManager exprManager = encoding.getExpressionManager();
		String fname = kind.name();

		switch (kind) {
		case DISJOINT: {
			PredicateClosure closure = suspend(null, encoding.tt(), ptrVar, sizeVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case HEAP_ORDERED: {
			PredicateClosure closure = suspend(null, encoding.tt(), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case PRE_DISJOINT: {
			BooleanExpression predicate = exprManager.booleanType().tt();
			state.putSafetyPredicate(fname, predicate);
			break;
		}
		case STACK_ORDERED: {
			PredicateClosure closure = suspend(null, encoding.tt(), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case VALID_ACCESS: {
			PredicateClosure closure = suspend(null, encoding.ff(), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case VALID_ACCESS_RANGE: {
			PredicateClosure closure = suspend(null, encoding.ff(), ptrVar, sizeVar);

			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		default:
			break;
		}
	}
}
