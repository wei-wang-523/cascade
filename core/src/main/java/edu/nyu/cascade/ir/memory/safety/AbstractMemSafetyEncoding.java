package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractMemSafetyEncoding implements IRMemSafetyEncoding {

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
	private final Collection<BooleanExpression> assumptions;

	protected AbstractMemSafetyEncoding(ExpressionEncoding encoding,
			IRDataFormatter formatter) {
		this.formatter = formatter;
		this.encoding = encoding;
		this.assumptions = initAssumptions();
	}

	public static IRMemSafetyEncoding getInstance(ExpressionEncoding encoding,
			IRDataFormatter formatter, Strategy strategy) {
		switch (strategy) {
		case ORDER:
			return OrderLinearMemSafetyEncoding.create(encoding, formatter);
		default:
			return SoundLinearMemSafetyEncoding.create(encoding, formatter);
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
	public Collection<BooleanExpression> getAssumptions() {
		return assumptions;
	}

	protected abstract void propagatePreDisjoint(
			SingleLambdaStateExpression fromState,
			SingleLambdaStateExpression toState);

	protected abstract Collection<BooleanExpression> initAssumptions();

	final void updatePredicateMap(SingleLambdaStateExpression fromState,
			SingleLambdaStateExpression toState) {
		Multimap<Expression, Collection<Expression>> toPredMapPrime = HashMultimap
				.create(fromState.getPredicateMap());

		Multimap<Expression, Collection<Expression>> toPredMap = toState
				.getPredicateMap();
		for (Expression toFunc : toPredMap.keySet()) {
			Kind kind = SafetyPredicate.parse(toFunc);
			updatePredicateMapWithSafetyPredicate(kind, toState, toFunc,
					toPredMapPrime);
		}

		toState.setPredicateMap(toPredMapPrime);
	}

	final void initSafetyPredicate(Kind kind, SingleLambdaStateExpression state,
			Expression ptrVar, Expression sizeVar) {
		ExpressionManager exprManager = encoding.getExpressionManager();
		String fname = kind.name();

		Type addrType = formatter.getAddressType();
		Type sizeType = formatter.getSizeType();

		switch (kind) {
		case DISJOINT: {
			List<Type> argTypes = Lists.newArrayList(addrType, sizeType);

			FunctionExpression func = exprManager.functionDeclarator(fname,
					exprManager.functionType(argTypes, exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, func.apply(ptrVar, sizeVar),
					ptrVar, sizeVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case HEAP_ORDERED: {
			FunctionExpression func = exprManager.functionDeclarator(fname,
					exprManager.functionType(addrType, exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, func.apply(ptrVar), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case PRE_DISJOINT: {
			BooleanExpression predicate = exprManager.booleanType().tt();
			state.putSafetyPredicate(fname, predicate);
			break;
		}
		case STACK_ORDERED: {
			FunctionExpression func = exprManager.functionDeclarator(fname,
					exprManager.functionType(addrType, exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, func.apply(ptrVar), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case VALID_ACCESS: {
			FunctionExpression func = exprManager.functionDeclarator(fname,
					exprManager.functionType(addrType, exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, func.apply(ptrVar), ptrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case VALID_ACCESS_RANGE: {
			List<Type> argTypes = Lists.newArrayList(addrType, sizeType);

			FunctionExpression func = exprManager.functionDeclarator(fname,
					exprManager.functionType(argTypes, exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, func.apply(ptrVar, sizeVar),
					ptrVar, sizeVar);

			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		default:
			break;
		}
	}

	// final void replaceLabelsInSafetyPredicate(Kind kind,
	// SingleLambdaStateExpression state,
	// Collection<VariableExpression> oldLabels,
	// Collection<VariableExpression> freshLabels) {
	// String propName = kind.name();
	// switch(kind) {
	// case PRE_DISJOINT: {
	// BooleanExpression to = state.getSafetyPredicate(propName);
	// BooleanExpression toPrime = to.subst(oldLabels, freshLabels)
	// .asBooleanExpression();
	// state.putSafetyPredicate(propName, toPrime);
	// break;
	// }
	// default: {
	// PredicateClosure to = state.getSafetyPredicateClosure(propName);
	// PredicateClosure toPrime = replaceLabels(to, oldLabels, freshLabels);
	// state.putSafetyPredicateClosure(propName, toPrime);
	// break;
	// }
	// }
	// }

	final void propagateSafetyPredicate(Kind kind,
			SingleLambdaStateExpression fromState,
			SingleLambdaStateExpression toState) {

		switch (kind) {
		case PRE_DISJOINT: {
			propagatePreDisjoint(fromState, toState);
			break;
		}
		default: {
			String propName = kind.name();
			PredicateClosure from = fromState.getSafetyPredicateClosure(propName);
			PredicateClosure to = toState.getSafetyPredicateClosure(propName);
			PredicateClosure toPrime = updatePredicateClosure(from, to);
			toState.putSafetyPredicateClosure(propName, toPrime);
			break;
		}
		}
	}

	final void updatePredicateMapWithSafetyPredicate(Kind kind,
			SingleLambdaStateExpression state, Expression func,
			Multimap<Expression, Collection<Expression>> predMap) {

		switch (kind) {
		case PRE_DISJOINT: {
			break;
		}
		default: {
			String propName = kind.name();
			PredicateClosure from = state.getSafetyPredicateClosure(propName);
			Expression fromFunc = from.getUninterpretedFunc();
			predMap.putAll(fromFunc, state.getPredicateMap().get(func));
			break;
		}
		}
	}

	private PredicateClosure updatePredicateClosure(PredicateClosure from,
			PredicateClosure to) {
		Expression[] toVars = to.getVars();
		BooleanExpression fromEvalBody = from.eval(toVars).asBooleanExpression();
		BooleanExpression toBody = to.getBodyExpr().asBooleanExpression();
		Expression toFunApp = to.getUninterpretedFunc().asFunctionExpression()
				.apply(Lists.newArrayList(toVars));
		BooleanExpression toBodyPrime = toBody.subst(toFunApp, fromEvalBody)
				.asBooleanExpression();
		Expression toFunPrime = from.getUninterpretedFunc();
		return suspend(toFunPrime, toBodyPrime, toVars);
	}

	// /**
	// * Replace the <code>closure</code> from <code>oldLabels</code> to
	// * <code>freshLabels</code>
	// * @param closure
	// * @param oldLabels
	// * @param freshLabels
	// * @return
	// */
	// private PredicateClosure replaceLabels(PredicateClosure closure,
	// Collection<VariableExpression> oldLabels,
	// Collection<VariableExpression> freshLabels) {
	// Expression[] vars = closure.getVars();
	// BooleanExpression body = closure.getBodyExpr().asBooleanExpression();
	// BooleanExpression bodyPrime = body.subst(oldLabels,
	// freshLabels).asBooleanExpression();
	//
	// Expression funApp = closure.getUninterpretedFunc();
	// return suspend(funApp, bodyPrime, vars);
	// }
}
