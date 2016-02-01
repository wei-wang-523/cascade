package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;

public class SoundLinearMemSafetyEncoding extends AbstractMemSafetyEncoding {
	
	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
			SafetyPredicate.Kind.VALID_ACCESS.name(),
			SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());
	
	private final Expression ptrVar, sizeVar;
	
	private SoundLinearMemSafetyEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
	}
	
	public static SoundLinearMemSafetyEncoding create(ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new SoundLinearMemSafetyEncoding(encoding, formatter);
	}
	
	@Override
  public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.DISJOINT, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state, ptrVar, sizeVar);
	}
	
	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state, VariableExpression ptrExpr, VariableExpression sizeExpr) {
		updateHeapFunValidAccess(state, ptrExpr, sizeExpr);
		updateHeapFunValidAccessRange(state, ptrExpr, sizeExpr);
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateHeapPreDisjoint(state, ptrExpr, sizeExpr);
		updateHeapFunDisjoint(state, ptrExpr, sizeExpr);
	}

	@Override
	public void updateStackMemSafetyPredicates(SingleLambdaStateExpression state, VariableExpression ptrExpr, VariableExpression sizeExpr) {
		updateStackFunValidAccess(state, ptrExpr, sizeExpr);
		updateStackFunValidAccessRange(state, ptrExpr, sizeExpr);
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateStackPreDisjoint(state, ptrExpr, sizeExpr);
		updateStackFunDisjoint(state, ptrExpr, sizeExpr);
	}
	
	@Override
  public Expression validMalloc(Expression ptr, Expression size) {
    Expression assump = encoding.eq(ptr, formatter.getNullAddress());
    
    /* size not overflow, but could be zero -- malloc(0) */
	  return encoding.or(assump, encoding.notOverflow(ptr, size));
  }
	
	@Override
	public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(formatter.getAddressType()));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(formatter.getSizeType()));
		Preconditions.checkArgument(ptr.getType().equals(formatter.getAddressType()));
		
	  Expression size = sizeArr.index(ptr);
		Expression nullPtr = formatter.getNullAddress();
		Expression sizeZro = formatter.getSizeZero();
	  return encoding.or(
	  		ptr.eq(nullPtr), 
	  		encoding.greaterThan(size, sizeZro)).asBooleanExpression();
	}
	
	@Override
	public void refreshDuplicateLabels(SingleLambdaStateExpression state, 
			final Collection<VariableExpression> labels, 
			Collection<VariableExpression> substLabels) {
		
		{ /* Update the predicate map */
			Multimap<Expression, Collection<Expression>> predMap = state.getPredicateMap();
			Collection<Entry<Expression, Collection<Expression>>> entries = Sets.newHashSet(predMap.entries());
			for(Entry<Expression, Collection<Expression>> entry : entries) {
					Collection<Expression> args = entry.getValue();
					if(args == null || args.isEmpty()) continue;
					
					if(Iterables.all(args, new Predicate<Expression>(){
						@Override
            public boolean apply(Expression arg) {
							return !labels.contains(arg);
            }
					})) continue;
					
					List<Expression> argsPrime = Lists.newArrayListWithExpectedSize(args.size());
					for(Expression arg : args) {
						Expression argPrime = arg.subst(labels, substLabels);
						argsPrime.add(argPrime);
					}
					
					Expression func = entry.getKey();
					predMap.remove(func, args);
					predMap.put(func, argsPrime);
			}
		}
		
		replaceLabelsInSafetyPredicate(Kind.VALID_ACCESS, state, labels, substLabels);
		replaceLabelsInSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, labels, substLabels);
		replaceLabelsInSafetyPredicate(Kind.PRE_DISJOINT, state, labels, substLabels);
		replaceLabelsInSafetyPredicate(Kind.DISJOINT, state, labels, substLabels);
	}
	
	@Override
  public void propagateSafetyPredicates(SingleLambdaStateExpression fromState, SingleLambdaStateExpression toState) {		
		propagateSafetyPredicate(Kind.VALID_ACCESS, fromState, toState);
		propagateSafetyPredicate(Kind.VALID_ACCESS_RANGE, fromState, toState);
		propagateSafetyPredicate(Kind.PRE_DISJOINT, fromState, toState);
		propagateSafetyPredicate(Kind.DISJOINT, fromState, toState);
		
		updatePredicateMap(fromState, toState);
  }
	
	@Override
	public Collection<String> getExprPropNames() {
		return PRED_NAMES;
	}

	@Override
	public Collection<String> getClosurePropNames() {
		return FUN_NAMES;
	}
	
	@Override
	protected final void propagatePreDisjoint(SingleLambdaStateExpression fromState, 
			SingleLambdaStateExpression toState) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		Multimap<Expression, Collection<Expression>> predMap = toState.getPredicateMap();
		PredicateClosure fromDJ = fromState.getSafetyPredicateClosure(disjointName);
		BooleanExpression fromPreDJ = fromState.getSafetyPredicate(preDisjointName);
		
		List<Expression> candidate = Lists.newArrayList();
		List<Expression> substitute = Lists.newArrayList();
		
		Expression toPreDJVar = null;
		for(Expression func : predMap.keySet()) {
			switch(SafetyPredicate.parse(func)) {
			case DISJOINT:
				for(Collection<Expression> args : predMap.get(func)) {
					assert(args.size() == 2);
					Expression cand = func.asFunctionExpression().apply(args);
					candidate.add(cand);
					
					Iterator<Expression> argItr = args.iterator();
					Expression arg1 = argItr.next();
					Expression arg2 = argItr.next();
					Expression subst = fromDJ.eval(arg1, arg2);
					substitute.add(subst);
				}
				break;
			case PRE_DISJOINT:
				toPreDJVar = func;
				break;
			default:
				break;
			}
		}
		
		candidate.add(toPreDJVar); 
		substitute.add(fromPreDJ);
		
		BooleanExpression toPreDJ = toState.getSafetyPredicate(preDisjointName);
		BooleanExpression toPreDJPrime = toPreDJ.subst(candidate, substitute).asBooleanExpression();
		toState.putSafetyPredicate(preDisjointName, toPreDJPrime);
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state, VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				body,
				encoding.within(ptr, size, vars[0]));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccess(SingleLambdaStateExpression state, VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptr.neq(formatter.getNullAddress()),
						size.neq(formatter.getSizeZero()),
						encoding.within(ptr, size, vars[0])));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				body,
				encoding.within(ptr, size, vars[0], vars[1]));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptr.neq(formatter.getNullAddress()),
						size.neq(formatter.getSizeZero()),
						encoding.within(ptr, size, vars[0], vars[1])));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		
		Expression bodyPrime = encoding.and(
				body,
				encoding.implies(
						ptr.neq(formatter.getNullAddress()),
						encoding.ifThenElse(size.neq(formatter.getSizeZero()), 
								encoding.disjoint(vars[0], vars[1], ptr, size),
								encoding.disjoint(vars[0], vars[1], ptr))));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateStackFunDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.and(
				body,
				encoding.disjoint(ptr, size, vars[0], vars[1]));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateStackPreDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				disjoint_closure.eval(ptr, size),
				encoding.notOverflow(ptr, size),
				ptr.neq(formatter.getNullAddress())).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptr, size);
	}
	
	private void updateHeapPreDisjoint(SingleLambdaStateExpression state, VariableExpression ptr, VariableExpression size) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);
		
		/* Here, we miss the clause like: 
		 *     implies(ptr.neq(formatter.getNullAddress()),
		 *     					encoding.lessThanOrEqual(ptr, encoding.plus(ptr, size)))
		 * Because the valid_malloc(ptr, size) has already specify it as assumption
		 */
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				disjoint_closure.eval(ptr, size)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptr, size);
	}
}
