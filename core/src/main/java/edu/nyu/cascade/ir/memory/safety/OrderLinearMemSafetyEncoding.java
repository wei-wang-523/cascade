package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
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

public class OrderLinearMemSafetyEncoding extends AbstractMemSafetyEncoding {
	
	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(), 
			SafetyPredicate.Kind.VALID_ACCESS.name(), 
			SafetyPredicate.Kind.STACK_OREDERED.name(), 
			SafetyPredicate.Kind.HEAP_OREDERED.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());
	
	Expression ptrVar, sizeVar;
	
	private OrderLinearMemSafetyEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
	}
	
	public static OrderLinearMemSafetyEncoding create(ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new OrderLinearMemSafetyEncoding(encoding, formatter);
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
  public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.STACK_OREDERED, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.HEAP_OREDERED, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state, ptrVar, sizeVar);
	}
	
	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state, VariableExpression ptrExpr, VariableExpression sizeExpr) {
		updateHeapFunValidAccess(state, ptrExpr, sizeExpr);
		updateHeapFunValidAccessRange(state, ptrExpr, sizeExpr);
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateHeapPreDisjoint(state, ptrExpr, sizeExpr);
		updateFunHeapOrdered(state, ptrExpr, sizeExpr);
	}

	@Override
	public void updateStackMemSafetyPredicates(SingleLambdaStateExpression state, VariableExpression ptrExpr, VariableExpression sizeExpr) {
		updateStackFunValidAccess(state, ptrExpr, sizeExpr);
		updateStackFunValidAccessRange(state, ptrExpr, sizeExpr);
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateStackPreDisjoint(state, ptrExpr, sizeExpr);
		updateFunStackOrdred(state, ptrExpr);
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
		replaceLabelsInSafetyPredicate(Kind.STACK_OREDERED, state, labels, substLabels);
		replaceLabelsInSafetyPredicate(Kind.HEAP_OREDERED, state, labels, substLabels);
	}

	@Override
	public void propagateSafetyPredicates(SingleLambdaStateExpression fromState,
	    SingleLambdaStateExpression toState) {		
		propagateSafetyPredicate(Kind.VALID_ACCESS, fromState, toState);
		propagateSafetyPredicate(Kind.VALID_ACCESS_RANGE, fromState, toState);
		propagateSafetyPredicate(Kind.PRE_DISJOINT, fromState, toState);
		propagateSafetyPredicate(Kind.STACK_OREDERED, fromState, toState);
		propagateSafetyPredicate(Kind.HEAP_OREDERED, fromState, toState);
		
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
		String stackOrdered = SafetyPredicate.Kind.STACK_OREDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_OREDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		Multimap<Expression, Collection<Expression>> predMap = toState.getPredicateMap();
		PredicateClosure fromStackOrdered = fromState.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure fromHeapOrdered = fromState.getSafetyPredicateClosure(heapOrdered);
		BooleanExpression fromPreDJ = fromState.getSafetyPredicate(preDisjoint);
		
		List<Expression> candidate = Lists.newArrayList();
		List<Expression> substitute = Lists.newArrayList();
		
		Expression toPreDJVar = null;
		for(Expression func : predMap.keySet()) {
			switch(SafetyPredicate.parse(func)) {
			case HEAP_OREDERED:
				for(Collection<Expression> args : predMap.get(func)) {
					assert(args.size() == 1);
					Expression cand = func.asFunctionExpression().apply(args);
					candidate.add(cand);
					
					Iterator<Expression> argItr = args.iterator();
					Expression arg1 = argItr.next();
					Expression subst = fromHeapOrdered.eval(arg1);
					substitute.add(subst);
				}
				break;
			case STACK_OREDERED:
				for(Collection<Expression> args : predMap.get(func)) {
					assert(args.size() == 1);
					Expression cand = func.asFunctionExpression().apply(args);
					candidate.add(cand);
					
					Iterator<Expression> argItr = args.iterator();
					Expression arg1 = argItr.next();
					Expression subst = fromStackOrdered.eval(arg1);
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
		
		BooleanExpression toPreDJ = toState.getSafetyPredicate(preDisjoint);
		BooleanExpression toPreDJPrime = toPreDJ.subst(candidate, substitute).asBooleanExpression();
		toState.putSafetyPredicate(preDisjoint, toPreDJPrime);
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				body,
				encoding.within(ptr, size, vars[0]));
		
		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}
	
	private void updateHeapFunValidAccess(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptr.neq(formatter.getNullAddress()),
						size.neq(formatter.getSizeZero()),
						encoding.within(ptr, size, vars[0])));
		
		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}
	
	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				body,
				encoding.within(ptr, size, vars[0], vars[1]));
		
		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
	
	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptr.neq(formatter.getNullAddress()),
						size.neq(formatter.getSizeZero()),
						encoding.within(ptr, size, vars[0], vars[1])));
		
		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
	
	private void updateFunHeapOrdered(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.HEAP_OREDERED.name();
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = heap_order_closure.getUninterpretedFunc();
		Expression[] vars = heap_order_closure.getVars();
		
		Expression ptrBound = encoding.plus(ptr, size);
		assert(vars.length == 1);
		
		Expression bodyPrime = encoding.implies(
				ptr.neq(formatter.getNullAddress()),
				encoding.lessThan(ptrBound, vars[0])); // encoding.lessThanOrEqual(ptrBound, vars[0]), size might be zero
		
		PredicateClosure heap_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, heap_order_closure_prime);
	}
	
	private void updateFunStackOrdred(SingleLambdaStateExpression state, VariableExpression ptr) {
		String propName = SafetyPredicate.Kind.STACK_OREDERED.name();
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = stack_order_closure.getUninterpretedFunc();
		Expression[] vars = stack_order_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.lessThan(vars[0], ptr); // encoding.lessThanOrEqual(vars[0], ptr)); vars[0] != ptr
		
		PredicateClosure stack_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, stack_order_closure_prime);
	}
	
	private void updateHeapPreDisjoint(SingleLambdaStateExpression state, VariableExpression ptr, VariableExpression size) {
		String stackOrdered = SafetyPredicate.Kind.STACK_OREDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_OREDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);
		
		Expression ptrBound = encoding.plus(ptr, size);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				encoding.implies(
						ptr.neq(formatter.getNullAddress()),
						encoding.and(					
								encoding.notOverflow(ptr, size),
								stack_order_closure.eval(ptrBound),
								heap_order_closure.eval(ptr)))).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);
		
		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptr);
	}
	
	private void updateStackPreDisjoint(SingleLambdaStateExpression state, VariableExpression ptr, VariableExpression size) {
		String stackOrdered = SafetyPredicate.Kind.STACK_OREDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_OREDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);
		
		Expression ptrBound = encoding.plus(ptr, size);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				ptr.neq(formatter.getNullAddress()),
				encoding.greaterThan(ptrBound, ptr),
				stack_order_closure.eval(ptrBound),
				heap_order_closure.eval(ptr)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);
		
		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptr);
	}
}
