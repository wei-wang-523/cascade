package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public class OrderLinearMemSafetyEncoding extends AbstractMemSafetyEncoding {
	
	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(), 
			SafetyPredicate.Kind.VALID_ACCESS.name(), 
			SafetyPredicate.Kind.STACK_ORDERED.name(), 
			SafetyPredicate.Kind.HEAP_ORDERED.name());
	private final static Collection<String> FUN_ORDER_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.STACK_ORDERED.name(), 
			SafetyPredicate.Kind.HEAP_ORDERED.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());
	
	private final Expression ptrVar, sizeVar;
	
	private OrderLinearMemSafetyEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
		initAssumptions();
	}
	
	public static OrderLinearMemSafetyEncoding create(ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new OrderLinearMemSafetyEncoding(encoding, formatter);
	}
	
	@Override
	public BooleanExpression validMalloc(Expression ptr, Expression size) {
		Expression notOverflow = encoding.notOverflow(ptr, size);
		BooleanExpression notNull = ptr.neq(formatter.getNullAddress());
		return notNull.and(notOverflow);
//			Expression isNull = ptr.eq(formatter.getNullAddress());
//			/* size not overflow, but could be zero -- malloc(0) */
//			return encoding.or(isNull, notOverflow).asBooleanExpression();
  }
	
	@Override
	public BooleanExpression validFree(ArrayExpression markArr, Expression region) {
		Preconditions.checkArgument(markArr.getType().getIndexType().equals(formatter.getAddressType()));
		Preconditions.checkArgument(markArr.getType().getElementType().isBoolean());
		Preconditions.checkArgument(region.getType().equals(formatter.getAddressType()));
		
	  BooleanExpression mark = markArr.index(region).asBooleanExpression();
		BooleanExpression tt = mark.getType().asBooleanType().tt();
	  return mark.eq(tt);
	}

	@Override
  public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
			initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		}
		initSafetyPredicate(Kind.STACK_ORDERED, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.HEAP_ORDERED, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state, ptrVar, sizeVar);
	}
	
	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccess(state, ptrExpr, sizeExpr);
			updateHeapFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateHeapPreDisjoint(state, ptrExpr, sizeExpr);
		updateFunHeapOrdered(state, ptrExpr, sizeExpr);
	}

	@Override
	public void updateStackMemSafetyPredicates(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateStackFunValidAccess(state, ptrExpr, sizeExpr);
			updateStackFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateStackPreDisjoint(state, ptrExpr, sizeExpr);
		updateFunStackOrdred(state, ptrExpr);
	}
	
//	@Override
//	public void refreshDuplicateLabels(SingleLambdaStateExpression state, 
//			final Collection<VariableExpression> labels, 
//			Collection<VariableExpression> substLabels) {
//		
//		{ /* Update the predicate map */
//			Multimap<Expression, Collection<Expression>> predMap = state.getPredicateMap();
//			Collection<Entry<Expression, Collection<Expression>>> entries = Sets.newHashSet(predMap.entries());
//			for(Entry<Expression, Collection<Expression>> entry : entries) {
//					Collection<Expression> args = entry.getValue();
//					if(args == null || args.isEmpty()) continue;
//					
//					List<Expression> argsPrime = Lists.newArrayListWithExpectedSize(args.size());
//					for(Expression arg : args) {
//						Expression argPrime = arg.subst(labels, substLabels);
//						argsPrime.add(argPrime);
//					}
//					
//					Expression func = entry.getKey();
//					predMap.remove(func, args);
//					predMap.put(func, argsPrime);
//			}
//		}
//		
//		replaceLabelsInSafetyPredicate(Kind.VALID_ACCESS, state, labels, substLabels);
//		replaceLabelsInSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, labels, substLabels);
//		replaceLabelsInSafetyPredicate(Kind.PRE_DISJOINT, state, labels, substLabels);
//		replaceLabelsInSafetyPredicate(Kind.STACK_ORDERED, state, labels, substLabels);
//		replaceLabelsInSafetyPredicate(Kind.HEAP_ORDERED, state, labels, substLabels);
//	}

	@Override
	public void propagateSafetyPredicates(SingleLambdaStateExpression fromState,
	    SingleLambdaStateExpression toState) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			propagateSafetyPredicate(Kind.VALID_ACCESS, fromState, toState);
			propagateSafetyPredicate(Kind.VALID_ACCESS_RANGE, fromState, toState);
		}
		propagateSafetyPredicate(Kind.PRE_DISJOINT, fromState, toState);
		propagateSafetyPredicate(Kind.STACK_ORDERED, fromState, toState);
		propagateSafetyPredicate(Kind.HEAP_ORDERED, fromState, toState);
		
		updatePredicateMap(fromState, toState);
	}

	@Override
	public Collection<String> getExprPropNames() {
		return PRED_NAMES;
	}

	@Override
	public Collection<String> getClosurePropNames() {
		return Preferences.isSet(Preferences.OPTION_MEMORY_CHECK) ? FUN_NAMES : FUN_ORDER_NAMES;
	}
	
	@Override
	protected final void propagatePreDisjoint(SingleLambdaStateExpression fromState,
			SingleLambdaStateExpression toState) {
		String stackOrdered = SafetyPredicate.Kind.STACK_ORDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_ORDERED.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		Multimap<Expression, Collection<Expression>> predMap = toState.getPredicateMap();
		PredicateClosure fromStackOrdered = fromState.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure fromHeapOrdered = fromState.getSafetyPredicateClosure(heapOrdered);
		
		List<Expression> candidate = Lists.newArrayList();
		List<Expression> substitute = Lists.newArrayList();
		
		for(Expression func : predMap.keySet()) {
			switch(SafetyPredicate.parse(func)) {
			case HEAP_ORDERED:
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
			case STACK_ORDERED:
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
			default:
				break;
			}
		}
		
		BooleanExpression fromPreDJ = fromState.getSafetyPredicate(preDisjointName);
		BooleanExpression toPreDJ = toState.getSafetyPredicate(preDisjointName);
		BooleanExpression toPreDJPrime = fromPreDJ.and(toPreDJ.subst(candidate, substitute));
		toState.putSafetyPredicate(preDisjointName, toPreDJPrime);
	}

	@Override
	protected final Collection<BooleanExpression> initAssumptions() {
		Collection<BooleanExpression> assumps = Lists.newArrayList();
		
		ExpressionManager exprManager = encoding.getExpressionManager();
		Type addrType = formatter.getAddressType();
		Type sizeType = formatter.getSizeType();
		
		String tpProviderName = encoding.getExpressionManager().getTheoremProver().getProviderName();
		
		{ // STACK_ORDERED
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.STACK_ORDERED.name(), 
							exprManager.functionType(addrType, 
									exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression assump_stack_ordered = encoding.forall(boundVar, 
						func.apply(boundVar).eq(encoding.tt()));
				assumps.add(assump_stack_ordered.asBooleanExpression());
      } else {
      	Expression boundVar = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression lamExpr = exprManager.lambda(boundVar, encoding.tt());
      	assumps.add(lamExpr.eq(func));
      }
		}
		
		{ // HEAP_ORDERED
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.HEAP_ORDERED.name(), 
							exprManager.functionType(addrType, 
									exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression assump_heap_ordered = encoding.forall(boundVar, 
						func.apply(boundVar).eq(encoding.tt()));
				assumps.add(assump_heap_ordered.asBooleanExpression());
      } else {
      	Expression boundVar = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression lamExpr = exprManager.lambda(boundVar, encoding.tt());
      	assumps.add(lamExpr.eq(func));
      }
		}
		
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))  return assumps;
		
		{ // VALID_ACCESS
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.VALID_ACCESS.name(), 
							exprManager.functionType(addrType, 
									exprManager.booleanType()), false);

			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression assump_valid_access = encoding.forall(boundVar, 
						func.apply(boundVar).eq(encoding.ff()));
				assumps.add(assump_valid_access.asBooleanExpression());
      } else {
      	Expression boundVar = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression lamExpr = exprManager.lambda(boundVar, encoding.ff());
      	assumps.add(lamExpr.eq(func));
      }
		}
		
		{ // VALID_ACCESS_RANGE
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.VALID_ACCESS_RANGE.name(), 
							exprManager.functionType(addrType, sizeType,
									exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar0 = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression boundVar1 = exprManager.boundExpression(sizeVarName, 1, sizeType, true);
				Expression assump_valid_access_range = encoding.forall(boundVar0, boundVar1, 
						func.apply(boundVar0, boundVar1).eq(encoding.ff()));
				assumps.add(assump_valid_access_range.asBooleanExpression());
      } else {
      	Expression boundVar0 = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression boundVar1 = exprManager.boundVar(sizeVarName, sizeType, true);
      	Expression lamExpr = exprManager.lambda(Lists.newArrayList(boundVar0, boundVar1), encoding.ff());
      	assumps.add(lamExpr.eq(func));
      }
		}
		
	  return assumps;
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				encoding.within(ptrExpr, sizeExpr, vars[0]), body);
		
		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}
	
	private void updateHeapFunValidAccess(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						sizeExpr.neq(formatter.getSizeZero()),
						encoding.within(ptrExpr, sizeExpr, vars[0])),
						body);
		
		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}
	
	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				encoding.within(ptrExpr, sizeExpr, vars[0], vars[1]), body);
		
		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
	
	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						sizeExpr.neq(formatter.getSizeZero()),
						encoding.within(ptrExpr, sizeExpr, vars[0], vars[1])), body);
		
		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
	
	private void updateFunHeapOrdered(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.HEAP_ORDERED.name();
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = heap_order_closure.getUninterpretedFunc();
		Expression[] vars = heap_order_closure.getVars();
		
		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);
		assert(vars.length == 1);
		
		Expression bodyPrime = encoding.implies(
				ptrExpr.neq(formatter.getNullAddress()),
				encoding.lessThan(ptrBound, vars[0])); // encoding.lessThanOrEqual(ptrBound, vars[0]), size might be zero
		
		PredicateClosure heap_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, heap_order_closure_prime);
	}
	
	private void updateFunStackOrdred(SingleLambdaStateExpression state, Expression ptrExpr) {
		String propName = SafetyPredicate.Kind.STACK_ORDERED.name();
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = stack_order_closure.getUninterpretedFunc();
		Expression[] vars = stack_order_closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.lessThan(vars[0], ptrExpr); // encoding.lessThanOrEqual(vars[0], ptr)); vars[0] != ptr
		
		PredicateClosure stack_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, stack_order_closure_prime);
	}
	
	private void updateHeapPreDisjoint(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		String stackOrdered = SafetyPredicate.Kind.STACK_ORDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_ORDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);
		
		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				encoding.implies(
						ptrExpr.neq(formatter.getNullAddress()),
						encoding.and(					
								encoding.notOverflow(ptrExpr, sizeExpr),
								stack_order_closure.eval(ptrBound),
								heap_order_closure.eval(ptrExpr)))).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);
		
		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptrExpr);
	}
	
	private void updateStackPreDisjoint(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		String stackOrdered = SafetyPredicate.Kind.STACK_ORDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_ORDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);
		
		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				ptrExpr.neq(formatter.getNullAddress()),
				encoding.greaterThan(ptrBound, ptrExpr),
				stack_order_closure.eval(ptrBound),
				heap_order_closure.eval(ptrExpr)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);
		
		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptrExpr);
	}
}
