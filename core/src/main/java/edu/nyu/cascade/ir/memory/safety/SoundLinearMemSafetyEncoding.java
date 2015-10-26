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

public class SoundLinearMemSafetyEncoding extends AbstractMemSafetyEncoding {
	
	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
			SafetyPredicate.Kind.VALID_ACCESS.name(),
			SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> FUN_DISJOINT_NAMES = Lists.newArrayList(
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
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
			initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		}
		initSafetyPredicate(Kind.DISJOINT, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state, ptrVar, sizeVar);
	}
	
	@Override
	public void freeUpdateHeapMemSafetyPredicates(
			SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccessFree(state, ptrExpr, sizeExpr);
			updateHeapFunValidAccessRangeFree(state, ptrExpr, sizeExpr);
		}	
	}
	
	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccess(state, ptrExpr, sizeExpr);
			updateHeapFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateHeapPreDisjoint(state, ptrExpr, sizeExpr);
		updateHeapFunDisjoint(state, ptrExpr, sizeExpr);
	}

	@Override
	public void updateStackMemSafetyPredicates(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateStackFunValidAccess(state, ptrExpr, sizeExpr);
			updateStackFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateStackPreDisjoint(state, ptrExpr, sizeExpr);
		updateStackFunDisjoint(state, ptrExpr, sizeExpr);
	}
	
	@Override
  public BooleanExpression validMalloc(Expression region, Expression size) {
		Expression notOverflow = encoding.notOverflow(region, size);
		BooleanExpression notNull = region.neq(formatter.getNullAddress());
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
//					if(Iterables.all(args, new Predicate<Expression>(){
//						@Override
//            public boolean apply(Expression arg) {
//							return !labels.contains(arg);
//            }
//					})) continue;
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
//		replaceLabelsInSafetyPredicate(Kind.DISJOINT, state, labels, substLabels);
//	}
	
	@Override
  public void propagateSafetyPredicates(SingleLambdaStateExpression fromState, SingleLambdaStateExpression toState) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			propagateSafetyPredicate(Kind.VALID_ACCESS, fromState, toState);
			propagateSafetyPredicate(Kind.VALID_ACCESS_RANGE, fromState, toState);
		}
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
		return Preferences.isSet(Preferences.OPTION_MEMORY_CHECK) ? FUN_NAMES : FUN_DISJOINT_NAMES;
	}
	
	@Override
	protected final void propagatePreDisjoint(SingleLambdaStateExpression fromState, 
			SingleLambdaStateExpression toState) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		Multimap<Expression, Collection<Expression>> predMap = toState.getPredicateMap();
		PredicateClosure fromDJ = fromState.getSafetyPredicateClosure(disjointName);
		
		List<Expression> candidate = Lists.newArrayList();
		List<Expression> substitute = Lists.newArrayList();
		
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
		
		{ // DISJOINT
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.DISJOINT.name(), 
							exprManager.functionType(addrType, sizeType, exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar0 = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression boundVar1 = exprManager.boundExpression(sizeVarName, 1, sizeType, true);
  			Expression assump_disjoint = encoding.forall(boundVar0, boundVar1,
  					func.apply(boundVar0, boundVar1).eq(encoding.tt()));
  			assumps.add(assump_disjoint.asBooleanExpression());
      } else {
      	Expression boundVar0 = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression boundVar1 = exprManager.boundVar(sizeVarName, sizeType, true);
      	Expression lamExpr = exprManager.lambda(Lists.newArrayList(boundVar0, boundVar1),
      			encoding.tt());
      	assumps.add(func.eq(lamExpr));
      }
		}
		
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))	return assumps;
		
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
      	Expression lamExpr = exprManager.lambda(boundVar,
      			encoding.ff());
      	assumps.add(func.eq(lamExpr));
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
      	Expression lamExpr = exprManager.lambda(Lists.newArrayList(boundVar0, boundVar1),
      			encoding.ff());
      	assumps.add(func.eq(lamExpr));
      }
		}
		
	  return assumps;
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				encoding.within(ptrExpr, sizeExpr, vars[0]), body);
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccess(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						sizeExpr.neq(formatter.getSizeZero()),
						encoding.within(ptrExpr, sizeExpr, vars[0])),
						body);
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccessFree(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.and(
				body,
				encoding.not(
						encoding.within(ptrExpr, sizeExpr, vars[0])));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				encoding.within(ptrExpr, sizeExpr, vars[0], vars[1]), body);
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						sizeExpr.neq(formatter.getSizeZero()),
						encoding.within(ptrExpr, sizeExpr, vars[0], vars[1])),
						body);
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunValidAccessRangeFree(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.and(
				body,
				encoding.not(encoding.within(ptrExpr, sizeExpr, vars[0], vars[1])));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateHeapFunDisjoint(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		
		Expression bodyPrime = encoding.and(
				body,
				encoding.implies(
						ptrExpr.neq(formatter.getNullAddress()),
						encoding.ifThenElse(sizeExpr.neq(formatter.getSizeZero()), 
								encoding.disjoint(vars[0], vars[1], ptrExpr, sizeExpr),
								encoding.disjoint(vars[0], vars[1], ptrExpr))));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}
	
	private void updateStackFunDisjoint(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.and(
				body,
				encoding.disjoint(ptrExpr, sizeExpr, vars[0], vars[1]));
		
		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateStackPreDisjoint(SingleLambdaStateExpression state, 
			Expression ptrExpr, Expression sizeExpr) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				disjoint_closure.eval(ptrExpr, sizeExpr),
				encoding.notOverflow(ptrExpr, sizeExpr),
				ptrExpr.neq(formatter.getNullAddress())).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptrExpr, sizeExpr);
	}
	
	private void updateHeapPreDisjoint(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
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
				disjoint_closure.eval(ptrExpr, sizeExpr)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptrExpr, sizeExpr);
	}
}
