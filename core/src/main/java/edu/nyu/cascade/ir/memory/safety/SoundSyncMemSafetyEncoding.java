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
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public class SoundSyncMemSafetyEncoding extends AbstractMemSafetyEncoding {
	
	private static final String testOverflowVarName = Identifiers.uniquify("overflow_var");
	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
			SafetyPredicate.Kind.VALID_ACCESS.name(),
			SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());
	
	private final Expression ptrVar, sizeVar;
	
	private SoundSyncMemSafetyEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		Type ptrType = formatter.getAddressType();
		ptrVar = exprManager.variable(ptrVarName, ptrType, true);
		Type sizeType = getOffsetType();
		sizeVar = exprManager.variable(sizeVarName, sizeType, true);
	}
	
	public static SoundSyncMemSafetyEncoding create(ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new SoundSyncMemSafetyEncoding(encoding, formatter);
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
    
		Type sizeType = getOffsetType();
    Expression variable = encoding.getExpressionManager().variable(
    		testOverflowVarName, sizeType, false);
    Expression notOverflow = encoding.notOverflow(variable, size);
    
    /* size not overflow, but could be zero -- malloc(0) */
	  return encoding.or(assump, notOverflow);
  }
	
	@Override
	public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(getRefType()));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(getOffsetType()));
		Preconditions.checkArgument(ptr.getType().equals(formatter.getAddressType()));
	  
		Expression ptrRef = ptr.asTuple().index(0);
	  Expression size = sizeArr.index(ptrRef);
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
	public void propagateSafetyPredicates(SingleLambdaStateExpression fromState,
	    SingleLambdaStateExpression toState) {		
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
		
		Expression ptrRef = formatter.getBase(ptr);
		Expression nullRef = formatter.getBase(formatter.getNullAddress());
		
		assert(vars.length == 1);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptrRef.neq(nullRef),
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
		
		Expression ptrRef = formatter.getBase(ptr);
		Expression nullRef = formatter.getBase(formatter.getNullAddress());
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				body,
				encoding.and(
						ptrRef.neq(nullRef),
						size.neq(formatter.getSizeZero()),
						encoding.within(ptr, size, vars[0], vars[1])));
		
		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
	
	private void updateHeapFunDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = disjoint_closure.getUninterpretedFunc();
		Expression body = disjoint_closure.getBodyExpr();
		Expression[] vars = disjoint_closure.getVars();
		
		Expression ptrRef = formatter.getBase(ptr);
		Expression nullRef = formatter.getBase(formatter.getNullAddress());
		
		assert(vars.length == 2);
		
		Expression bodyPrime = encoding.and(
				body,
				encoding.implies(
						ptrRef.neq(nullRef),
						encoding.ifThenElse(size.neq(formatter.getSizeZero()), 
								encoding.disjoint(vars[0], vars[1], ptr, size),
								encoding.disjoint(vars[0], vars[1], ptr))));
		
		PredicateClosure disjoint_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, disjoint_closure_prime);
	}
	
	private void updateStackFunDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = disjoint_closure.getUninterpretedFunc();
		Expression body = disjoint_closure.getBodyExpr();
		Expression[] vars = disjoint_closure.getVars();
		
		assert(vars.length == 2);
    
		Expression bodyPrime = encoding.and(
				body,
				encoding.disjoint(ptr, size, vars[0], vars[1]));
		PredicateClosure disjoint_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, disjoint_closure_prime);
	}
	
	private void updateHeapPreDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);
		
		/* Here, we miss the clause like:
		 *     Expression variable = encoding.getExpressionManager().variable(
     *																			testOverflowVarName, sizeType, false);
     *		 
		 *     implies(ptrRef.neq(nullRef),
		 *     					encoding.lessThanOrEqual(variable, encoding.plus(variable, size)))
		 * Because the valid_malloc(ptr, size) has already specify it as assumption
		 */
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				disjoint_closure.eval(ptr, size)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptr, size);
	}
	
	private void updateStackPreDisjoint(SingleLambdaStateExpression state, 
			VariableExpression ptr, VariableExpression size) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();
		
		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);
		
		Expression ptrRef = formatter.getBase(ptr);
		Expression nullRef = formatter.getBase(formatter.getNullAddress());
		
		Type sizeType = getOffsetType();
    Expression variable = encoding.getExpressionManager().variable(
    		testOverflowVarName, sizeType, false);
		
		BooleanExpression pre_disjoint_prime = encoding.and(
				pre_disjoint,
				disjoint_closure.eval(ptr, size),
				encoding.notOverflow(variable, size),
				ptrRef.neq(nullRef)).asBooleanExpression();
		
		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptr, size);
	}

	private Type getOffsetType() {
		return formatter.getAddressType().asTuple().getElementTypes().get(1);
	}
	
	private Type getRefType() {
		return formatter.getAddressType().asTuple().getElementTypes().get(0);
	}
}
