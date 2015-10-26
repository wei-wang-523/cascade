package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.SoundLinearMemSafetyArrEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public class SoundLinearMemSafetyArrEncoding implements IRMemSafetyEncoding {
	
	protected final static String ptrVarName = "ptrVar";
	protected final static String sizeArrVarName = "sizeArrVar";
	protected final static String sizeVarName = "sizeVar";
	
	final static class SafetyPredicate {
		enum Kind {
			VALID_ACCESS,
			VALID_ACCESS_RANGE,
			DISJOINT,
			PRE_DISJOINT
		}
		
		static Kind parse(Expression key) {
			Preconditions.checkArgument(key.isFunction() || key.isBoolean());
			String name = key.isFunction() ? key.asFunctionExpression().getName() :
				key.asVariable().getName();
			
			if(name.equals(Kind.VALID_ACCESS_RANGE.name())) 
				return Kind.VALID_ACCESS_RANGE;
			
			if(name.equals(Kind.VALID_ACCESS.name())) 
				return Kind.VALID_ACCESS;
			
			if(name.equals(Kind.DISJOINT.name())) 
				return Kind.DISJOINT;
			
			if(name.equals(Kind.PRE_DISJOINT.name())) 
				return Kind.PRE_DISJOINT;
			
			throw new IllegalArgumentException("Invalid predicate " + name);
		}
	}
	
	private final IRDataFormatter formatter;
	private final ExpressionEncoding encoding;	
	private final Collection<BooleanExpression> assumptions;
	private final Expression ptrVar, sizeVar, sizeArrVar;
	
	protected SoundLinearMemSafetyArrEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		this.formatter = formatter;
		this.encoding = encoding;
		this.assumptions = initAssumptions();
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
		sizeArrVar = exprManager.variable(sizeArrVarName, formatter.getSizeArrayType(), true);
	}
	
	public static IRMemSafetyEncoding getInstance(ExpressionEncoding encoding, IRDataFormatter formatter, Strategy strategy) {
		return create(encoding, formatter);
	}

	@Override
	public PredicateClosure suspend(final Expression func, final Expression expr, final Expression... vars) {
		return new PredicateClosure() {
			
			@Override
			public String toString() {
				return new StringBuilder().append("\n\tfunc: ").append(func)
						.append("\n\texpr: ").append(expr).toString();
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
		PredicateClosure predicateClosure = state.getSafetyPredicateClosure(funcName);
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
	public PredicateClosure getValidAccessRange(SingleLambdaStateExpression state) {
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
	
	final void updatePredicateMap(SingleLambdaStateExpression fromState, 
			SingleLambdaStateExpression toState) {
		Multimap<Expression, Collection<Expression>> toPredMapPrime = HashMultimap.create(fromState.getPredicateMap());
		
		Multimap<Expression, Collection<Expression>> toPredMap = toState.getPredicateMap();
		for(Expression toFunc : toPredMap.keySet()) {
			Kind kind = SafetyPredicate.parse(toFunc);
			updatePredicateMapWithSafetyPredicate(kind, toState, toFunc, toPredMapPrime);
		}
		
		toState.setPredicateMap(toPredMapPrime);
	}
	
	final void initSafetyPredicate(Kind kind, SingleLambdaStateExpression state, Expression... vars) {
		ExpressionManager exprManager = encoding.getExpressionManager();
		String fname = kind.name();
		
		Type addrType = formatter.getAddressType();
	  Type sizeType = formatter.getSizeType();
	  Type sizeArrType = formatter.getSizeArrayType();
		
		switch(kind) {
		case DISJOINT: {
		  List<Type> argTypes = Lists.newArrayList(addrType, sizeArrType);
		  Expression ptrVar = vars[0];
		  Expression sizeArrVar = vars[1];
		  FunctionExpression func = 
		  		exprManager.functionDeclarator(fname,
		  				exprManager.functionType(argTypes,
		  						exprManager.booleanType()), false);
		  PredicateClosure closure = suspend(func, 
		  		func.apply(ptrVar, sizeArrVar), ptrVar, sizeArrVar);
		  state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case PRE_DISJOINT: {
			BooleanExpression predicate = exprManager.booleanType().tt();
			state.putSafetyPredicate(fname, predicate);
			break;
		}
		case VALID_ACCESS: {
			List<Type> argTypes = Lists.newArrayList(addrType, sizeArrType);
		  Expression ptrVar = vars[0];
		  Expression sizeArrVar = vars[1];
		  
			FunctionExpression func = 
					exprManager.functionDeclarator(fname, 
							exprManager.functionType(argTypes, 
									exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func,
					func.apply(ptrVar, sizeArrVar), ptrVar, sizeArrVar);
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		case VALID_ACCESS_RANGE: {
		  List<Type> argTypes = Lists.newArrayList(addrType, sizeArrType, sizeType);
		  Expression ptrVar = vars[0];
		  Expression sizeArrVar = vars[1];
		  Expression sizeVar = vars[2];
			
		  FunctionExpression func = 
					exprManager.functionDeclarator(fname, 
							exprManager.functionType(argTypes,
									exprManager.booleanType()), false);
			PredicateClosure closure = suspend(func, 
					func.apply(ptrVar, sizeArrVar, sizeVar), ptrVar, sizeArrVar, sizeVar);
			
			state.putSafetyPredicateClosure(fname, closure);
			break;
		}
		default:
			break;
		}
	}
	
	final void propagateSafetyPredicate(Kind kind, 
			SingleLambdaStateExpression fromState, 
			SingleLambdaStateExpression toState) {
		
		switch(kind) {
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
			SingleLambdaStateExpression state, 
			Expression func,
			Multimap<Expression, Collection<Expression>> predMap) {
		
		switch(kind) {
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

	private PredicateClosure updatePredicateClosure(PredicateClosure from, PredicateClosure to) {
		Expression[] toVars = to.getVars();
		BooleanExpression fromEvalBody = from.eval(toVars).asBooleanExpression();
		BooleanExpression toBody = to.getBodyExpr().asBooleanExpression();
		Expression toFunApp = to.getUninterpretedFunc().asFunctionExpression().apply(
				Lists.newArrayList(toVars));
		BooleanExpression toBodyPrime = toBody.subst(toFunApp, fromEvalBody).asBooleanExpression();
		Expression toFunPrime = from.getUninterpretedFunc();
		return suspend(toFunPrime, toBodyPrime, toVars);
	}

	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
			SafetyPredicate.Kind.VALID_ACCESS.name(),
			SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> FUN_DISJOINT_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());
	
	public static SoundLinearMemSafetyArrEncoding create(ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new SoundLinearMemSafetyArrEncoding(encoding, formatter);
	}
	
	@Override
  public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeArrVar);
			initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeArrVar, sizeVar);
		}
		initSafetyPredicate(Kind.DISJOINT, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state);
	}
	
	@Override
	public void freeUpdateHeapMemSafetyPredicates(
			SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
//		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
//			updateHeapFunValidAccessFree(state, ptrExpr, sizeExpr);
//			updateHeapFunValidAccessRangeFree(state, ptrExpr, sizeExpr);
//		}	
	}
	
	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state, Expression ptrExpr, Expression sizeExpr) {
		if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccess(state, ptrExpr);
			updateHeapFunValidAccessRange(state, ptrExpr);
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
	  return region.eq(formatter.getNullAddress()).or(mark.eq(tt));
	}
	
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
	
	private final void propagatePreDisjoint(SingleLambdaStateExpression fromState, 
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
	
	private Collection<BooleanExpression> initAssumptions() {
		Collection<BooleanExpression> assumps = Lists.newArrayList();
		
		ExpressionManager exprManager = encoding.getExpressionManager();
		Type addrType = formatter.getAddressType();
		Type sizeType = formatter.getSizeType();
		Type sizeArrType = formatter.getSizeArrayType();
		
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
							exprManager.functionType(addrType, sizeArrType,
									exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression boundVar1 = exprManager.boundExpression(sizeArrVarName, 1, sizeArrType, true);
				Expression assump_valid_access = encoding.forall(boundVar, boundVar1,
						func.apply(boundVar, boundVar1).eq(encoding.ff()));
				assumps.add(assump_valid_access.asBooleanExpression());
      } else {
      	Expression boundVar = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression boundVar1 = exprManager.boundVar(sizeArrVarName, sizeArrType, true);
      	Expression lamExpr = exprManager.lambda(Lists.newArrayList(boundVar, boundVar1),
      			encoding.ff());
      	assumps.add(func.eq(lamExpr));
      }
		}
		
		{ // VALID_ACCESS_RANGE
			FunctionExpression func = 
					exprManager.functionDeclarator(Kind.VALID_ACCESS_RANGE.name(), 
							exprManager.functionType(addrType, sizeType, sizeArrType,
									exprManager.booleanType()), false);
			
			if(Preferences.PROVER_Z3.equals(tpProviderName)) {
				Expression boundVar0 = exprManager.boundExpression(ptrVarName, 0, addrType, true);
				Expression boundVar1 = exprManager.boundExpression(sizeArrVarName, 1, sizeArrType, true);
				Expression boundVar2 = exprManager.boundExpression(sizeVarName, 2, sizeType, true);
  			Expression assump_valid_access_range = encoding.forall(boundVar0, boundVar1, boundVar2,
  					func.apply(boundVar0, boundVar1).eq(encoding.ff()));
  			assumps.add(assump_valid_access_range.asBooleanExpression());
      } else {
      	Expression boundVar0 = exprManager.boundVar(ptrVarName, addrType, true);
      	Expression boundVar1 = exprManager.boundVar(sizeArrVarName, sizeArrType, true);
      	Expression boundVar2 = exprManager.boundVar(sizeVarName, sizeType, true);
      	Expression lamExpr = exprManager.lambda(Lists.newArrayList(boundVar0, boundVar1, boundVar2),
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
	
	private void updateHeapFunValidAccess(SingleLambdaStateExpression state, Expression ptrExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 2);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						encoding.within(ptrExpr, vars[1].asArray().index(ptrExpr), vars[0])),
						body);
		
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
			Expression ptrExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);
		
		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();
		
		assert(vars.length == 3);
		Expression bodyPrime = encoding.or(
				encoding.and(
						ptrExpr.neq(formatter.getNullAddress()),
						encoding.within(ptrExpr, vars[1].asArray().index(ptrExpr), vars[0], vars[2])),
						body);
		
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
