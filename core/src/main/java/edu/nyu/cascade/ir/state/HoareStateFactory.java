package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

public class HoareStateFactory<T> implements StateFactory<T> {
	
	private static String HOARE_MAP = "Hoare_map";
	
	private AbstractStateFactory<T> stateFactory;
	private Map<Expression, Expression> lr_var_binding_pair = Maps.newHashMap();
	
	@Inject
	private HoareStateFactory(AbstractStateFactory<T> _stateFactory) {
		stateFactory = _stateFactory;
	}
	
	public static <T> HoareStateFactory<T> create(AbstractStateFactory<T> _stateFactory) {
		return new HoareStateFactory<T>(_stateFactory);
  }

	@Override
  public Expression eval(Expression expr, StateExpression stateVar,
      StateExpression state) {
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				stateFactory.getSubstElemsPair(stateVar, state);
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				stateFactory.getSubstPredicatesPair(stateVar, state);
		Pair<List<Expression>, List<Expression>> substVarsPair = 
				getSubstVars(state);
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(substElemsPair.fst());
	  fromExprs.addAll(substPredsPair.fst());
	  fromExprs.addAll(substVarsPair.fst());
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(substElemsPair.snd());
		toExprs.addAll(substPredsPair.snd());
		toExprs.addAll(substVarsPair.snd());
		
		if(fromExprs.isEmpty()) return expr;
		
		return expr.subst(fromExprs, toExprs);
  }

	@Override
  public StateExpression resolvePhiNode(Collection<StateExpression> preStates) {
				
	  /* Collect common Hoare variable set (ignore local variables defined in branches) */
		Set<Expression> keySet = Sets.newHashSet();
	  for(StateExpression preState : preStates) {
	  	if(!preState.hasProperty(HOARE_MAP)) continue;
	  	Set<Expression> preHoareKeySet = getHoareMap(preState).keySet();
	  	if(keySet.isEmpty())
	  		keySet.addAll(preHoareKeySet);
	  	else
	  		keySet = Sets.intersection(keySet, preHoareKeySet);
	  }
	  
	  ExpressionEncoding encoding = getExpressionEncoding();
	  
	  Map<Expression, Expression> joinHoareMap = Maps.newHashMapWithExpectedSize(keySet.size());
	  int preStatesSize = Iterables.size(preStates);
	  for(Expression key : keySet) {
	  	List<Expression> preValues = Lists.newArrayListWithCapacity(preStatesSize);
	  	List<BooleanExpression> preGuardsLeft = Lists.newArrayListWithCapacity(preStatesSize);
	  	
	  	for(StateExpression preState : preStates) {
	  		if(!preState.hasProperty(HOARE_MAP)) continue;
	  		Expression preValue = getHoareMap(preState).get(key);
	  		BooleanExpression preGuard = preState.getGuard();
	  		if(!preValue.equals(key)) { // nothing has been updated
	  			preValues.add(preValue);
	  			preGuardsLeft.add(preGuard);
	  		}
	  	}
	  	
	  	// The first case is the default case
	  	if(preValues.size() < preStatesSize) {
	  		preValues.add(0, key);
	  		preGuardsLeft.add(0, encoding.not(encoding.and(preGuardsLeft)).asBooleanExpression());
	  	}
	  	
	  	Expression joinValue = stateFactory.getITEExpression(encoding, preValues, preGuardsLeft);
	  	joinHoareMap.put(key, joinValue);
	  }
	  
	  StateExpression state = stateFactory.resolvePhiNode(preStates);
	  state.setProperty(HOARE_MAP, joinHoareMap);
	  return state;
  }

	@Override
  public Expression cleanup(StateExpression state, Expression ptr) {
		Expression ptrPrime = stateFactory.cleanup(state, ptr);
		
		Pair<List<Expression>, List<Expression>> substVarsPair = getSubstVars(state);
		Collection<Expression> fromExprs = substVarsPair.fst();
		Collection<Expression> toExprs = substVarsPair.snd();
		
		if(!fromExprs.isEmpty()) ptrPrime = ptrPrime.subst(fromExprs, toExprs);
		
		return ptrPrime;
  }

	@Override
  public Expression applyValidMalloc(StateExpression state, Expression ptr,
      Expression size) {
	  return stateFactory.applyValidMalloc(state, ptr, size);
  }

	@Override
  public BooleanExpression applyValidFree(StateExpression state, Expression ptr) {
	  return stateFactory.applyValidFree(state, ptr);
  }

	@Override
  public Expression validAccess(StateExpression state, Expression arg) {
	  return stateFactory.validAccess(state, arg);
  }

	@Override
  public Expression validAccessRange(StateExpression state, Expression ptr,
      Expression size) {
	  return stateFactory.validAccessRange(state, ptr, size);
  }

	@Override
  public Expression getDisjointAssumption(StateExpression state) {
	  return stateFactory.getDisjointAssumption(state);
  }

	@Override
  public IRDataFormatter getDataFormatter() {
	  return stateFactory.getDataFormatter();
  }

	@Override
  public ExpressionEncoding getExpressionEncoding() {
	  return stateFactory.getExpressionEncoding();
  }

	@Override
  public StateExpression alloc(StateExpression state, Expression ptr,
      Expression size) {
		if(!lr_var_binding_pair.containsKey(ptr))
			return stateFactory.alloc(state, ptr, size);
		
		Expression region = stateFactory.createFreshRegion(ptr);
		StateExpression statePrime = updateMemState(state, ptr, region);
		StateExpression statePrime1 = stateFactory.updateSizeStateWithAlloc(statePrime, ptr, region, size);
		
		return statePrime1;
  }

	@Override
  public StateExpression updateMemState(StateExpression state,
      Expression memIdx, Expression memVal) {
		if(!lr_var_binding_pair.containsKey(memIdx))
		  return stateFactory.updateMemState(state, memIdx, memVal);
		
		Map<Expression, Expression> hoareMap;
		
		if(state.hasProperty(HOARE_MAP)) {
			hoareMap = Maps.newHashMap(getHoareMap(state));
		} else {
			hoareMap = Maps.newHashMap();
		}
		
		Expression r_var_binding = lr_var_binding_pair.get(memIdx);
		memVal = getDataFormatter().cast(memIdx, memVal);
		
		hoareMap.put(r_var_binding, memVal);
		StateExpression statePrime = state.copy();
		statePrime.setProperty(HOARE_MAP, hoareMap);
		return statePrime;
  }

	@Override
  public StateExpression updateSizeState(StateExpression state,
      Expression sizeIdx, Expression sizeVal) {
	  return stateFactory.updateSizeState(state, sizeIdx, sizeVal);
  }

	@Override
  public Expression deref(StateExpression state, Expression index) {
	  return stateFactory.deref(state, index);
  }

	@Override
  public StateExpression freshState() {
	  return stateFactory.freshState();
  }

	@Override
  public void propagateNewInfo(StateExpression fromState,
      StateExpression toState) {
		
		propagateNewSubState(fromState, toState);
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				stateFactory.getSubstElemsPair(fromState, toState);
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				stateFactory.getSubstPredicatesPair(fromState, toState);
		Pair<List<Expression>, List<Expression>> substVarsPair = 
				getSubstVars(toState);
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(substElemsPair.fst());
	  fromExprs.addAll(substPredsPair.fst());
	  fromExprs.addAll(substVarsPair.fst());
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(substElemsPair.snd());
		toExprs.addAll(substPredsPair.snd());
		toExprs.addAll(substVarsPair.snd());
		
		doPropagateNewInfo(fromState, toState,  fromExprs, toExprs);
  }

	@Override
  public StateExpression addStackVar(StateExpression state, Expression lval,
      IRVarInfo info) {
	  boolean isHoare = (Boolean) info.getProperty(Identifiers.HOARE_VAR);
	  if(!isHoare)		return stateFactory.addStackVar(state, lval, info);
	  
	  Expression lVarBinding = info.getLValBinding();
	  Expression rVarBinding = info.getRValBinding();
	  lr_var_binding_pair.put(lVarBinding, rVarBinding);
	  
	  Map<Expression, Expression> hoareMap = Maps.newHashMap();
	  if(state.hasProperty(HOARE_MAP))	hoareMap.putAll(getHoareMap(state));
	  hoareMap.put(rVarBinding, rVarBinding);
	  
	  StateExpression statePrime = state.copy();
	  statePrime.setProperty(HOARE_MAP, hoareMap);
	  return statePrime;
  }

	@Override
  public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		stateFactory.setLabelAnalyzer(preprocessor);
  }

	@Override
  public StateExpression scopeOptimize(StateExpression preEntState,
      StateExpression retState) {
	  return stateFactory.scopeOptimize(preEntState, retState);
  }
	
	@Override
	public StateExpression propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		IOUtils.debug().pln("Pre-state: " + stateArg);
		IOUtils.debug().pln("Clean-state: " + cleanState.toString());
		StateExpression statePrime = refreshDuplicateLabels(stateArg, cleanState);
	  statePrime = substitute(statePrime, stateVar, stateArg);
		stateFactory.propagateProperties(stateArg, statePrime);
    propagateMap(stateArg, statePrime);
    propagateNewSubState(stateArg, statePrime);
    IOUtils.debug().pln("Post-state: " + statePrime.toString());
	  return statePrime;
	}
	
	private void doPropagateNewInfo(StateExpression fromState, 
			StateExpression toState, 
			Collection<Expression> fromExprs, 
			Collection<Expression> toExprs) {
  	if(stateFactory instanceof MultiLambdaStateFactory) {
  		((MultiLambdaStateFactory<T>) stateFactory).doPropagateNewInfo(fromState, toState, fromExprs, toExprs);
  	} 
  	
  	if(stateFactory instanceof SingleLambdaStateFactory) {
  		((SingleLambdaStateFactory<T>) stateFactory).doPropagateNewInfo(fromState, toState, fromExprs, toExprs);
  	}
	}
	
	private StateExpression refreshDuplicateLabels(StateExpression fromState, StateExpression toState) {
  	if(stateFactory instanceof MultiLambdaStateFactory) {
  		return ((MultiLambdaStateFactory<T>) stateFactory).refreshDuplicateLabels(fromState, toState);
  	} 
  	
  	if(stateFactory instanceof SingleLambdaStateFactory) {
  		return ((SingleLambdaStateFactory<T>) stateFactory).refreshDuplicateLabels(fromState, toState);
  	}
  	
  	return toState;
	}
	
	private void propagateNewSubState(StateExpression fromState, StateExpression toState) {
		if(stateFactory instanceof MultiLambdaStateFactory) {
			((MultiLambdaStateFactory<T>) stateFactory).propagateNewSubState(fromState, toState);
			return;
		}
		
		if(stateFactory instanceof MultiStateFactory) {
			((MultiStateFactory<T>) stateFactory).propagateNewSubState(fromState, toState);
			return;
		}
		
		return;
	}

	private StateExpression substitute(StateExpression state,
	    StateExpression stateVar, StateExpression stateArg) {
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair;
		
  	if(stateFactory instanceof MultiLambdaStateFactory) {
  		substElemsPair = 
  				((MultiLambdaStateFactory<T>) stateFactory).getSubstElemsPair(state, stateArg, true);
  	} else if(stateFactory instanceof MultiStateFactory) {
  		substElemsPair = 
  				((MultiStateFactory<T>) stateFactory).getSubstElemsPair(state, stateArg, true);
  	} else if(stateFactory instanceof SingleLambdaStateFactory) {
  		substElemsPair = 
  				((SingleLambdaStateFactory<T>) stateFactory).getSubstElemsPair(stateVar, stateArg);
  	} else { // stateFactory instanceof SingleStateFactory
  		substElemsPair = 
  				((SingleStateFactory<T>) stateFactory).getSubstElemsPair(stateVar, stateArg);
  	}
  	
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				stateFactory.getSubstPredicatesPair(state, stateArg);
		
		Pair<List<Expression>, List<Expression>> substVarsPair = 
				getSubstVars(stateArg);
		
		Collection<Expression> fromElems = Lists.newArrayList();
		fromElems.addAll(substElemsPair.fst());
	  fromElems.addAll(substVarsPair.fst());
	  
		Collection<Expression> toElems = Lists.newArrayList();
		toElems.addAll(substElemsPair.snd());
		toElems.addAll(substVarsPair.snd());
		
		return stateFactory.doSubstitute(state, fromElems, toElems,
				substPredsPair.fst(), substPredsPair.snd());
	}

	private void propagateMap(StateExpression fromState,
	    StateExpression toState) {
		
		if(fromState.hasProperty(HOARE_MAP)) {
			Map<Expression, Expression> fromHoareMap = getHoareMap(fromState);
			Map<Expression, Expression> toHoareMapPrime = Maps.newHashMap(fromHoareMap);
			IOUtils.debug().pln("from state map: " + fromHoareMap);
			
			if(toState.hasProperty(HOARE_MAP)) {
				Map<Expression, Expression> toHoareMap = getHoareMap(toState);
				IOUtils.debug().pln("to state map: " + toHoareMap);
				
				Pair<List<Expression>, List<Expression>> substVarPair = getSubstVars(fromState);
				Collection<Expression> fromExprs = substVarPair.fst();
				Collection<Expression> toExprs = substVarPair.snd();
				
				if(fromExprs.isEmpty()) {
					toHoareMapPrime.putAll(toHoareMap);
				} else {
					for(Entry<Expression, Expression> entry : toHoareMap.entrySet()) {
						Expression key = entry.getKey();
						Expression value = entry.getValue().subst(fromExprs, toExprs);
						toHoareMapPrime.put(key, value);
					}
				}
			}
			
			toState.setProperty(HOARE_MAP, toHoareMapPrime);
		}
	}
	
	private Pair<List<Expression>, List<Expression>> getSubstVars(StateExpression state) {
		if(!state.hasProperty(HOARE_MAP))
			return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
			
		List<Expression> fromExprs = Lists.newArrayList();
		List<Expression> toExprs = Lists.newArrayList();
		
    Map<Expression, Expression> hoareMap = getHoareMap(state);
    for(Entry<Expression, Expression> entry : hoareMap.entrySet()) {
      Expression key = entry.getKey();
      Expression value = entry.getValue();
      if(key.equals(value)) continue;
      fromExprs.add(key);
      toExprs.add(value);
    }
		
		return Pair.of(fromExprs, toExprs);
	}

	@SuppressWarnings("unchecked")
  private Map<Expression, Expression> getHoareMap(StateExpression state) {
		Preconditions.checkArgument(state.hasProperty(HOARE_MAP));
		return (Map<Expression, Expression>) state.getProperty(HOARE_MAP);
	}
}
