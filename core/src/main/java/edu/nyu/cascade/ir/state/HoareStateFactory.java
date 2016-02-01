package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
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
	
	private final static String HOARE_MAP = "Hoare_map";
	
	private final AbstractStateFactory<T> stateFactory;
	private final Map<Expression, Integer> lvalToIndex = Maps.newHashMap();
	private final List<Expression> rvals = Lists.newArrayList();
	
	@Inject
	private HoareStateFactory(AbstractStateFactory<T> _stateFactory) {
		stateFactory = _stateFactory;
	}
	
	public static <T> StateFactory<T> create(AbstractStateFactory<T> _stateFactory) {
		return new HoareStateFactory<T>(_stateFactory);
  }
	
	@Override
	public void reset() {
		lvalToIndex.clear();
		rvals.clear();
		stateFactory.reset();
	}
	
  @Override
  public StateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		StateExpression state = stateFactory.resolvePhiNode(preStates);
		
		int preStatesSize = preStates.size();
	  Map<Integer, Multimap<Expression, BooleanExpression>> hoareGuardTable = Maps
	  		.newHashMapWithExpectedSize(lvalToIndex.size());
	  
	  for(StateExpression preState : preStates) {
	  	if(!preState.hasProperty(HOARE_MAP)) continue;
	  	Map<Integer, Expression> hoareMap = getHoareMap(preState);
  		BooleanExpression guard = preState.getGuard();
	  	for(Entry<Integer, Expression> entry : hoareMap.entrySet()) {
	  		int lvalIdx = entry.getKey();
	  		Expression value = entry.getValue();
	  		
	  		Multimap<Expression, BooleanExpression> hoareGuardMap;
	  		if(hoareGuardTable.containsKey(lvalIdx)) {
	  			hoareGuardMap = hoareGuardTable.get(lvalIdx);
	  		} else {
	  			hoareGuardMap = LinkedHashMultimap.create();
	  			hoareGuardTable.put(lvalIdx, hoareGuardMap);
	  		}
	  		hoareGuardMap.put(value, guard);
	  	}
	  }
	  
	  Collection<Integer> lvalIdxSet = hoareGuardTable.keySet();
	  Map<Integer, Expression> joinHoareMap = Maps.newHashMapWithExpectedSize(lvalIdxSet.size());
	  for(int lvalIdx : lvalIdxSet) {
	  	Multimap<Expression, BooleanExpression> guardHoareMap = hoareGuardTable.get(lvalIdx);
	  	Expression joinValue;
	  	if(guardHoareMap.size() < preStatesSize) {
	  		Expression defaultValue = rvals.get(lvalIdx);
	  		joinValue = stateFactory.getITEExpressionWithDefaultValue(guardHoareMap, defaultValue);
	  	} else {
	  		joinValue = stateFactory.getITEExpression(guardHoareMap);
	  	}
	  	joinHoareMap.put(lvalIdx, joinValue);
	  }
	  
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
  public BooleanExpression applyValidMalloc(StateExpression state, Expression ptr,
      Expression size, Node pNode) {
	  return stateFactory.applyValidMalloc(state, ptr, size, pNode);
  }

	@Override
  public BooleanExpression applyValidFree(StateExpression state, Expression ptr,
  		Node pNode) {
	  return stateFactory.applyValidFree(state, ptr, pNode);
  }
	
	@Override
	public BooleanExpression applyMemoryTrack(StateExpression state) {
		return stateFactory.applyMemoryTrack(state);
	}
	
	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region, 
			Expression size, Expression value, Node ptrNode) {
		return stateFactory.applyMemset(state, region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		return stateFactory.applyMemcpy(state, destRegion, srcRegion, size, destNode, srcNode);
	}
	
	@Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr,
  		Node pNode) {
		if(lvalToIndex.containsKey(ptr))
			return getExpressionEncoding().tt().asBooleanExpression();
		else
			return stateFactory.validAccess(state, ptr, pNode);
  }

	@Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
      Expression size, Node pNode) {
	  return stateFactory.validAccessRange(state, ptr, size, pNode);
  }

	@Override
  public BooleanExpression getDisjointAssumption(StateExpression state) {
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
  public void malloc(StateExpression state, Expression ptr,
      Expression size, Node ptrNode) {
		if(!lvalToIndex.containsKey(ptr)) {
			stateFactory.malloc(state, ptr, size, ptrNode);
			return;
		}
		
		Expression region = stateFactory.createFreshRegion();
		BooleanExpression tt = getExpressionEncoding().tt().asBooleanExpression();
		
		updateHoareMemState(state, ptr, ptrNode, region, null);		
		stateFactory.updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		stateFactory.updateMarkState(state, region, tt, ptrNode);
		
		stateFactory.plusRegionSize(state, size);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
  }
	
	@Override
  public void calloc(StateExpression state, Expression ptr, Expression nitem,
      Expression size, Node ptrNode) {
		if(!lvalToIndex.containsKey(ptr)) {
			stateFactory.calloc(state, ptr, nitem, size, ptrNode);
			return;
		}
		
		ExpressionEncoding encoding = getExpressionEncoding();
		
		Expression region = stateFactory.createFreshRegion();
		Expression multSize = encoding.times(nitem, size);
		BooleanExpression tt = encoding.tt().asBooleanExpression();
		
		updateHoareMemState(state, ptr, ptrNode, region, null);		
		stateFactory.updateSizeStateWithAlloc(state, ptr, region, multSize, ptrNode);
		stateFactory.updateMarkState(state, region, tt, ptrNode);
		
		stateFactory.plusRegionSize(state, multSize);
		state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
		state.addConstraint(applyMemset(state, region, multSize, 
				getExpressionEncoding().characterConstant(0),
				ptrNode));
  }
	
	@Override
  public void alloca(StateExpression state, Expression ptr,
      Expression size, Node ptrNode) {
		if(!lvalToIndex.containsKey(ptr)) {
			stateFactory.alloca(state, ptr, size, ptrNode);
			return;
		}
		
		Expression region = stateFactory.createFreshRegion();
		updateHoareMemState(state, ptr, ptrNode, region, null);		
		stateFactory.updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
  }

	@Override
	public void assign(StateExpression state, Expression memIdx, Node idxNode, Expression memVal, Node valNode) {
		if(!lvalToIndex.containsKey(memIdx)) {
			stateFactory.assign(state, memIdx, idxNode, memVal, valNode);
			return;
		}
		updateHoareMemState(state, memIdx, idxNode, memVal, valNode);
	}

	@Override
	public void initializeDefault(StateExpression state, Expression lval,
			Node lNode) {
		if(!lvalToIndex.containsKey(lval)) {
			stateFactory.initializeDefault(state, lval, lNode);
			return;
		}
		
		ExpressionEncoding encoding = getExpressionEncoding();
		int size = (int) stateFactory.getCTypeAnalyzer().getWidth(CType.getType(lNode));
		Expression zero = encoding.getExpressionManager().bitVectorZero(size);
		updateHoareMemState(state, lval, lNode, zero, null);
	}
	
	@Override
	public void initializeValues(StateExpression state, Expression lval,
			Node lNode, List<Expression> rvals, List<Node> rNodes) {
		if(!lvalToIndex.containsKey(lval)) {
			stateFactory.initializeValues(state, lval, lNode, rvals, rNodes); 
		} else {
			int rvalSize = rvals.size();
			assert (rvalSize == 0 || rvalSize == 1);
			Expression rval = rvalSize == 0 ? 
					stateFactory.getExpressionEncoding().zero() : rvals.get(0);
			Node rNode = rvalSize == 0 ? null : rNodes.get(0);
			updateHoareMemState(state, lval, lNode, rval, rNode);
		}
	}

	@Override
	public void free(StateExpression state, Expression region, Node ptrNode) {
		stateFactory.free(state, region, ptrNode);
	}

	@Override
  public Expression deref(StateExpression state, Expression memIdx, Node memIdxNode) {
		if(!lvalToIndex.containsKey(memIdx)) {
			return stateFactory.deref(state, memIdx, memIdxNode);
		}

		int idx = lvalToIndex.get(memIdx);
		Expression rval = rvals.get(idx);
		
		if(!state.hasProperty(HOARE_MAP)) return rval;
		
		Map<Integer, Expression> hoareMap = getHoareMap(state);
		if(!hoareMap.containsKey(idx)) return rval;
		
		return hoareMap.get(idx);
  }

	@Override
  public StateExpression freshState() {
	  return stateFactory.freshState();
  }

	@Override
  public void addStackVar(StateExpression state, Expression lval,
      IRVarInfo info) {
	  boolean isHoare = (Boolean) info.getProperty(Identifiers.HOARE_VAR);
	  if(!isHoare) {
	  	stateFactory.addStackVar(state, lval, info);
	  	return;
	  }
	  
	  Expression lVarBinding = info.getLValBinding();
	  Expression rVarBinding = info.getRValBinding();
	  int size = lvalToIndex.size();
	  lvalToIndex.put(lVarBinding, size);
	  rvals.add(rVarBinding);
  }

	@Override
  public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		stateFactory.setLabelAnalyzer(preprocessor);
  }
	
	@Override
	public void propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		IOUtils.debug().pln("Pre-state: " + stateArg);
		IOUtils.debug().pln("Clean-state: " + cleanState);
		refreshDuplicateLabels(stateArg, cleanState);
	  substitute(cleanState, stateVar, stateArg);
	  cleanState.addPreGuard(stateArg.getGuard());
	  cleanState.addConstraint(stateArg.getConstraint());
		 
		stateFactory.propagateProperties(stateArg, cleanState);
    propagateMap(stateArg, cleanState);
    propagateNewSubState(stateArg, cleanState);
    IOUtils.debug().pln("Post-state: " + cleanState.toString());
	}
	
	@Override
	public StateExpression copy(StateExpression state) {
		StateExpression stateClone = stateFactory.copy(state);
		if(stateClone.hasProperty(HOARE_MAP)) {
			Map<Integer, Expression> hoareMap = Maps.newHashMap(getHoareMap(state));
			stateClone.setProperty(HOARE_MAP, hoareMap);
		}
		return stateClone;
	}
	
	@Override
	public StateExpression getStateVar(StateExpression state) {
	  return stateFactory.getStateVar(state);
	}

	@Override
	public StateExpressionClosure suspend(
  		final StateExpression stateVar, final Expression expr) {
    return new StateExpressionClosure() {
      @Override
      public Expression eval(final StateExpression preState) {
        return HoareStateFactory.this.eval(expr, stateVar, preState);
      }

      @Override
      public edu.nyu.cascade.prover.type.Type getExprType() {
        return expr.getType();
      }

			@Override
      public Expression getExpression() {
	      return expr;
      }

			@Override
      public StateExpression getStateVar() {
	      return stateVar;
      }
    };
  }

	private void updateHoareMemState(StateExpression state,
	    Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		Preconditions.checkArgument(lvalToIndex.containsKey(index));
		if(!state.hasProperty(HOARE_MAP)) {
			state.setProperty(HOARE_MAP, Maps.newHashMap());
		}
		
		int idx = lvalToIndex.get(index);
		Expression rval = rvals.get(idx);
		
		ExpressionEncoding encoding = stateFactory.getExpressionEncoding();
		
		if(encoding.isInteger(rval)) {
			xtc.type.Type idxType = CType.getType(idxNode);
			boolean isUnsigned = valNode != null && CType.isUnsigned(CType.getType(valNode));
			int size = (int) stateFactory.getCTypeAnalyzer().getWidth(idxType);
			value = encoding.castToInteger(value, size, !isUnsigned);
			assert(value.getType().equals(rval.getType()));
		} else if(encoding.isBoolean(rval)) {
			value = encoding.castToBoolean(value);
		}
		
		Map<Integer, Expression> hoareMap = getHoareMap(state);
		hoareMap.put(idx, value);
	}
	
	private Expression eval(Expression expr, StateExpression stateVar,
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
		
		Expression exprPrime = fromExprs.isEmpty() ? expr : expr.subst(fromExprs, toExprs);
		return exprPrime;
	}

	/**
	 * Find the duplicate labels between <code>fromState</code> and <code>toState</code>,
	 * generate fresh labels for them, and replace old labels to fresh labels in everything 
	 * may contains those labels. 
	 * 
	 * @param fromState
	 * @param toState
	 * @return
	 */
	private void refreshDuplicateLabels(StateExpression fromState, StateExpression toState) {
  	if(!toState.isLambda()) return;
  	
  	if(toState.isMultiple()) {
  		((MultiLambdaStateFactory<T>) stateFactory).refreshDuplicateLabels(fromState, toState);
  	} else {
  		((SingleLambdaStateFactory<T>) stateFactory).refreshDuplicateLabels(fromState, toState);
  	}
	}
	
	/**
	 * Propagate the labels in <code>fromState</code> which are not in the <code>
	 * toState</code> to the <code>toState</code>
	 * @param fromState
	 * @param toState
	 */
	private void propagateNewSubState(StateExpression fromState, StateExpression toState) {
		if(!toState.isMultiple()) return;
		
		if(toState.isLambda()) {
			((MultiLambdaStateFactory<T>) stateFactory).propagateNewSubState(fromState, toState);
		} else {
			((MultiStateFactory<T>) stateFactory).propagateNewSubState(fromState, toState);
		}
	}

	private void substitute(StateExpression state,
	    StateExpression stateVar, StateExpression stateArg) {
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair =
				stateFactory.getSubstElemsPair(stateVar, stateArg);
  	
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
		
		stateFactory.doSubstitute(state, fromElems, toElems,
				substPredsPair.fst(), substPredsPair.snd());
	}

	private void propagateMap(StateExpression fromState,
	    StateExpression toState) {
		
		if(!fromState.hasProperty(HOARE_MAP)) return;
		
		Map<Integer, Expression> fromHoareMap = getHoareMap(fromState);
		Map<Integer, Expression> toHoareMapPrime = Maps.newHashMap(fromHoareMap);
		
		if(toState.hasProperty(HOARE_MAP)) {
			Map<Integer, Expression> toHoareMap = getHoareMap(toState);
			
			Pair<List<Expression>, List<Expression>> substVarPair = getSubstVars(fromState);
			Collection<Expression> fromExprs = substVarPair.fst();
			Collection<Expression> toExprs = substVarPair.snd();
			
			if(fromExprs.isEmpty()) {
				toHoareMapPrime.putAll(toHoareMap);
			} else {
				for(Entry<Integer, Expression> entry : toHoareMap.entrySet()) {
					int idx = entry.getKey();
					Expression value = entry.getValue().subst(fromExprs, toExprs);
					toHoareMapPrime.put(idx, value);
				}
			}
		}
		
		toState.setProperty(HOARE_MAP, toHoareMapPrime);
	}
	
	private Pair<List<Expression>, List<Expression>> getSubstVars(StateExpression state) {
		if(!state.hasProperty(HOARE_MAP))
			return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
			
		List<Expression> fromExprs = Lists.newArrayList();
		List<Expression> toExprs = Lists.newArrayList();
		
    Map<Integer, Expression> hoareMap = getHoareMap(state);
    for(Entry<Integer, Expression> entry : hoareMap.entrySet()) {
      int idx = entry.getKey();
      Expression rval = rvals.get(idx);
      Expression expr = entry.getValue();
      assert rval.getType().equals(expr.getType());
      fromExprs.add(rval);
      toExprs.add(expr);
    }
		return Pair.of(fromExprs, toExprs);
	}

	@SuppressWarnings("unchecked")
  private Map<Integer, Expression> getHoareMap(StateExpression state) {
		Preconditions.checkArgument(state.hasProperty(HOARE_MAP));
		return (Map<Integer, Expression>) state.getProperty(HOARE_MAP);
	}
}