package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractStateFactory<T> implements StateFactory<T> {
  protected static final String REGION_VARIABLE_NAME = "CASCADE.region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "CASCADE.m";
  protected static final String DEFAULT_SIZE_VARIABLE_NAME = "CASCADE.size";
  protected static final String DEFAULT_MARK_VARIABLE_NAME = "CASCADE.mark";
  protected static final String MEM_TRACKER = "MemTracker";
	
	protected static Function<StateExpression, BooleanExpression> pickGuard = 
			new Function<StateExpression, BooleanExpression>() {
  	@Override
  	public BooleanExpression apply(StateExpression state) {
  		return state.getGuard();
  	}
  };
	
	private final CType cTypeAnalyzer;
	private final ExpressionEncoding encoding;
	private final IRDataFormatter formatter;
	
	@Inject
	public AbstractStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter) {
	  this.encoding = encoding;
	  this.formatter = formatter;
	  this.cTypeAnalyzer = encoding.getCTypeAnalyzer();
  }
	
	public static <T> SingleLambdaStateFactory<T> createSingleLambda(ExpressionEncoding encoding,
      IRDataFormatter formatter, IRMemSafetyEncoding memSafetyEncoding) {
		return new SingleLambdaStateFactory<T>(encoding, formatter, memSafetyEncoding);
  }
	
	public static <T> MultiStateFactory<T> createMultiple(ExpressionEncoding encoding,
      IRDataFormatter formatter, IRPartitionHeapEncoder heapEncoder) {
		return new MultiStateFactory<T>(encoding, formatter, heapEncoder);
  }
	
	public static <T> SingleStateFactory<T> createSingle(ExpressionEncoding encoding,
      IRDataFormatter formatter, IRSingleHeapEncoder heapEncoder) {
		return new SingleStateFactory<T>(encoding, formatter, heapEncoder);
  }
	
	public static <T> MultiLambdaStateFactory<T> createMultipleLambda(ExpressionEncoding encoding,
      IRDataFormatter formatter, IRMemSafetyEncoding memSafetyEncoding) {
		return new MultiLambdaStateFactory<T>(encoding, formatter, memSafetyEncoding);
  }
	
	static <T> SingleStateFactory<T> createSingle(ExpressionEncoding encoding,
	    IRDataFormatter formatter) {
		return new SingleStateFactory<T>(encoding, formatter, null);
	}
	
	CType getCTypeAnalyzer() {
		return cTypeAnalyzer;
	}

	@Override
	public StateExpression getStateVar(StateExpression state) {
		if(state.isSingle())	return freshState();

		if(state.isLambda()) {
			MultiLambdaStateExpression freshStateVar = MultiLambdaStateExpression.create();
			Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
			for(Entry<String, SingleLambdaStateExpression> entry : stateMap.entrySet()) {
				String name = entry.getKey();
				SingleLambdaStateExpression singleLambdaState = entry.getValue();
				ArrayType[] elemType = singleLambdaState.getSingleState().getElemTypes();
				SingleStateExpression freshSingleState = freshSingleState(name, elemType);
				SingleLambdaStateExpression freshSingleLambdaState = SingleLambdaStateExpression
						.create(freshSingleState);
				freshStateVar.getStateMap().put(name, freshSingleLambdaState);
			}
			return freshStateVar;
			
		} else {
			MultiStateExpression freshStateVar = MultiStateExpression.create();
			Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
			for(Entry<String, SingleStateExpression> entry : stateMap.entrySet()) {
				String name = entry.getKey();
				SingleStateExpression singleState = entry.getValue();
				ArrayType[] elemType = singleState.getElemTypes();
				SingleStateExpression freshSingleState = freshSingleState(name, elemType);
				freshStateVar.getStateMap().put(name, freshSingleState);
			}
			return freshStateVar;
		}
	}

	@Override
	public IRDataFormatter getDataFormatter() {
	  return formatter;
	}

	@Override
	public ExpressionEncoding getExpressionEncoding() {
		return encoding;
	}
	
	@Override
	public void free(StateExpression state, Expression region, Node ptrNode) {
    minusRegionSize(state, region, ptrNode);
    Expression sizeZro = formatter.getSizeZero();
    updateSizeState(state, region, sizeZro, ptrNode);
		BooleanExpression ff = getExpressionEncoding().ff().asBooleanExpression();
		updateMarkState(state, region, ff, ptrNode);
	}
	
	@Override
	public void assign(StateExpression state, Expression index, Node idxNode, Expression value, Node valNode) {
		updateMemState(state, index, idxNode, value, valNode);
	}
	
	@Override
  public Expression deref(StateExpression state, Expression index, Node idxNode) {
		return dereference(state, index, idxNode);
  }
	
	@Override
	public StateExpressionClosure suspend(
  		final StateExpression stateVar, final Expression expr) {
    return new StateExpressionClosure() {
      @Override
      public Expression eval(final StateExpression preState) {
        return AbstractStateFactory.this.eval(expr, stateVar, preState);
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
	
	@Override
	public BooleanExpression applyMemoryTrack(StateExpression state) {
		if(!state.hasProperty(MEM_TRACKER)) return encoding.tt().asBooleanExpression();
		Expression memTracker = (Expression) state.getProperty(MEM_TRACKER);
		return formatter.getSizeZero().eq(memTracker);
	}
	
	/**
	 * Get the size of the region that <code>ptr</code> points-to
	 * from <code>state</code>
	 * 
	 * @param state
	 * @param ptr
	 * @param ptrNode
	 * @return
	 */
	protected abstract Expression getSizeOfRegion(
			StateExpression state, Expression region, Node ptrNode);
	
	/**
	 * Update the size array in <code>state</code> with <code>
	 * sizeArr[region] := size</code>.
	 * 
	 * @param state
	 * @param ptr is only useful in multi-state
	 * @param region
	 * @param size
	 * @param ptrNode is only useful in multi-state
	 * @return
	 */
	protected abstract void updateSizeStateWithAlloc(
			StateExpression state, 
			Expression ptr, 
			Expression region, 
			Expression size,
			Node ptrNode);
	
	/**
	 * Update the memory safety predicates registered in the predicate map of 
	 * <code>stateVar</code>, as "valid_access label_2", with the corresponding 
	 * updated predicate function in <code>state</code>, and apply it to "label_2"
	 * 
	 * @param stateVar
	 * @param state
	 * @return
	 */
	protected abstract Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState);

	protected abstract void doSubstitute(StateExpression state,
			final Collection<Expression> fromElems,
			final Collection<Expression> toElems,
			final Collection<Expression> fromPredicates,
			final Collection<Expression> toPredicates);
	
	/**
	 * Get the substitution element expressions pair from <code>fromState</code>
	 * and <code>toState</code>, and make sure if element pair are same, do not
	 * add them in.
	 * 
	 * @param fromState
	 * @param toState
	 * @return
	 */
	protected abstract Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState);
	
	/**
	 * Propagate the memory relates safety predicates of <code>fromState</code> to <code>toState</code>
	 * 
	 * @param fromState
	 * @param toState
	 * @return
	 */
	abstract protected void propagateProperties(StateExpression fromState, StateExpression toState);
	
	abstract protected StateExpression joinPreStates(
			Iterable<StateExpression> preStates, Iterable<BooleanExpression> preGuards);
	
	abstract protected void substitute(StateExpression state, 
			StateExpression stateVar, StateExpression stateArg);
	
	abstract protected void updateMemState(StateExpression state, 
  		Expression index, Node idxNode, Expression value, @Nullable Node valNode);
	
	abstract protected void updateSizeState(StateExpression state, 
  		Expression region, Expression sizeVal, Node ptrNode);
	
	abstract protected void updateMarkState(StateExpression state, 
  		Expression region, BooleanExpression mark, Node ptrNode);
	
  /**
   * Evaluate <code>expr</code> by replacing <code>stateVar</code>'s
   * (1). state elements (for normal expression)
   * (2). safety predicates (for validAccess(...) and validAccessRange(...))
   * with those in <code>state</code>
   * 
   * @param expr
   * @param stateVar
   * @param state
   * @return
   */
	abstract protected Expression eval(Expression expr, 
			StateExpression stateVar, StateExpression state);
	
	abstract protected Expression dereference(StateExpression state, Expression index, Node idxNode);

	ExpressionManager getExpressionManager() {
	  return encoding.getExpressionManager();
	}
	
	SingleStateExpression freshSingleState(String labelName, ArrayType[] elemTypes) {
		Preconditions.checkArgument(elemTypes.length == 3);
	  ArrayExpression memVar = elemTypes[0].variable(DEFAULT_MEMORY_VARIABLE_NAME + 
	  		labelName, false);
	  ArrayExpression sizeVar = elemTypes[1].variable(DEFAULT_SIZE_VARIABLE_NAME + 
	  		labelName, false);
	  ArrayExpression markVar = elemTypes[2].variable(DEFAULT_MARK_VARIABLE_NAME +
	  		labelName, false);
	  return SingleStateExpression.create(labelName, memVar, sizeVar, markVar);
	}
	
	BooleanExpression joinConstraints(Iterable<? extends StateExpression> preStates) {
		Multimap<Expression, BooleanExpression> guardPCMap = LinkedHashMultimap.create();
    for(StateExpression preState : preStates) {
    	if(preState.getConstraint() == null) continue;
    	guardPCMap.put(preState.getConstraint(), preState.getGuard());
    }
    
    if(guardPCMap.isEmpty()) return null;
    if(guardPCMap.size() < Iterables.size(preStates))
    	return getITEExpressionWithDefaultValue(guardPCMap, encoding.tt()).asBooleanExpression();
    else
    	return getITEExpression(guardPCMap).asBooleanExpression();
	}
	
	void joinMemTrackers(StateExpression joinState, Iterable<? extends StateExpression> preStates) {
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return;
		
		Multimap<Expression, BooleanExpression> guardRegionSizeTrackerMap = LinkedHashMultimap.create();
    for(StateExpression preState : preStates) {
    	if(!preState.hasProperty(MEM_TRACKER)) continue;
    	Expression regionSizeTracker = (Expression) preState.getProperty(MEM_TRACKER);
    	guardRegionSizeTrackerMap.put(regionSizeTracker, preState.getGuard());
    }
    
    if(guardRegionSizeTrackerMap.isEmpty()) return;
    
    Expression joinMemTracker;
    if(guardRegionSizeTrackerMap.size() < Iterables.size(preStates))
    	joinMemTracker = getITEExpressionWithDefaultValue(guardRegionSizeTrackerMap, formatter.getSizeZero());
    else
    	joinMemTracker = getITEExpression(guardRegionSizeTrackerMap);
    
		joinState.setProperty(MEM_TRACKER, joinMemTracker);
	}
	
	BooleanExpression joinGuards(Iterable<? extends StateExpression> preStates) {
		Iterable<BooleanExpression> guards = Iterables.transform(preStates, pickGuard);
    return encoding.or(guards).asBooleanExpression();
	}
	
	Expression createFreshRegion() {
    String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);    
    return formatter.getFreshPtr(regionName, false);
	}
	
	Expression getITEExpression(Multimap<Expression, BooleanExpression> guardHoareMap) {
		// Check if all the cases are same, then just return the case
		Collection<Expression> caseSet = guardHoareMap.keySet();
		if(caseSet.size() == 1) return caseSet.iterator().next();
		
	  Expression resExpr = null;
	  for(Expression currCase : caseSet) {
	  	if(resExpr == null) {
	  		resExpr = currCase;
	  	} else {
		  	BooleanExpression guard = getExpressionManager().or(guardHoareMap.get(currCase));
		    resExpr = guard.ifThenElse(currCase, resExpr);
	  	}
	  }
	  
	  return resExpr;
	}
	
	Expression getITEExpressionWithDefaultValue(Multimap<Expression, BooleanExpression> guardHoareMap,
			final Expression defaultCase) {
		Preconditions.checkNotNull(defaultCase);
		Collection<Expression> caseSet = guardHoareMap.keySet();
		
		if(caseSet.size() == 1 && defaultCase.equals(caseSet.iterator().next())) return defaultCase;
		
	  Expression resExpr = defaultCase;
	  for(Expression currCase : caseSet) {
	  	BooleanExpression guard = getExpressionManager().or(guardHoareMap.get(currCase));
	  	assert (currCase.getType().equals(resExpr.getType()));
	    resExpr = guard.ifThenElse(currCase, resExpr);
	  }
	  
	  return resExpr;
	}
	
	ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		ExpressionManager exprManager = getExpressionManager();
		return exprManager.storeAll(formatter.getSizeZero(), sizeArrType);
	}
	
	ArrayExpression getConstMarkArr(ArrayType markArrType) {
		ExpressionManager exprManager = getExpressionManager();
		return exprManager.storeAll(exprManager.ff(), markArrType);
	}
	
	void plusRegionSize(StateExpression state, Expression size) {
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return;
		
		Expression memTracker = state.hasProperty(MEM_TRACKER) ? 
				(Expression) state.getProperty(MEM_TRACKER) : formatter.getSizeZero();
		
		size = formatter.castToSize(size);
		memTracker = encoding.plus(memTracker, size);
		
		state.setProperty(MEM_TRACKER, memTracker);
	}
	
	void minusRegionSize(StateExpression state, Expression region, Node ptrNode) {
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return;
		
		Expression size = getSizeOfRegion(state, region, ptrNode);
		Expression regionSizeTracker = state.hasProperty(MEM_TRACKER) ? 
				(Expression) state.getProperty(MEM_TRACKER) : formatter.getSizeZero();
		regionSizeTracker = encoding.minus(regionSizeTracker, size);
		state.setProperty(MEM_TRACKER, regionSizeTracker);
	}
}
