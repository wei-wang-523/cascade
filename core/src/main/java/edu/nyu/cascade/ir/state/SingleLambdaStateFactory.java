package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import com.google.inject.Inject;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.PredicateClosure;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression.LabelType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Pair;

public class SingleLambdaStateFactory<T> extends AbstractStateFactory<T> {
	
	private static final String LABEL_NAME = "label";	
	private static final String VAR_PREFIX = "addr_of_";
	private final IRMemSafetyEncoding memSafetyEncoding;
	private final SingleStateFactory<T> singleStateFactory;
	
	@Inject
	SingleLambdaStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter, 
			IRMemSafetyEncoding memSafetyEncoding) {
	  super(encoding, formatter);
	  this.memSafetyEncoding = memSafetyEncoding;
	  this.singleStateFactory = createSingle(encoding, formatter);
  }
	
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public SingleLambdaStateExpression alloc(StateExpression state, Expression ptr, Expression size) {		
		Expression region = createFreshRegion(ptr);
		SingleLambdaStateExpression state1 = updateMemState(state, ptr, region);
		SingleLambdaStateExpression state2 = updateSizeStateWithAlloc(state1, ptr, region, size);
		return state2;
	}

	@Override
	public SingleLambdaStateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		/* Build the joined state */
  	Iterable<BooleanExpression> preGuards = Iterables.transform(preStates, pickGuard);
  	SingleLambdaStateExpression joinState = joinPreStates(preStates, preGuards);
  	
  	/* Set the constraint and guard */
    BooleanExpression joinConstraint = joinConstraints(preStates);
    joinState.setConstraint(joinConstraint);
    BooleanExpression joinGuard = joinGuards(preStates);
    joinState.setGuard(joinGuard);
    return joinState;
	}
	
  @Override
  public Expression cleanup(StateExpression state, Expression expr) {
    SingleLambdaStateExpression lambdaState = state.asSingleLambda();
    
    Pair<Collection<Expression>, Collection<Expression>> cleanupSubstPair = 
    		getCleanupSubstPair(lambdaState);
    
    boolean changed = false;
    do {
    	Expression exprPrime = expr.subst(
    			cleanupSubstPair.fst(), cleanupSubstPair.snd());
    	
    	changed = exprPrime.equals(expr);
    	expr = exprPrime;
    } while(!changed);
    return expr;
  }

	@Override
  public Expression eval(Expression expr, StateExpression stateVar,
  		StateExpression state) {
		
		Pair<List<Expression>, List<Expression>> sustElemsPair = getSubstElemsPair(stateVar, state);
		Pair<List<Expression>, List<Expression>> substPredsPair = getSubstPredicatesPair(stateVar, state);
		
		/* Get substitution pair of size array and memory array */
		List<Expression> fromExprs = Lists.newArrayList();
		fromExprs.addAll(sustElemsPair.fst()); 
		fromExprs.addAll(substPredsPair.fst());
		
		List<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(sustElemsPair.snd());	
		toExprs.addAll(substPredsPair.snd());
		
		if(fromExprs.isEmpty()) return expr;
		
		return expr.subst(fromExprs, toExprs);
  }
	
	/** The only new info is the fresh labels generated during visiting safety-related
	 * functions like valid_malloc, valid_access.
	 */
	@Override
	public void propagateNewInfo(StateExpression fromState, StateExpression toState) {
		/* Get substitution pair of size and memory elements */
		
		Pair<List<Expression>, List<Expression>> substElemsPair = getSubstElemsPair(fromState, toState);
		doPropagateNewInfo(fromState, toState, substElemsPair.fst(), substElemsPair.snd());
	}

	@Override
  public Expression applyValidMalloc(StateExpression state, Expression ptr, Expression size) {
		return memSafetyEncoding.validMalloc(ptr, size);
  }
	
	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr) {
		ArrayExpression sizeArr = state.asSingleLambda().getSingleState().getElement(1).asArray();
		return memSafetyEncoding.validFree(sizeArr, ptr);
	}
	
	@Override
  public Expression validAccess(StateExpression state, Expression arg) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccess(lambdaState);
		VariableExpression argVar = getFreshLabel(arg);
		lambdaState.registerLabel(argVar, arg);
	  lambdaState.registerPredicate(func.getUninterpretedFunc(), argVar);
	  return func.eval(argVar);
	}
	
  @Override
  public Expression validAccessRange(StateExpression state, Expression ptr, Expression size) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccessRange(lambdaState);
		VariableExpression ptrVar = getFreshLabel(ptr);
		lambdaState.registerLabel(ptrVar, ptr);
		VariableExpression sizeVar = getFreshLabel(size);
		lambdaState.registerLabel(sizeVar, size);
		lambdaState.registerPredicate(func.getUninterpretedFunc(), ptrVar, sizeVar);
	  return func.eval(ptrVar, sizeVar);
  }
	
  @Override
  public BooleanExpression getDisjointAssumption(StateExpression state) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		return memSafetyEncoding.getPreDisjoint(lambdaState);
  }
	
  @Override
  public SingleLambdaStateExpression freshState() {
    SingleLambdaStateExpression lambdaState = SingleLambdaStateExpression.create(
    		singleStateFactory.freshState());
    memSafetyEncoding.initMemSafetyPredicates(lambdaState);
    return lambdaState;
  }
	
	@Override
  public SingleLambdaStateExpression updateMemState(StateExpression state, 
  		Expression memIdx, Expression memVal) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
  	SingleStateExpression singleStatePrime = singleStateFactory
  			.updateMemState(lambdaState.getSingleState(), memIdx, memVal);
  	SingleLambdaStateExpression lambdaStatePrime = SingleLambdaStateExpression.create(singleStatePrime);
  	copySafetyProperties(lambdaState, lambdaStatePrime);
    return lambdaStatePrime;
  }
  
  @Override
  public SingleLambdaStateExpression updateSizeState(StateExpression state, 
  		Expression sizeIdx, Expression sizeVal) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
  	SingleStateExpression singleStatePrime = singleStateFactory
  			.updateSizeState(lambdaState.getSingleState(), sizeIdx, sizeVal);
  	SingleLambdaStateExpression lambdaStatePrime = SingleLambdaStateExpression.create(singleStatePrime);
  	copySafetyProperties(lambdaState, lambdaStatePrime);
    return lambdaStatePrime;
  }
	
	@Override
	public Expression deref(StateExpression state, Expression index) {
		ArrayExpression memArr = state.asSingleLambda().getSingleState().getElement(0).asArray();
		return getDataFormatter().indexMemoryArray(memArr, index);
	}
	
	@Override
	public SingleLambdaStateExpression addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		
		// If the lval has been registered, do nothing
		if(lambdaState.getLabelTable().containsValue(lval)) return lambdaState;
		
		Expression lvalSize = getExpressionEncoding().integerConstant(info.getSize());
		addStackVar(lambdaState, lval, lvalSize);
		
		return lambdaState;
	}
	
	/** Do nothing */
	@Override
	public StateExpression scopeOptimize(StateExpression preState, 
			StateExpression postState) {
		return postState;
	}
	
	@Override
	public StateExpression propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
	 StateExpression statePrime = refreshDuplicateLabels(stateArg, cleanState);
	 statePrime = substitute(statePrime, stateVar, stateArg);
	 propagateProperties(stateArg, statePrime);
	 return statePrime;
	}
	
	@Override
	protected void propagateProperties(StateExpression fromState, StateExpression toState) {    
		singleStateFactory.propagateProperties(fromState, toState);
		toState.asSingleLambda().putLabelTable(fromState.asSingleLambda().getLabelTable());
		memSafetyEncoding.propagateSafetyPredicates(fromState.asSingleLambda(), toState.asSingleLambda());
	}

	@Override
	protected SingleLambdaStateExpression doSubstitute(StateExpression state,
			final Collection<Expression> fromElems,
			final Collection<Expression> toElems,
			final Collection<Expression> fromPredicates,
			final Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isLambda() && state.isSingle());
		
		if(fromElems.isEmpty() && fromPredicates.isEmpty()) return state.asSingleLambda();
		
		SingleLambdaStateExpression lambdaStatePrime = state.asSingleLambda();
		
		if(!fromElems.isEmpty()) {
			
			/* Substitute state elements */
			Iterable<Expression> newElems = Iterables.transform(state.asSingleLambda().getElements(), 
					new Function<Expression, Expression>() {
	    	@Override
	    	public Expression apply(Expression elem) {
	    		return elem.subst(fromElems, toElems);
	    	}
	    });
			
			lambdaStatePrime = createSingleLambdaState(state.asSingleLambda().getName(), newElems);
			
	    /* Substitute the real expressions stored in the label table*/
	    Table<VariableExpression, LabelType, Expression> labelTable = state.asSingleLambda().getLabelTable();
	    if(!labelTable.isEmpty()) {
	    	Table<VariableExpression, LabelType, Expression> labelMapPrime = HashBasedTable.create();
	    	for(Cell<VariableExpression, LabelType, Expression> cell : labelTable.cellSet()) {
	    		Expression value = cell.getValue();
	    		Expression valuePrime = value.subst(fromElems, toElems);
	    		
	    		labelMapPrime.put(cell.getRowKey(), cell.getColumnKey(), valuePrime);
	    	}
	    	lambdaStatePrime.putLabelTable(labelMapPrime);
	    }
	    
	    /* Copy properties */
	    lambdaStatePrime.setProperties(state.asSingleLambda().getProperties());
	    
	    /* Copy safety-related properties */
	    lambdaStatePrime.putAllPredicateMap(state.asSingleLambda().getPredicateMap());
	    lambdaStatePrime.putAllSafetyPredicateClosures(state.asSingleLambda().getSafetyPredicateClosures());
	    lambdaStatePrime.putAllSafetyPredicates(state.asSingleLambda().getSafetyPredicates());
		}
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(fromElems);
	  fromExprs.addAll(fromPredicates);
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(toElems);
		toExprs.addAll(toPredicates);
		
    /* Substitute constraint */
    if(state.hasConstraint()) {
    	BooleanExpression pc = state.getConstraint();
    	if(!fromExprs.isEmpty()) pc = pc.subst(fromExprs, toExprs).asBooleanExpression();
    	lambdaStatePrime.setConstraint(pc);
    }
    
    /* Substitute guards */
    if(state.hasGuard()) {
    	BooleanExpression guard = state.getGuard();
    	if(!fromExprs.isEmpty()) guard = guard.subst(fromExprs, toExprs).asBooleanExpression();
    	lambdaStatePrime.setGuard(guard);
    }
    
    return lambdaStatePrime;
	}

	/** <code>ptr</code> is not used here */
	@Override
	protected SingleLambdaStateExpression updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size) {
		Preconditions.checkArgument(state.isSingle() || state.isLambda());
		
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		
  	StateExpression singleStatePrime = singleStateFactory
  			.updateSizeState(lambdaState.getSingleState(), region, size);
  	SingleLambdaStateExpression lambdaStatePrime = SingleLambdaStateExpression
  			.create(singleStatePrime.asSingle());
  	
  	copySafetyProperties(lambdaState, lambdaStatePrime);
  	addHeapRegInfo(lambdaStatePrime, region);
    return lambdaStatePrime;
	}
	
	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState) {		
		SingleLambdaStateExpression stateVar = fromState.asSingleLambda();
		SingleLambdaStateExpression state = toState.asSingleLambda();
		
		// FIXME: may don't need for memory and size array, only needs to update for constraint
		Multimap<Expression, Collection<Expression>> stateVarPredMap = stateVar.getPredicateMap();
		int size = stateVarPredMap.size();
		
		List<Expression> fromExprs = Lists.newArrayListWithCapacity(size);
		List<Expression> toExprs = Lists.newArrayListWithCapacity(size);
		
		for(Entry<Expression, Collection<Expression>> entry : stateVarPredMap.entries()) {
			Expression key = entry.getKey();
			assert(key.isBoolean() || key.isFunction());
			
			Expression fromExpr, toExpr;
			
			if(key.isBoolean()) {
				fromExpr = key;
				toExpr = getDisjointAssumption(state);
			} else {
				Collection<Expression> args = entry.getValue();
				FunctionExpression predicate = key.asFunctionExpression();
				fromExpr = predicate.apply(args);
				toExpr = memSafetyEncoding.applyUpdatedPredicate(state, predicate, args);
			}
			
			if(!fromExpr.equals(toExpr)) {
				fromExprs.add(fromExpr);	toExprs.add(toExpr);
			}
		}
		
		return Pair.of(fromExprs, toExprs);
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState, boolean fetchFreshMap) {
		return singleStateFactory.getSubstElemsPair(
				fromState.asSingleLambda().getSingleState(), 
				toState.asSingleLambda().getSingleState(), 
				fetchFreshMap);
	}

	@Override
	protected SingleLambdaStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		int preStateSize = Iterables.size(preStates);
		
		Collection<StateExpression> preSingleStates = Lists.newArrayListWithCapacity(preStateSize);
		for(StateExpression preState : preStates) {
			Preconditions.checkArgument(preState.isSingle() && preState.isLambda());
	    preSingleStates.add(preState.asSingleLambda().getSingleState());
		}
		
	  SingleStateExpression joinState = singleStateFactory.joinPreStates(preSingleStates, preGuards);
	  SingleLambdaStateExpression joinLambdaState = SingleLambdaStateExpression.create(joinState);
	  
	  memSafetyEncoding.initMemSafetyPredicates(joinLambdaState);
	  
	  // Create join state predicates 
	  joinSafetyProperties(preStates, preGuards, joinLambdaState);
	  
	  return joinLambdaState;
	}
	
  SingleLambdaStateExpression refreshDuplicateLabels(StateExpression fromState, StateExpression toState) {
		SingleLambdaStateExpression resState = toState.copy().asSingleLambda();
		
		SingleLambdaStateExpression lambdaFrom = fromState.asSingleLambda();
		SingleLambdaStateExpression lambdaTo = toState.asSingleLambda();
		
		Table<VariableExpression, LabelType, Expression> toLabelTable = lambdaTo.getLabelTable();
		Table<VariableExpression, LabelType, Expression> fromLabelTable = lambdaFrom.getLabelTable();
		Collection<VariableExpression> duplicateLabels = Sets.intersection(toLabelTable.rowKeySet(), 
				fromLabelTable.rowKeySet());
		if(duplicateLabels.isEmpty()) return resState;
		
		Pair<Pair<Collection<VariableExpression>, Collection<VariableExpression>>, 
				 Pair<Collection<Expression>, Collection<Expression>>> 
		doublePair = getSubstitutionLabelsExprs(lambdaTo, duplicateLabels);
		
		Collection<VariableExpression> fromLabels = doublePair.fst().fst();
		Collection<VariableExpression> toLabels = doublePair.fst().snd();
		final Collection<Expression> fromExprs = doublePair.snd().fst();
		final Collection<Expression> toExprs = doublePair.snd().snd();
		
	  /* Update resState elements */
	  Iterable<Expression> newElems = Iterables.transform(resState.getElements(), 
	  		new Function<Expression, Expression>() {
	  	@Override
	  	public Expression apply(Expression elem) {
	  		return elem.subst(fromExprs, toExprs);
	  	}
	  });
	  
	  SingleLambdaStateExpression resStatePrime = 
	  		createSingleLambdaState(resState.getName(), newElems);
	  
	  /* Copy properties -- include constraint and guard */
	  resStatePrime.setProperties(resState.getProperties());
	  
	  /* Update memory safety predicates, predicate closures and predicate map */
	  resStatePrime.putAllSafetyPredicateClosures(resState.getSafetyPredicateClosures());
	  resStatePrime.putAllSafetyPredicates(resState.getSafetyPredicates());
	  resStatePrime.setPredicateMap(resState.getPredicateMap());
	  
	  /* With duplicated labels and the label table should be updated */
		
	  Table<VariableExpression, LabelType, Expression> resLabelTablePrime = 
	  		refreshLabelTable(resState.getLabelTable(), fromLabels, toLabels, fromExprs, toExprs);
	  
	  resStatePrime.putLabelTable(resLabelTablePrime);
	  
	  /* Refresh duplicate labels in safety properties */
	  memSafetyEncoding.refreshDuplicateLabels(resStatePrime, fromLabels, toLabels);
	  
	  int capacity = fromLabels.size() + fromExprs.size();
	  Collection<Expression> from = Lists.newArrayListWithCapacity(capacity);
	  Collection<Expression> to = Lists.newArrayListWithCapacity(capacity);
	  
	  from.addAll(fromLabels); from.addAll(fromExprs);
	  to.addAll(toLabels); to.addAll(toExprs);
	  
	  /* Update constraint */
	  if(resState.hasConstraint()) {
	  	BooleanExpression pc = resState.getConstraint();
	  	BooleanExpression pcPrime = pc.subst(from, to).asBooleanExpression();
	  	resStatePrime.setConstraint(pcPrime);
	  }
	  
	  /* Update guards */
	  if(resState.hasGuard()) {
	  	BooleanExpression guard = resState.getGuard();
	  	BooleanExpression guardPrime = guard.subst(from, to).asBooleanExpression();
	  	resStatePrime.setGuard(guardPrime);
	  }
		
		return resStatePrime;
	}

	void doPropagateNewInfo(StateExpression fromState,
	    StateExpression toState, Collection<Expression> fromExprs,
	    Collection<Expression> toExprs) {
		Table<VariableExpression, LabelType, Expression> labelTable = 
				refreshLabelTable(
						fromState.asSingleLambda().getLabelTable(), fromExprs, toExprs);
		
		toState.asSingleLambda().putLabelTable(labelTable);
	}

	void addStackVar(SingleLambdaStateExpression lambdaState, Expression lval, Expression lvalSize) {		
		VariableExpression stVarExprVar = getFreshLabel(lval);
	  VariableExpression stVarSizeVar = getFreshLabel(lvalSize);
	  lambdaState.registerStackLabel(stVarExprVar, lval);
	  lambdaState.registerLabel(stVarSizeVar, lvalSize);
	  memSafetyEncoding.updateStackMemSafetyPredicates(lambdaState, stVarExprVar, stVarSizeVar);
	}
	
	void addHeapRegInfo(SingleLambdaStateExpression lambdaState, Expression hpRegExpr) {
		Expression hpRegExprBase = getDataFormatter().getBase(hpRegExpr);
		ArrayExpression sizeArr = lambdaState.getElement(1).asArray();
		Expression hpRegSize = sizeArr.index(hpRegExprBase);
	  VariableExpression hpRegExprVar = getFreshLabel(hpRegExpr);
	  VariableExpression hpRegSizeVar = getFreshLabel(hpRegSize);
	  lambdaState.registerHeapLabel(hpRegExprVar, hpRegExpr);
	  lambdaState.registerLabel(hpRegSizeVar, hpRegSize);
	  memSafetyEncoding.updateHeapMemSafetyPredicates(lambdaState, hpRegExprVar, hpRegSizeVar);
	}

	Pair<Collection<Expression>, Collection<Expression>> getCleanupSubstPair(
			SingleLambdaStateExpression state) {
		Collection<Expression> fromExprs, toExprs;
		fromExprs = Lists.newArrayList();
		toExprs = Lists.newArrayList();
		
		/* Get the pair of size array variable and constant size array */
		
		Pair<Expression, Expression> pair = singleStateFactory
				.getCleanSizeSubstPair(state.getSingleState());
		fromExprs.add(pair.fst()); toExprs.add(pair.snd());
		
		/* Get the pair of predicate, like pre_disjoint(label), disjoint(label_1, label_2)
		 * and its initial value. */
		
		for(Entry<Expression, Collection<Expression>> entry : state.getPredicateMap().entries()) {
			Expression key = entry.getKey();
			assert(key.isBoolean() || key.isFunction());
			if(key.isBoolean()) {				
				fromExprs.add(key);
			} else {				
				fromExprs.add(key.asFunctionExpression().apply(entry.getValue()));
			}
			
			Expression initBoolValue = memSafetyEncoding.getInitBoolValue(key);
			toExprs.add(initBoolValue);
		}
		
		/* Get the pair of label and its corresponding expression */
		
		for(Cell<VariableExpression, LabelType, Expression> cell : state.getLabelTable().cellSet()) {
			fromExprs.add(cell.getRowKey());
			toExprs.add(cell.getValue());
		}
		
		return Pair.of(fromExprs, toExprs);
	}

	/**
	 * Update the label table in <code>fromState</code>: substitute the
	 * real expression corresponding to the label from <code> 
	 * fromExprs</code> to <code>toExprs</code>
	 * 
	 * @param fromState
	 * @param fromExprs
	 * @param toExprs
	 * @return a updated label table
	 */
	Table<VariableExpression, LabelType, Expression> refreshLabelTable(
			Table<VariableExpression, LabelType, Expression> fromTable,
			Collection<? extends Expression> fromExprs,
			Collection<? extends Expression> toExprs) {
		
		if(fromTable.isEmpty()) return fromTable;
		
		if(fromExprs.isEmpty()) return fromTable;
		
		int rowSize = fromTable.rowKeySet().size();
		int colSize = fromTable.columnKeySet().size();
		
		Table<VariableExpression, LabelType, Expression> fromTablePrime = 
				HashBasedTable.create(rowSize, colSize);
		
		for(Cell<VariableExpression, LabelType, Expression> cell : fromTable.cellSet()) {
			Expression arg = cell.getValue();
			Expression argPrime = arg.subst(fromExprs, toExprs);
			fromTablePrime.put(cell.getRowKey(), cell.getColumnKey(), argPrime);
		}
		
		return fromTablePrime;
	}

	/**
	 * Substitute the keys in <code>labelTable</code> with <code>labelPair</code>.
	 * Substitute the values in <code>labelTable</code> with <code>exprPair</code>.
	 * 
	 * @param labelTable
	 * @param labelPair
	 * @param exprPair
	 * @return
	 */
	Table<VariableExpression, LabelType, Expression> refreshLabelTable(
			Table<VariableExpression, LabelType, Expression> labelTable,
			Collection<VariableExpression> fromLabels,
			Collection<VariableExpression> toLabels,
			Collection<Expression> fromExprs,
			Collection<Expression> toExprs) {
		
		if(labelTable.isEmpty()) return labelTable;
		if(fromLabels.isEmpty() && fromExprs.isEmpty()) return labelTable;
		
		int rowSize = labelTable.rowKeySet().size();
		int colSize = labelTable.columnKeySet().size();
		Table<VariableExpression, LabelType, Expression> resLabelTable = 
				HashBasedTable.create(rowSize, colSize);
	  
	  for(Cell<VariableExpression, LabelType, Expression> cell : labelTable.cellSet()) {
	  	VariableExpression rowKey = cell.getRowKey();	  	
	  	VariableExpression rowKeyPrime = rowKey.subst(fromLabels, toLabels).asVariable();
	  	
	  	Expression val = cell.getValue();
	  	Expression valPrime = val.subst(fromExprs, toExprs);
	  	
	  	LabelType colKey = cell.getColumnKey();
	  	
	  	resLabelTable.put(rowKeyPrime, colKey, valPrime);
	  }
	  
	  return resLabelTable;
	}

	/**
	 * Collection the substitution of labels and corresponding expressions (heap regions and stack
	 * variables)
	 * @param lambdaState
	 * @param duplicateLabels
	 * @return a pair of duplicate labels and substitute labels for safety related property update,
	 * 				 a pair of collection expressions for the update stack var and heap region: 
	 * 				 1). the original lval of stack var and heap region
	 * 				 2). the new lval of stack var and fresh heap region
	 */
	Pair<Pair<Collection<VariableExpression>, Collection<VariableExpression>>,
			 Pair<Collection<Expression>, Collection<Expression>>>
	getSubstitutionLabelsExprs(SingleLambdaStateExpression lambdaState, 
			Collection<VariableExpression> duplicateLabels) {
		
		int labelSize = duplicateLabels.size();
		
		Collection<VariableExpression> substLabels = Lists.newArrayListWithCapacity(labelSize);
		Collection<Expression> fromExprs = Lists.newArrayListWithExpectedSize(labelSize);
		Collection<Expression> toExprs = Lists.newArrayListWithExpectedSize(labelSize);
		
		Table<VariableExpression, LabelType, Expression> labelTable = lambdaState.getLabelTable();
		
		IRDataFormatter formatter = getDataFormatter();
		
		for(VariableExpression label : duplicateLabels ) {
			if(!duplicateLabels.contains(label)) continue;
			
			Map<LabelType, Expression> map = labelTable.row(label);
			assert(map.size() == 1);
			
			Entry<LabelType, Expression> entry = map.entrySet().iterator().next();
			/* only update region or stack variable, not the size */
			switch(entry.getKey()) {
			case HEAP:
			case STACK: {
				VariableExpression labelPrime = getFreshLabel(label);
				substLabels.add(labelPrime);
				Expression expr = entry.getValue();
				String ptrBaseName = expr.getNode().getString(0);
				Expression exprPrime = formatter.getFreshPtr(VAR_PREFIX + ptrBaseName, true);
				exprPrime.setNode(expr.getNode());
				fromExprs.add(expr);
				toExprs.add(exprPrime);
				break;
			}
			case OTHER: {
				VariableExpression labelPrime = getFreshLabel(label);
				substLabels.add(labelPrime);
				break;
			}
			default:
				break;
			}
		}
		
		return Pair.of(Pair.of(duplicateLabels, substLabels), Pair.of(fromExprs, toExprs));
	}
	
	/**
	 * Create a single state expression with <code>name</code> and value type <code>type</code>
	 * as memory state element type, and initialize all the safety predicates
	 * @param name
	 * @param type
	 * @return
	 */
	SingleLambdaStateExpression freshSingleLambdaState(String name, xtc.type.Type type) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				singleStateFactory.freshSingleState(name, type));
		memSafetyEncoding.initMemSafetyPredicates(fresh);
		return fresh;
	}
	
	StateExpression freshSingleLambdaState(String elemName, Type[] elemTypes) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				singleStateFactory.freshSingleState(elemName, elemTypes));
		memSafetyEncoding.initMemSafetyPredicates(fresh);
		return fresh;
  }
	
	/**
	 * Create a single state expression with <code>name</code> and value type <code>type</code>
	 * as memory state element type, without initializing safety predicates
	 * @param name
	 * @param elems
	 * @return
	 */
	SingleLambdaStateExpression createSingleLambdaState(String name, Iterable<Expression> elems) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				SingleStateExpression.create(name, elems));
		return fresh;
	}

	private SingleLambdaStateExpression substitute(StateExpression state, 
			StateExpression stateVar, StateExpression stateArg) {
		
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(stateVar, stateArg);
		Pair<List<Expression>, List<Expression>> substPredsPair =
				getSubstPredicatesPair(state, stateArg);
		
		SingleLambdaStateExpression lambdaStatePrime = doSubstitute(state, 
				substElemsPair.fst(),
				substElemsPair.snd(), 
				substPredsPair.fst(), 
				substPredsPair.snd());
	  
	  return lambdaStatePrime;
	}

	private void copySafetyProperties(SingleLambdaStateExpression from, SingleLambdaStateExpression to) {
		to.putAllPredicateMap(from.getPredicateMap());
		to.putLabelTable(from.getLabelTable());
		to.putAllSafetyPredicateClosures(from.getSafetyPredicateClosures());
		to.putAllSafetyPredicates(from.getSafetyPredicates());
	}

	private void joinSafetyProperties(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards, SingleLambdaStateExpression joinState) {
		ExpressionEncoding encoding = getExpressionEncoding();
		
		Collection<String> closurePropNames = memSafetyEncoding.getClosurePropNames();
		
		for(String name : closurePropNames) {
			Function<StateExpression, PredicateClosure> funcClosure = getFuncClosure(name);
			Iterable<PredicateClosure> preElems = Iterables.transform(preStates, funcClosure);
			PredicateClosure joinPreElems = getITEPredClosure(encoding, preElems, preGuards);
			joinState.putSafetyPredicateClosure(name, joinPreElems);
		}
		
		Collection<String> exprPropNames = memSafetyEncoding.getExprPropNames();
		
		for(String name : exprPropNames) {
			Function<StateExpression, BooleanExpression> func = getFuncExpr(name);
			Iterable<BooleanExpression> preElems = Iterables.transform(preStates, func);
			BooleanExpression joinPreElems = getITEPredicate(encoding, preElems, preGuards)
					.asBooleanExpression();
			joinState.putSafetyPredicate(name, joinPreElems);
		}
	  
	  for(StateExpression preState : preStates) { // Combine predicate map
	  	joinState.putAllPredicateMap(preState.asSingleLambda().getPredicateMap());
	  }
	  
	  for(StateExpression preState : preStates) {  // Combine label_map
	  	joinState.putLabelTable(preState.asSingleLambda().getLabelTable());
	  }
	}
	
	private VariableExpression getFreshLabel(Expression expr) {
		return getExpressionManager().variable(LABEL_NAME, expr.getType(), true);
	}

	private BooleanExpression getITEPredicate(ExpressionEncoding encoding, 
			Iterable<? extends Expression> exprs, 
	    Iterable<? extends Expression> guards) {
	  Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(guards));
	  	  
	  Iterator<? extends Expression> itr = exprs.iterator();
	  Iterator<? extends Expression> guardItr = guards.iterator();
	  
	  Expression resExpr = null;
	  
	  if(itr.hasNext()) {
	  	resExpr = itr.next();
	  	guardItr.next();  // the first case is the default case
	  }
	  
	  ExpressionManager exprManager = encoding.getExpressionManager();
	  while(itr.hasNext() && guardItr.hasNext()) {
	    BooleanExpression guard = guardItr.next().asBooleanExpression();
	    Expression currCase = itr.next();
	    resExpr = exprManager.ifThenElse(guard, currCase, resExpr);
	  }
	  return resExpr.asBooleanExpression();
	}

	private PredicateClosure getITEPredClosure(ExpressionEncoding encoding,
			Iterable<? extends PredicateClosure> preClosures, 
	    Iterable<? extends Expression> guards) {
	  Preconditions.checkArgument(Iterables.size(preClosures) == Iterables.size(guards));
	  
	  Iterator<? extends PredicateClosure> itr = preClosures.iterator();
	  Iterator<? extends Expression> guardItr = guards.iterator();
	  
	  Expression resBodyExpr = null;
	  Expression[] resVarExprs = null;
	  List<Expression> unInterFunc = Lists.newArrayListWithCapacity(Iterables.size(preClosures));
	  
	  if(itr.hasNext()) {
	  	PredicateClosure preClosure = itr.next();
	  	resBodyExpr = preClosure.getBodyExpr();
	  	resVarExprs = preClosure.getVars();
	  	unInterFunc.add(preClosure.getUninterpretedFunc());
	  	guardItr.next();  // the first case is the default case
	  }
	  
	  ExpressionManager exprManager = encoding.getExpressionManager();
	  while(itr.hasNext() && guardItr.hasNext()) {
	    BooleanExpression guard = guardItr.next().asBooleanExpression();
	    PredicateClosure preClosure = itr.next();
	    Expression currCase = preClosure.eval(resVarExprs); // TODO: may removed for non-unique variable creating
	    resBodyExpr = exprManager.ifThenElse(guard, currCase, resBodyExpr);
	    unInterFunc.add(preClosure.getUninterpretedFunc());
	  }
	  
	  final Expression firstFunc = unInterFunc.get(0);
	  
	  assert(Iterables.all(unInterFunc, new Predicate<Expression>(){
	  	@Override
	    public boolean apply(Expression expr) {
	  		return expr.equals(firstFunc);
	  	}
	  }));
	  
	  return memSafetyEncoding.suspend(firstFunc, resBodyExpr, resVarExprs);
	}

	private static Function<StateExpression, BooleanExpression> getFuncExpr(final String name) {
		return new Function<StateExpression, BooleanExpression>() {
			@Override
			public BooleanExpression apply(StateExpression state) {
				Preconditions.checkArgument(state.isSingle() && state.isLambda());
				return state.asSingleLambda().getSafetyPredicate(name);
			}
		};
	}
	
	private static Function<StateExpression, PredicateClosure> getFuncClosure(final String name) {
		return new Function<StateExpression, PredicateClosure>() {
	  	@Override
	  	public PredicateClosure apply(StateExpression state) {
	  		Preconditions.checkArgument(state.isSingle() && state.isLambda());
	  		return state.asSingleLambda().getSafetyPredicateClosure(name);
	  	}
		};
	}
}

