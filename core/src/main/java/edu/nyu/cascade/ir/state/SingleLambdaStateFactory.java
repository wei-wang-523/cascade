package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
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
import edu.nyu.cascade.prover.type.ArrayType;
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
	public void reset() {}
	
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public void malloc(StateExpression state, Expression ptr, Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression region = createFreshRegion();
		BooleanExpression tt = encoding.tt().asBooleanExpression();
		
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, size);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}
	
	@Override
	public void calloc(StateExpression state, Expression ptr, Expression nitem,
			Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression multSize = encoding.times(nitem, size);
		Expression region = createFreshRegion();
		BooleanExpression tt = encoding.tt().asBooleanExpression();
		
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, multSize, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, multSize);
		state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
		state.addConstraint(applyMemset(state, region, multSize, 
				getExpressionEncoding().characterConstant(0),
				ptrNode));
	}
	
	@Override
	public void alloca(StateExpression state, Expression ptr, Expression size, Node ptrNode) {		
		Expression region = createFreshRegion();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
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
    
    /* Set the memory tracker */
		joinMemTrackers(joinState, preStates);
		
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
  public BooleanExpression applyValidMalloc(StateExpression state, Expression ptr, 
  		Expression size, Node ptrNode) {
		return memSafetyEncoding.validMalloc(ptr, size);
  }
	
	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
			Expression size, Expression value, Node ptrNode) {
		return singleStateFactory.applyMemset(
				state.asSingleLambda().getSingleState(), region, size, value, ptrNode);
	}
	
	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion,
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		return singleStateFactory.applyMemcpy(
				state.asSingleLambda().getSingleState(), destRegion, srcRegion, size, destNode, srcNode);
	}
	
	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr,
			Node ptrNode) {
		ArrayExpression markArr = state.asSingleLambda().getSingleState().getMark();
		return memSafetyEncoding.validFree(markArr, ptr);
	}
	
	@Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr,
  		Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccess(lambdaState);
		VariableExpression argVar = getFreshLabel(ptr);
		lambdaState.registerLabel(argVar, ptr);
	  lambdaState.registerPredicate(func.getUninterpretedFunc(), argVar);
	  return func.eval(argVar).asBooleanExpression();
	}
	
  @Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr, 
  		Expression size, Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccessRange(lambdaState);
		VariableExpression ptrVar = getFreshLabel(ptr);

		size = getDataFormatter().castToSize(size);
		
		lambdaState.registerLabel(ptrVar, ptr);
		VariableExpression sizeVar = getFreshLabel(size);
		lambdaState.registerLabel(sizeVar, size);
		lambdaState.registerPredicate(func.getUninterpretedFunc(), ptrVar, sizeVar);
	  return func.eval(ptrVar, sizeVar).asBooleanExpression();
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
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		
		// If the lval has been registered, do nothing
		if(!lambdaState.getLabelTable().containsValue(lval)) {
			int size = (int) getCTypeAnalyzer().getWidth(info.getXtcType());
			Expression lvalSize = getExpressionEncoding().integerConstant(size);
			addStackVar(lambdaState, lval, lvalSize);
		}
	}
	
	@Override
	public void propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		refreshDuplicateLabels(stateArg, cleanState);
		substitute(cleanState, stateVar, stateArg);
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
		
		propagateProperties(stateArg, cleanState);
	}
	
	/** Shallow copy */
  @Override
  public SingleLambdaStateExpression copy(StateExpression state) {
  	Preconditions.checkArgument(state.isSingle() && state.isLambda());
  	
  	SingleLambdaStateExpression singleLambdaState = state.asSingleLambda();
  	SingleStateExpression singleState = singleLambdaState.getSingleState();
  	SingleStateExpression singleStateCopy = singleStateFactory.copy(singleState);
  	SingleLambdaStateExpression stateClone = SingleLambdaStateExpression.create(singleStateCopy);
  	
  	stateClone.setConstraint(state.getConstraint());
  	stateClone.setGuard(state.getGuard());
  	stateClone.putAllPredicateMap(singleLambdaState.getPredicateMap());
  	stateClone.putLabelTable(singleLambdaState.getLabelTable());
  	stateClone.putAllSafetyPredicateClosures(singleLambdaState.getSafetyPredicateClosures());
  	stateClone.putAllSafetyPredicates(singleLambdaState.getSafetyPredicates());
  	return stateClone;
  }
	
	@Override
	public void initializeDefault(StateExpression state, Expression lval,
			Node lNode) {
		Preconditions.checkArgument(state.isLambda());
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.initializeDefault(singleState, lval, lNode);
	}
	
	@Override
	public void initializeValues(StateExpression state, Expression lval,
			Node lNode, List<Expression> rvals, List<Node> rNodes) {
		Preconditions.checkArgument(state.isLambda());
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.initializeValues(singleState, lval, lNode, rvals, rNodes);
	}
	
	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle() && state.isLambda());
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}

	@Override
	protected void updateMemState(StateExpression state, 
			Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
	}

	@Override
	protected void updateSizeState(StateExpression state, 
			Expression region, Expression size, Node ptrNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.updateSizeState(singleState, region, size, ptrNode);
	}
	
	@Override
	protected void updateMarkState(StateExpression state, 
			Expression region, BooleanExpression mark, Node ptrNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
	}

	/** <code>ptr</code> is not used here */
	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle() || state.isLambda());
		
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		SingleStateExpression singleState = lambdaState.getSingleState();
		singleStateFactory.updateSizeState(singleState, region, size, ptrNode);
  	addHeapRegInfo(lambdaState, region);
	}
	
	@Override
	protected void propagateProperties(StateExpression fromState, StateExpression toState) {
		toState.asSingleLambda().putLabelTable(fromState.asSingleLambda().getLabelTable());
		memSafetyEncoding.propagateSafetyPredicates(fromState.asSingleLambda(), toState.asSingleLambda());
	}

	@Override
	protected void doSubstitute(StateExpression state,
			final Collection<Expression> fromElems,
			final Collection<Expression> toElems,
			final Collection<Expression> fromPredicates,
			final Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isLambda() && state.isSingle());
		
		if(fromElems.isEmpty() && fromPredicates.isEmpty()) return;
		
		if(!fromElems.isEmpty()) {
			SingleLambdaStateExpression lambdaState = state.asSingleLambda();
			SingleStateExpression singleState = lambdaState.getSingleState();
			
			/* Substitute state elements */
			Expression newMem = singleState.getMemory().subst(fromElems, toElems);
			Expression newSize = singleState.getSize().subst(fromElems, toElems);
			Expression newMark = singleState.getMark().subst(fromElems, toElems);
			singleState.setMemory(newMem.asArray());
			singleState.setSize(newSize.asArray());
			singleState.setMark(newMark.asArray());
			
	    /* Substitute the real expressions stored in the label table*/
	    Table<VariableExpression, LabelType, Expression> labelTable = state.asSingleLambda().getLabelTable();
	    if(!labelTable.isEmpty()) {
	    	for(Cell<VariableExpression, LabelType, Expression> cell : ImmutableSet.copyOf(labelTable.cellSet())) {
	    		Expression value = cell.getValue();
	    		Expression valuePrime = value.subst(fromElems, toElems);
	    		labelTable.put(cell.getRowKey(), cell.getColumnKey(), valuePrime);
	    	}
	    }
		}
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(fromElems);
	  fromExprs.addAll(fromPredicates);
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(toElems);
		toExprs.addAll(toPredicates);
		
		if(fromExprs.isEmpty()) return;
	
	  if(state.getConstraint() != null) { /* Substitute constraint */
	  	BooleanExpression pc = state.getConstraint();
	  	pc = pc.subst(fromExprs, toExprs).asBooleanExpression();
	  	state.setConstraint(pc);
	  }
	  
	  { /* Substitute guards */
	  	BooleanExpression guard = state.getGuard();
	  	guard = guard.subst(fromExprs, toExprs).asBooleanExpression();
	  	state.setGuard(guard);
	  }
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
			StateExpression fromState, StateExpression toState) {
		return singleStateFactory.getSubstElemsPair(
				fromState.asSingleLambda().getSingleState(), 
				toState.asSingleLambda().getSingleState());
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
	
  @Override
	protected void substitute(StateExpression state, 
			StateExpression stateVar, StateExpression stateArg) {
		
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(stateVar, stateArg);
		Pair<List<Expression>, List<Expression>> substPredsPair =
				getSubstPredicatesPair(state, stateArg);
		
		doSubstitute(state, 
				substElemsPair.fst(),
				substElemsPair.snd(), 
				substPredsPair.fst(), 
				substPredsPair.snd());
	}
  
  @Override
  protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		ArrayExpression memArr = state.asSingleLambda().getSingleState().getMemory();
		xtc.type.Type idxType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(memArr, index, idxType);
  }

	@Override
	protected Expression eval(Expression expr, StateExpression stateVar,
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
	void refreshDuplicateLabels(StateExpression fromState, StateExpression toState) {		
		SingleLambdaStateExpression lambdaFrom = fromState.asSingleLambda();
		SingleLambdaStateExpression lambdaTo = toState.asSingleLambda();
		
		Table<VariableExpression, LabelType, Expression> toLabelTable = lambdaTo.getLabelTable();
		Table<VariableExpression, LabelType, Expression> fromLabelTable = lambdaFrom.getLabelTable();
		Collection<VariableExpression> duplicateLabels = Sets.intersection(toLabelTable.rowKeySet(), 
				fromLabelTable.rowKeySet());
		if(duplicateLabels.isEmpty()) return;
		
		Pair<Pair<Collection<VariableExpression>, Collection<VariableExpression>>, 
				 Pair<Collection<Expression>, Collection<Expression>>> 
		doublePair = getSubstitutionLabelsExprs(lambdaTo, duplicateLabels);
		
		Collection<VariableExpression> fromLabels = doublePair.fst().fst();
		Collection<VariableExpression> toLabels = doublePair.fst().snd();
		final Collection<Expression> fromExprs = doublePair.snd().fst();
		final Collection<Expression> toExprs = doublePair.snd().snd();
		
	  /* Update resState elements */
		SingleStateExpression singleStateTo = lambdaTo.getSingleState();
		Expression newMem = singleStateTo.getMemory().subst(fromExprs, toExprs);
		Expression newSize = singleStateTo.getSize().subst(fromExprs, toExprs);
		Expression newMark = singleStateTo.getMark().subst(fromExprs, toExprs);
		singleStateTo.setMemory(newMem.asArray());
		singleStateTo.setSize(newSize.asArray());
		singleStateTo.setMark(newMark.asArray());
	  
	  /* With duplicated labels and the label table should be updated */
		
	  refreshLabelTable(lambdaTo.getLabelTable(), fromLabels, toLabels, fromExprs, toExprs);
	  
	  /* Refresh duplicate labels in safety properties */
	  memSafetyEncoding.refreshDuplicateLabels(lambdaTo, fromLabels, toLabels);
	  
	  int capacity = fromLabels.size() + fromExprs.size();
	  Collection<Expression> from = Lists.newArrayListWithCapacity(capacity);
	  Collection<Expression> to = Lists.newArrayListWithCapacity(capacity);
	  
	  from.addAll(fromLabels); from.addAll(fromExprs);
	  to.addAll(toLabels); to.addAll(toExprs);
	  
    if(toState.getConstraint() != null) { /* Update constraint */
	  	BooleanExpression pc = lambdaTo.getConstraint();
	  	BooleanExpression pcPrime = pc.subst(from, to).asBooleanExpression();
	  	lambdaTo.setConstraint(pcPrime);
	  }
	  
	  { /* Update guards */
	  	BooleanExpression guard = lambdaTo.getGuard();
	  	BooleanExpression guardPrime = guard.subst(from, to).asBooleanExpression();
	  	lambdaTo.setGuard(guardPrime);
	  }
	}

	void doPropagateNewInfo(
			StateExpression fromState,
	    StateExpression toState,
	    Collection<Expression> fromExprs,
	    Collection<Expression> toExprs) {
		refreshLabelTable(fromState.asSingleLambda(), toState.asSingleLambda(), fromExprs, toExprs);
	}

	void addStackVar(SingleLambdaStateExpression lambdaState, Expression lval, Expression lvalSize) {		
		VariableExpression stVarExprVar = getFreshLabel(lval);
	  VariableExpression stVarSizeVar = getFreshLabel(lvalSize);
	  lambdaState.registerStackLabel(stVarExprVar, lval);
	  lambdaState.registerLabel(stVarSizeVar, lvalSize);
	  memSafetyEncoding.updateStackMemSafetyPredicates(lambdaState, stVarExprVar, stVarSizeVar);
	}
	
	void addHeapRegInfo(SingleLambdaStateExpression lambdaState, Expression hpRegExpr) {
		ArrayExpression sizeArr = lambdaState.getSingleState().getSize();
		Expression hpRegSize = sizeArr.index(hpRegExpr);
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
		
		Pair<Expression, Expression> pair1 = singleStateFactory
				.getCleanSizeSubstPair(state.getSingleState());
		fromExprs.add(pair1.fst()); toExprs.add(pair1.snd());
		
		Pair<Expression, Expression> pair2 = singleStateFactory
				.getCleanMarkSubstPair(state.getSingleState());
		fromExprs.add(pair2.fst()); toExprs.add(pair2.snd());
		
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
	 * fromExprs</code> to <code>toExprs</code>, and put it in the <code
	 * toState</code>
	 * 
	 * @param fromState
	 * @param toState
	 * @param fromExprs
	 * @param toExprs
	 */
	void refreshLabelTable(
			SingleLambdaStateExpression fromState,
			SingleLambdaStateExpression toState,
			Collection<? extends Expression> fromExprs,
			Collection<? extends Expression> toExprs) {
			
		Table<VariableExpression, LabelType, Expression> fromTable = fromState.getLabelTable();
		Table<VariableExpression, LabelType, Expression> toTable = toState.getLabelTable();
		
		if(fromTable.isEmpty()) return;
		
		if(fromExprs.isEmpty()) { toTable.putAll(fromTable); return;}
		
		for(Cell<VariableExpression, LabelType, Expression> cell : fromTable.cellSet()) {
			Expression arg = cell.getValue();
			Expression argPrime = arg.subst(fromExprs, toExprs);
			toTable.put(cell.getRowKey(), cell.getColumnKey(), argPrime);
		}
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
	void refreshLabelTable(Table<VariableExpression, LabelType, Expression> labelTable,
			Collection<VariableExpression> fromLabels,
			Collection<VariableExpression> toLabels,
			Collection<Expression> fromExprs,
			Collection<Expression> toExprs) {
		
		if(labelTable.isEmpty()) return;
		if(fromLabels.isEmpty() && fromExprs.isEmpty()) return;
	  
	  for(Cell<VariableExpression, LabelType, Expression> cell : ImmutableSet.copyOf(labelTable.cellSet())) {
	  	VariableExpression rowKey = cell.getRowKey();	  	
	  	VariableExpression rowKeyPrime = rowKey.subst(fromLabels, toLabels).asVariable();
	  	
	  	Expression val = cell.getValue();
	  	Expression valPrime = val.subst(fromExprs, toExprs);
	  	
	  	LabelType colKey = cell.getColumnKey();
	  	
	  	labelTable.put(rowKeyPrime, colKey, valPrime);
	  }
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
				String ptrBaseName = expr.asVariable().getName();
				Expression exprPrime = formatter.getFreshPtr(VAR_PREFIX + ptrBaseName, true);
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
	
	StateExpression freshSingleLambdaState(String elemName, ArrayType[] elemTypes) {
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
	SingleLambdaStateExpression createSingleLambdaState(String name, Expression mem, Expression size, Expression mark) {
		Preconditions.checkArgument(mem.isArray() && size.isArray() && mark.isArray());
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				SingleStateExpression.create(name, mem.asArray(), size.asArray(), mark.asArray()));
		return fresh;
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

