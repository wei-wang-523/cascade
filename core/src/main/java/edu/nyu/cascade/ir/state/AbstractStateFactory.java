package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import xtc.tree.GNode;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

public abstract class AbstractStateFactory<T> implements StateFactory<T> {
  protected static final String REGION_VARIABLE_NAME = "region";
  
	private static Predicate<StateExpression> hasConstraint = new Predicate<StateExpression>() {
  	@Override
  	public boolean apply(StateExpression state) {
  		return state.hasConstraint();
  	}
  };
  
	private static Predicate<StateExpression> hasGuard = new Predicate<StateExpression>() {
  	@Override
  	public boolean apply(StateExpression state) {
  		return state.hasGuard();
  	}
  };
	
	private static Function<StateExpression, BooleanExpression> pickConstraint = 
			new Function<StateExpression, BooleanExpression>() {
  	@Override
  	public BooleanExpression apply(StateExpression state) {
  		return state.getConstraint();
  	}
  };
  
	protected static Function<StateExpression, BooleanExpression> pickGuard = 
			new Function<StateExpression, BooleanExpression>() {
  	@Override
  	public BooleanExpression apply(StateExpression state) {
  		return state.getGuard();
  	}
  };
	
	private final ExpressionEncoding encoding;
	private final IRDataFormatter formatter;
	
	@Inject
	public AbstractStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter) {
	  this.encoding = encoding;
	  this.formatter = formatter;
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

	@Override
	public IRDataFormatter getDataFormatter() {
	  return formatter;
	}

	@Override
	public ExpressionEncoding getExpressionEncoding() {
		return encoding;
	}
	
	/**
	 * Update the size array in <code>state</code> with <code>
	 * sizeArr[region] := size</code>.
	 * 
	 * @param state
	 * @param ptr is only useful in multi-state
	 * @param region
	 * @param size
	 * @return
	 */
	protected abstract StateExpression updateSizeStateWithAlloc(
			StateExpression state, 
			Expression ptr, 
			Expression region, 
			Expression size);
	
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
	
	protected abstract StateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards);

	protected abstract StateExpression doSubstitute(StateExpression state,
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
	 * @param fetchFreshMap is only useful for multi-state
	 * @return
	 */
	protected abstract Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState, boolean fetchFreshMap);
	
	/**
	 * Propagate the properties of <code>fromState</code> to <code>toState</code>.
	 * (1). add constraint of <code>fromState</code> to <code>toState</code>;
	 * (2). add guard of <code>fromState</code> to <code>toState</code>
	 * (3). propagate memory relates safety predicates of <code>fromState</code> to <code>toState</code>
	 * @param fromState
	 * @param toState
	 * @return
	 */
	protected abstract void propagateProperties(StateExpression fromState, StateExpression toState);
	
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState) {
		return getSubstElemsPair(fromState, toState, false);
	}

	ExpressionManager getExpressionManager() {
	  return encoding.getExpressionManager();
	}
	
	BooleanExpression joinConstraints(Iterable<? extends StateExpression> preStates) {
    // Create join state constraint 
    assert(Iterables.all(preStates, hasConstraint));
    Iterable<BooleanExpression> constraints = Iterables.transform(preStates, pickConstraint);
    return encoding.or(constraints).asBooleanExpression();
	}
	
	BooleanExpression joinGuards(Iterable<? extends StateExpression> preStates) {
		assert(Iterables.all(preStates, hasGuard));
		Iterable<BooleanExpression> guards = Iterables.transform(preStates, pickGuard);
    return encoding.or(guards).asBooleanExpression();
	}
	
	Expression createFreshRegion(Expression ptr) {
		Preconditions.checkNotNull(ptr.getNode());
    String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
    GNode regionNode = GNode.create("SimpleDeclarator", regionName);
    CType.unwrapped(CType.getType(ptr.getNode())).toPointer().getType().mark(regionNode);
    String regionScope = CType.getScopeName(ptr.getNode());
    regionNode.setProperty(CType.SCOPE, regionScope);
    regionNode.setLocation(ptr.getNode().getLocation());
    
    Expression region = getDataFormatter().getFreshPtr(regionName, false);
    region.setNode(regionNode);
    return region;
	}
	
	Expression getITEExpression(ExpressionEncoding encoding,
			Iterable<? extends Expression> exprs, 
	    Iterable<? extends Expression> guards) {
	  Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(guards));
	  ExpressionManager exprManager = encoding.getExpressionManager();
	  
	  Iterator<? extends Expression> itr = exprs.iterator();
	  Iterator<? extends Expression> guardItr = guards.iterator();
	  
	  Expression resExpr = null;
	  
	  if(itr.hasNext()) {
	  	resExpr = itr.next();
	  	guardItr.next();  // the first case is the default case
	  }
	  
	  while(itr.hasNext() && guardItr.hasNext()) {
	  	BooleanExpression guard = guardItr.next().asBooleanExpression();
	    Expression currCase = itr.next();
	    assert(resExpr.getType().equals(currCase.getType()));
	    resExpr = exprManager.ifThenElse(guard, currCase, resExpr);
	  }
	  
	  return resExpr;
	}
}
