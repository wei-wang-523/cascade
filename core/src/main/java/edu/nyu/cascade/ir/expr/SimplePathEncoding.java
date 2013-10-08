package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
 */

import java.util.Iterator;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public class SimplePathEncoding extends AbstractPathEncoding {
  public static <Mem extends Expression> SimplePathEncoding create(
      ExpressionEncoder encoder) {
    return new SimplePathEncoding(encoder);
  }

  private TupleType pathType;
  private static final String DEFAULT_PATH_STATE_NAME = "pathState";
  
  private SimplePathEncoding(ExpressionEncoder encoder) {
    super(encoder);
    ExpressionManager em = encoder.getExpressionManager();
    Type memType = encoder.getMemoryModel().getStateType();
    pathType = getExpressionManager().tupleType(Identifiers.uniquify(DEFAULT_PATH_STATE_NAME), memType, em.booleanType());
  }

  @Override
  public Expression alloc(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().alloc(memPrime, lval.eval(mem), rval.eval(mem));
    return getUpdatedPathState(pre, memPrime, pc);
  }

@Override
  public Expression assign(Expression pre,
      ExpressionClosure var, ExpressionClosure val) {
    Expression mem = pre.getChild(0);

    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().assign(memPrime, var.eval(mem), val.eval(mem));
    return getUpdatedPathState(pre, memPrime, pre.getChild(1));
  }

  @Override
  public Expression assume(Expression pre,
      ExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    Preconditions.checkArgument( expr.getInputType().equals( 
        pathType.getElementTypes().get(0) ));
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));
    
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    ExpressionManager exprManager = getExpressionManager();
    Expression pcPrime = exprManager.ifThenElse(pc, expr.eval(memPrime).asBooleanExpression(), 
        exprManager.ff());
    return getUpdatedPathState(pre, memPrime, pcPrime);
  }
  
  @Override
  public Expression check(Expression pre, ExpressionClosure bool) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    return getUpdatedPathState(pre, memPrime, pc);
  }

  @Override
  public Expression declareArray(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().declareArray(memPrime, ptr.eval(mem), size.eval(mem));
    return getUpdatedPathState(pre, memPrime, pc);
  }

@Override
  public Expression declareStruct(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().declareStruct(memPrime, ptr.eval(mem), size.eval(mem));
    return getUpdatedPathState(pre, memPrime, pc);
  }

@Override
  public Expression emptyPath() {
    Expression memState = getMemoryModel().initialState();
    Expression pcState = getExpressionManager().tt();
    return getFreshPathState(memState, pcState);
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval,
      String field, ExpressionClosure rval) {
    ExpressionManager exprManager =  getExpressionManager();
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression pcPrime = pc;
    if(getMemoryModel() instanceof ReachMemoryModel) {
      ReachMemoryModel mm = (ReachMemoryModel) getMemoryModel();
      Expression memAssume = mm.fieldAssign(mem, lval.eval(mem), field, rval.eval(mem));
      pcPrime = exprManager.ifThenElse(pc, memAssume, exprManager.ff());
    }
    
    return getUpdatedPathState(pre, mem, pcPrime);
  }

@Override
  public Expression free(Expression pre, ExpressionClosure ptr) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().free(memPrime, ptr.eval(mem));
    return getUpdatedPathState(pre, memPrime, pc);
  }

  @Override
  public TupleType getPathType() {
    return pathType;
  }

@Override
  public Expression havoc(Expression pre, ExpressionClosure lval) {
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().clearCurrentState();
    
    memPrime = getMemoryModel().havoc(memPrime, lval.eval(mem));
    return getUpdatedPathState(pre, memPrime, pc);
  }
  
  @Override
  public Expression noop(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    Preconditions.checkArgument(Iterables.size(prefixes) == Iterables.size(preGuards));
    
    // Split path state into two-lists: memory state & pc
    ImmutableList.Builder<Expression> memStateBuilder, pcBuilder;
    memStateBuilder = new ImmutableList.Builder<Expression>();
    pcBuilder = new ImmutableList.Builder<Expression>();
    for(Expression prefix : prefixes) {
    	memStateBuilder.add(prefix.getChild(0));
    	pcBuilder.add(prefix.getChild(1));
    }
    
    Expression resPC = getITEExpression(pcBuilder.build(), preGuards); 
    
    Expression resMemState = null;
    // Split memory state into multi-lists
    Type stateType = getMemoryModel().getStateType();
    if(stateType.isTuple()) {
    	int size = stateType.asTuple().size();
    	List<ImmutableList.Builder<Expression>> builders = Lists.newArrayListWithCapacity(size);
    	for(int i = 0; i < size; i++) {
    		builders.add(new ImmutableList.Builder<Expression>());
    	}
    	
    	for(Expression memState : memStateBuilder.build()) {
    		for(int i = 0; i < size; i++) {
    			builders.get(i).add(memState.getChild(i));
    		}
    	}
    	
    	ImmutableList.Builder<Expression> memStateElemsBuilder = new ImmutableList.Builder<Expression>();
    	for(ImmutableList.Builder<Expression> builder : builders) {
    		memStateElemsBuilder.add(getITEExpression(builder.build(), preGuards));
    	}
    	
    	resMemState = getMemoryModel().getUpdatedState(memStateElemsBuilder.build());
    } else {
    	resMemState = getITEExpression(memStateBuilder.build(), preGuards);
    }
    
    return getFreshPathState(resMemState, resPC);
  }

@Override
  public boolean setPathType(Type pathType) {
    Preconditions.checkArgument(pathType.isTuple());
    Preconditions.checkArgument(Preferences.isSet(Preferences.OPTION_MERGE_PATH));
    if(getMemoryModel() instanceof AbstractBurstallMemoryModel) {
      this.pathType = pathType.asTuple();
      ((AbstractBurstallMemoryModel) getMemoryModel()).setStateType(
          pathType.asTuple().getElementTypes().get(0).asTuple());
      return true;
    } else
      return false;
  }

@Override
  protected BooleanExpression assertionToBoolean(Expression pre,
      ExpressionClosure bool) {
    Preconditions.checkArgument( bool.getInputType().equals( 
        pathType.getElementTypes().get(0) ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    ExpressionManager em = getExpressionManager();
    Expression mem = pre.getChild(0);
    Expression pc = pre.getChild(1);
    BooleanExpression memorySafe = em.and(getMemoryModel().getAssumptions(mem));
    
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    /* The same currentState as check(). */
    if(currentState != null) getMemoryModel().clearCurrentState();
    
    Expression res = em.implies(em.and(pc, memorySafe), bool.eval(mem));
    
    /* Substitute alloc element's initial variable as constant array with all zero */
    res = getMemoryModel().substAlloc(res);

    return res.asBooleanExpression();
  }

@Override
  protected BooleanExpression pathToBoolean(Expression pre) {
    Expression pc = pre.getChild(1);
    Expression mem = pre.getChild(0);
    BooleanExpression memorySafe = getExpressionManager()
        .and(getMemoryModel().getAssumptions(mem));
    return memorySafe.and(pc);
  }

private Expression getITEExpression(Iterable<? extends Expression> exprs, 
      Iterable<? extends Expression> guards) {
    Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(guards));
    ExpressionManager exprManager = getExpressionManager();
    
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
      if(resExpr.getType().equals(currCase.getType())) {
      	resExpr = exprManager.ifThenElse(guard, currCase, resExpr);
      } else {
      	assert resExpr.isRecord() && currCase.isRecord();
      	resExpr = getMemoryModel().combineRecordStates(guard, currCase.asRecord(), resExpr.asRecord());
      }
    }
    return resExpr;
  }

	private TupleExpression getFreshPathState(Expression memoryPrime, Expression pcPrime) {		
		ExpressionManager exprManager = getExpressionManager();
		TupleType	pathStateTypePrime = exprManager.tupleType(Identifiers.uniquify(DEFAULT_PATH_STATE_NAME), 
					memoryPrime.getType(), pcPrime.getType());
		return exprManager.tuple(pathStateTypePrime, memoryPrime, pcPrime);
	}
  
  private TupleExpression getUpdatedPathState(Expression pathState, Expression memoryPrime, Expression pcPrime) {
  	Preconditions.checkArgument(pathState != null && pathState.isTuple() 
  			&& pathState.getType().asTuple().size() == 2);
  	List<? extends Type> pathStateElemTypes = pathState.getType().asTuple().getElementTypes();
  	boolean isUpdated = !(pathStateElemTypes.get(0).equals(memoryPrime.getType()) &&
  			pathStateElemTypes.get(1).equals(pcPrime.getType()));
  	
  	ExpressionManager exprManager = getExpressionManager();
  	TupleType pathStateTypePrime = pathState.getType().asTuple();
  	if(isUpdated) {
  		pathStateTypePrime = exprManager.tupleType(Identifiers.uniquify(DEFAULT_PATH_STATE_NAME), 
  				memoryPrime.getType(), pcPrime.getType());
  		pathType = pathStateTypePrime;
  	}
  	return exprManager.tuple(pathStateTypePrime, memoryPrime, pcPrime);
  }
}
