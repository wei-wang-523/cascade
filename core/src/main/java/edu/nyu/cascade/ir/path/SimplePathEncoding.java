package edu.nyu.cascade.ir.path;

/** A path StateFactory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
 */

import java.util.Collection;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public class SimplePathEncoding extends AbstractPathEncoding {
  public static <Mem extends Expression> SimplePathEncoding create(
      ExpressionEncoder encoder) {
    return new SimplePathEncoding(encoder);
  }
  
  private SimplePathEncoding(ExpressionEncoder encoder) {
    super(encoder);
  }
  
  @Override
  public StateFactory<?> getStateFactory() {
  	return getExpressionEncoder().getStateFactory();
  }
  
	@Override
  public StateExpression declare(StateExpression preState, StateExpressionClosure lval) {		
    Node varNode = lval.getOutput().getNode();
    assert(varNode.hasName("SimpleDeclarator"));
    String name = varNode.getString(0);
    IRVarInfo info = (IRVarInfo) getExpressionEncoder().getCurrentScope().lookup(name);
    
    StateExpression currState = preState.copy();
    currState = getMemoryModel().declare(currState, lval.eval(currState), info);
    return currState;
  }
	
	@Override
	public StateExpression declareEnum(StateExpression preState, StateExpressionClosure ... rvals) {
		StateExpression currState = preState.copy();
		Collection<Expression> rvalExprs = Lists.newArrayListWithCapacity(rvals.length);
		for(StateExpressionClosure rval : rvals) {
			Expression rvalExpr = rval.eval(currState);
			rvalExprs.add(rvalExpr);
		}
		
		Expression distinctAssump = getExpressionEncoding().distinct(rvalExprs);
		
    if(!preState.hasConstraint()) {
    	currState.setConstraint(distinctAssump.asBooleanExpression());
    } else {
	    ExpressionManager exprManager = getExpressionManager();
    	BooleanExpression pc = preState.getConstraint();
    	BooleanExpression pcPrime = exprManager.ifThenElse(pc, distinctAssump,
    			exprManager.ff()).asBooleanExpression();
    	currState.setConstraint(pcPrime);
    }
    return currState;
	}
  
  @Override
  public StateExpression alloc(StateExpression preState, StateExpressionClosure lval,
  		StateExpressionClosure rval) {
  	StateExpression currState = preState.copy();
    currState = getMemoryModel().alloc(currState, lval.eval(currState), rval.eval(currState));
    return currState;
  }

  @Override
  public StateExpression assign(StateExpression preState,
  		StateExpressionClosure var, StateExpressionClosure val) {
  	StateExpression currState = preState.copy();
    currState = getMemoryModel().assign(currState, var.eval(currState), val.eval(currState));
    return currState;
  }

  @Override
  public StateExpression assume(StateExpression preState, StateExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));
    
    StateExpression currState = preState.copy();
    
    Expression exprPrime = expr.eval(currState);
    
    if(!preState.hasConstraint()) {
    	currState.setConstraint(exprPrime.asBooleanExpression());
    } else {
	    ExpressionManager exprManager = getExpressionManager();
    	BooleanExpression pc = preState.getConstraint();
    	BooleanExpression pcPrime = exprManager.ifThenElse(pc, exprPrime,
    			exprManager.ff()).asBooleanExpression();
    	currState.setConstraint(pcPrime);
    }
    return currState;
  }

  @Override
  public StateExpression emptyState() {
    StateExpression memState = getStateFactory().freshState();
    BooleanExpression pc = getExpressionManager().tt();
    memState.setConstraint(pc);
    return memState;
  }

  @Override
  public StateExpression free(StateExpression preState, StateExpressionClosure ptr) {
  	StateExpression currState = preState.copy();
    currState = getMemoryModel().free(currState, ptr.eval(currState));
    return currState;
  }

  @Override
  public StateExpression havoc(StateExpression preState, StateExpressionClosure lval) {
  	StateExpression currState = preState.copy();
    currState = getMemoryModel().havoc(currState, lval.eval(currState));
    return currState;
  }
  
  @Override
  public StateExpression noop(Collection<StateExpression> preStates) {
  	if(preStates.size() == 1) return preStates.iterator().next();
    return getStateFactory().resolvePhiNode(preStates);
  }

  @Override
	public StateExpression call(StateExpression preState, String func, StateExpressionClosure... operands) {
  	return preState;
	}

	@Override
  final protected BooleanExpression assertionToBoolean(StateExpression preState,
      StateExpressionClosure bool) {
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    StateExpression currState = preState.copy();
    
    ExpressionManager exprManager = getExpressionManager();
    BooleanExpression memorySafe = getStateFactory().getDisjointAssumption(preState)
    		.asBooleanExpression();
    
    BooleanExpression assumption = currState.hasConstraint() ? 
    		currState.getConstraint().and(memorySafe) : memorySafe;
    		
    Expression boolExpr = bool.eval(currState);
    Expression res = exprManager.implies(assumption, boolExpr);
    Expression resCleanup = getStateFactory().cleanup(currState, res);
    return resCleanup.asBooleanExpression();
  }

  @Override
  final protected BooleanExpression pathToBoolean(StateExpression preState) {    
    BooleanExpression memorySafe = getStateFactory().getDisjointAssumption(preState)
    		.asBooleanExpression();
    
    Expression pc = preState.getConstraint();
    Expression res = memorySafe.and(pc);
    Expression resCleanup = getStateFactory().cleanup(preState, res);
    return resCleanup.asBooleanExpression();
  }
}