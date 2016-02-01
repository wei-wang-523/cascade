package edu.nyu.cascade.ir.path;

/** A path StateFactory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
 */

import java.util.Collection;
import java.util.List;

import xtc.tree.Node;
import xtc.type.EnumeratorT;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.ReservedFunction;

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
  public StateExpression declare(StateExpression preState, Expression lval, Node sourceNode) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
    
    String name = sourceNode.getString(0);
    IRVarInfo info = (IRVarInfo) getExpressionEncoder().getCurrentScope().lookup(name);
    stateFactory.addStackVar(currState, lval, info);
    xtc.type.Type type = info.getXtcType();
    
    if(type.hasEnum()) {
    	ExpressionEncoding encoding = getExpressionEncoding();
    	Expression derefLval = stateFactory.deref(preState, lval, sourceNode);
    	
      Collection<BooleanExpression> assump = Lists.newArrayList();
    	for(EnumeratorT enumerator : type.toEnum().getMembers()) {
    		int val = enumerator.getConstant().bigIntValue().intValue();
    		Expression constExpr = encoding.integerConstant(val);
    		assump.add(derefLval.eq(constExpr));
    	}
    	
    	currState.addConstraint(encoding.or(assump).asBooleanExpression());
    }
    
    return currState;
  }
	
	@Override
  public StateExpression init(StateExpression preState, Expression lval, Node lNode, 
  		List<Expression> rvals, List<Node> rNodes) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
    
    stateFactory.initializeValues(currState, lval, lNode, rvals, rNodes);
    return currState;
  }
  
  @Override
  public StateExpression malloc(StateExpression preState, Expression lval, Node lNode,
  		Expression rval) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
  	stateFactory.malloc(currState, lval, rval, lNode);
    return currState;
  }
  
  @Override
  public StateExpression calloc(StateExpression preState, Expression lval, Node lNode,
  		Expression nitem, Expression size) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
  	stateFactory.calloc(currState, lval, nitem, size, lNode);
    return currState;
  }
  
  @Override
  public StateExpression alloca(StateExpression preState, Expression lval, Node lNode,
  		Expression rval) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
  	stateFactory.alloca(currState, lval, rval, lNode);
    return currState;
  }

  @Override
  public StateExpression assign(StateExpression preState, 
  		Expression lval, Node lNode, Expression rval, Node rNode) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
  	stateFactory.assign(currState, lval, lNode, rval, rNode);
    return currState;
  }

  @Override
  public StateExpression assume(StateExpression preState, Expression expr, boolean isEdge) {
    Preconditions.checkArgument(expr.isBoolean());
    StateExpression currState = preState;
  	
    if(isEdge) 	currState.addGuard(expr.asBooleanExpression());
    else 				currState.addConstraint(expr.asBooleanExpression());
    return currState;
  }

  @Override
  public StateExpression emptyState() {
    StateExpression memState = getStateFactory().freshState();
    BooleanExpression tt = getExpressionManager().tt();
    memState.setGuard(tt);
    return memState;
  }

  @Override
  public StateExpression free(StateExpression preState, Expression region, Node pNode) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
    
  	stateFactory.free(currState, region, pNode);
    return currState;
  }

  @Override
  public StateExpression havoc(StateExpression preState, Expression lval, Node lNode) {
    StateFactory<?> stateFactory = getStateFactory();
    StateExpression currState = preState;
    
  	Expression rval = stateFactory
  			.getDataFormatter().getUnknownValue(CType.getType(lNode));
  	
  	stateFactory.assign(currState, lval, lNode, rval, null);
    return currState;
  }
  
  @Override
  public StateExpression noop(Collection<StateExpression> preStates) {
  	Preconditions.checkArgument(!preStates.isEmpty());
  	if(preStates.size() == 1) return preStates.iterator().next();
    return getStateFactory().resolvePhiNode(preStates);
  }
  
  @Override
  public StateExpression call(StateExpression preState, String funcName, Node funcNode,
  		List<Expression> args, List<Node> argNodes) {
  	StateFactory<?> stateFactory = getStateFactory();
  	
  	if(funcName.equals(ReservedFunction.MEMSET)) {
  		Expression region = args.get(0);
  		Expression value = args.get(1);
  		Expression size = args.get(2);
  		BooleanExpression memset = stateFactory.applyMemset(preState, region, size, value, argNodes.get(0));
  		preState.addConstraint(memset);
  		return preState;
  	}
  	
  	if(funcName.equals(ReservedFunction.MEMCOPY)) {
  		Expression destRegion = args.get(0);
  		Expression srcRegion = args.get(1);
  		Expression size = args.get(2);
  		BooleanExpression memcpy = stateFactory.applyMemcpy(preState, destRegion, srcRegion, size, argNodes.get(0), argNodes.get(1));
  		preState.addConstraint(memcpy);
  		return preState;
  	}
  	
  	return preState;
  }

	@Override
  final protected BooleanExpression assertionToBoolean(StateExpression preState,
      Expression bool) {
    Preconditions.checkArgument( bool.isBoolean() );
    StateFactory<?> stateFactory = getStateFactory();
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    
    StateExpression currState = preState;
  	
    BooleanExpression memorySafe = stateFactory.getDisjointAssumption(currState)
    		.asBooleanExpression();
    Expression pc = currState.getConstraint();
    Expression guard = currState.getGuard();
    Expression assumption = pc == null ? exprEncoding.and(guard, memorySafe) :
    	exprEncoding.and(pc, guard, memorySafe);
    
    Expression res = exprEncoding.implies(assumption, bool);
    Expression resCleanup = stateFactory.cleanup(currState, res);
    return resCleanup.asBooleanExpression();
  }

  @Override
  public final BooleanExpression pathToBoolean(StateExpression preState) {
  	StateFactory<?> stateFactory = getStateFactory();
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    
    Expression pc = preState.getConstraint();
    Expression guard = preState.getGuard();
    Expression memorySafe = stateFactory.getDisjointAssumption(preState);
    Expression res = pc == null ? exprEncoding.and(guard, memorySafe) :
    	exprEncoding.and(pc, guard, memorySafe);
    	
    Expression resCleanup = stateFactory.cleanup(preState, res);
    return resCleanup.asBooleanExpression();
  }
}