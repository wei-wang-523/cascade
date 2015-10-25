package edu.nyu.cascade.ir.path;

import java.util.Collection;
import java.util.List;

import xtc.tree.Node;

import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractPathEncoding implements PathEncoding {
	
  private final ExpressionEncoder encoder;
  private final StateFactory<?> stateFactory;
	
  private Expression traceExpression;

  protected AbstractPathEncoding(ExpressionEncoder encoder) {
    this.encoder = encoder;
    this.stateFactory = encoder.getStateFactory();
  }
  
  @Override
  public void reset() {
  	traceExpression = null;
  	stateFactory.reset();
  }
  
	@Override
  public StateExpression declare(StateExpression pre, IRExpression lval) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  Expression lvalExpr = lval.toLval(pre, encoder);
	  
	  return declare(pre, lvalExpr, lval.getSourceNode());
  }
	
	@Override
	public StateExpression declareVarArray(StateExpression pre, 
			IRExpression lval, 
			IRExpression rval) throws PathFactoryException {
		ExpressionEncoder encoder = getExpressionEncoder();
		Expression lvalExpr = lval.toLval(pre, encoder);
		Expression rvalExpr = rval.toExpression(pre, encoder);
		
		return declareVarArray(pre, lvalExpr, lval.getSourceNode(), rvalExpr);
	}
	
	@Override
  public StateExpression init(StateExpression pre, IRExpression lval, IRExpression rval) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  Node lNode = lval.getSourceNode();
	  Node rNode = rval.getSourceNode();
	  
	  Expression lvalExpr = lval.toLval(pre, encoder);	  
	  Expression rvalExpr = rval.toExpression(pre, encoder);
	  
	  updateTraceExpression(lNode, rvalExpr);
	  return init(pre, lvalExpr, lNode, rvalExpr, rNode);
  }
	
	@Override
  public StateExpression call(StateExpression pre, IRExpression func, IRExpression... args) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  
	  Node funcNode = func.getSourceNode();
	  if(!funcNode.hasName("PrimaryIdentifier")) return pre;
	  String funcName = funcNode.getString(0);
	  
	  List<Node> argNodes = Lists.newArrayListWithExpectedSize(args.length);
	  List<Expression> argExprs = Lists.newArrayListWithExpectedSize(args.length);
	  
	  for(IRExpression arg : args) {
	  	argExprs.add(arg.toExpression(pre, encoder));
	  	argNodes.add(arg.getSourceNode());
	  }
	  
	  xtc.type.Type funcType = CType.getType(func.getSourceNode()).resolve();
	  if(funcType.isFunction() && !funcType.toFunction().getResult().resolve().isVoid()) {
	  	updateTraceExpression(argNodes.get(0), argExprs.get(0));
	  }
	  
	  return call(pre, funcName, funcNode, argExprs, argNodes);
  }
	
  @Override
  public StateExpression assign(StateExpression pre, IRExpression lhs, IRExpression rhs) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression lhsExpr = lhs.toLval(pre, encoder);
    Expression rhsExpr = rhs.toExpression(pre, encoder);
    stateFactory.setValidAccess(pre, lhsExpr, lhs.getSourceNode());
    
    updateTraceExpression(lhs.getSourceNode(), rhsExpr);
    return assign(pre, lhsExpr, lhs.getSourceNode(), rhsExpr, rhs.getSourceNode());
  }

  @Override
  public StateExpression assume(StateExpression pre, IRExpression b, boolean isGuard) throws PathFactoryException {
  	Expression guard = b.toBoolean(pre, getExpressionEncoder());
  	updateTraceExpression(null, guard);
    return assume(pre, guard, isGuard);
  }
  
  @Override
  public StateExpression malloc(StateExpression pre, IRExpression ptr, IRExpression size) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression ptrExpr = ptr.toLval(pre, encoder);
    Expression sizeExpr = size.toExpression(pre, encoder);
    stateFactory.setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    
    StateExpression post = malloc(pre, ptrExpr, ptr.getSourceNode(), sizeExpr);
    Expression regionExpr = ptr.toExpression(post, encoder);
    updateTraceExpression(ptr.getSourceNode(), regionExpr);
    return post;
  }
  
  @Override
  public StateExpression calloc(StateExpression pre, IRExpression ptr, IRExpression nitem, IRExpression size) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression ptrExpr = ptr.toLval(pre, encoder);
    Expression nitemExpr = nitem.toExpression(pre, encoder);
    Expression sizeExpr = size.toExpression(pre, encoder);
    stateFactory.setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    
    StateExpression post = calloc(pre, ptrExpr, ptr.getSourceNode(), nitemExpr, sizeExpr);
    Expression regionExpr = ptr.toExpression(post, encoder);
    updateTraceExpression(ptr.getSourceNode(), regionExpr);
    return post;
  }
  
  @Override
  public StateExpression alloca(StateExpression pre, IRExpression ptr, IRExpression size) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression ptrExpr = ptr.toLval(pre, encoder);
    Expression sizeExpr = size.toExpression(pre, encoder);
    stateFactory.setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    
    StateExpression post = alloca(pre, ptrExpr, ptr.getSourceNode(), sizeExpr);
    Expression regionExpr = ptr.toExpression(post, encoder);
    updateTraceExpression(ptr.getSourceNode(), regionExpr);
    return post;
  }
  
  @Override
  public StateExpression free(StateExpression pre, IRExpression ptr) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression regionExpr = ptr.toExpression(pre, encoder);
    stateFactory.setValidFree(pre, regionExpr, ptr.getSourceNode());
    updateTraceExpression(ptr.getSourceNode(), regionExpr);
    return free(pre, regionExpr, ptr.getSourceNode());
  }

  @Override
  public StateExpression havoc(StateExpression pre, IRExpression lhs) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression lhsExpr = lhs.toLval(pre, encoder);
    stateFactory.setValidAccess(pre, lhsExpr, lhs.getSourceNode());
    
    return havoc(pre, lhsExpr, lhs.getSourceNode());
  }
  
  @Override
	public StateExpression ret(StateExpression pre, IRExpression lhs) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  lhs.toExpression(pre, encoder);
	  
		return pre;
	}

	@Override
  public ValidityResult<?> checkAssertion(Expression assertion)
      throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    ExpressionManager exprManager = exprEncoding.getExpressionManager();

    try {
      TheoremProver tp = exprManager.getTheoremProver();
      
      Collection<? extends BooleanExpression> assumptions = exprEncoding.getAssumptions();
      tp.assume(assumptions);
      
      Collection<BooleanExpression> stateAssumptions = stateFactory.getAssumptions();
      tp.assume(stateAssumptions);
      
      ValidityResult<?> res = tp.checkValidity(assertion);
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    }
  }

  @Override
  public SatResult<?> checkPath(StateExpression state) throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    TheoremProver tp = exprEncoding.getExpressionManager().getTheoremProver();
    try {
      BooleanExpression assertion = stateFactory.stateToBoolean(state);
      Collection<? extends BooleanExpression> assumptions = exprEncoding.getAssumptions();
      tp.assume(assumptions);
      
      Collection<BooleanExpression> stateAssumptions = stateFactory.getAssumptions();
      tp.assume(stateAssumptions);
      
      SatResult<?> res = tp.checkSat(assertion);
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    }
  }

  /**
   * {@inheritDoc}
   * 
   * Default implementation: returns the expression factory associated with the
   * expression interpreter.
   */
  @Override
  public ExpressionEncoding getExpressionEncoding() {
    return getExpressionEncoder().getEncoding();
  }

  @Override
  public ExpressionEncoder getExpressionEncoder() {
    return encoder;
  }

  /**
   * {@inheritDoc}
   * 
   * Default implementation: returns the expression manager associated with the
   * expression interpreter.
   */
  @Override
  public ExpressionManager getExpressionManager() {
    return getExpressionEncoder().getEncoding().getExpressionManager();
  }

  @Override
  public StateExpression noop(StateExpression pre) {
    return pre;
  }
  
  @Override 
  public Expression getTraceExpression() {
  	return traceExpression;
  }
	
	private void updateTraceExpression(Node lNode, Expression rvalExpr) {
		if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
		if(lNode == null) {
			traceExpression = rvalExpr;
		} else {
	    ExpressionEncoding encoding = encoder.getEncoding();
			xtc.type.Type idxType = CType.getType(lNode);
			boolean isUnsigned = CType.isUnsigned(idxType);
			
			CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
			int size = (int) cTypeAnalyzer.getWidth(idxType);
			traceExpression = encoding.castToInteger(rvalExpr, size, !isUnsigned);
		}
	}
}
