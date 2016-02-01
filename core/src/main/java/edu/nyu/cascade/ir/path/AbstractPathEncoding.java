package edu.nyu.cascade.ir.path;

import java.util.List;
import java.util.Map.Entry;

import xtc.tree.Node;
import xtc.type.PointerT;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractPathEncoding implements PathEncoding {
	
  private final ExpressionEncoder encoder;
	
  private ValidityResult<?> runIsValid;
  private String failReason;
  private Expression traceExpression;

  protected AbstractPathEncoding(ExpressionEncoder encoder) {
    this.encoder = encoder;
  }

  protected abstract BooleanExpression assertionToBoolean(StateExpression path,
      Expression bool);
  
  @Override
  public void reset() {
  	traceExpression = null;
  	failReason = null;
  	runIsValid = null;
  }
  
	@Override
  public StateExpression declare(StateExpression pre, IRExpression lval) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  Expression lvalExpr = lval.toLval(pre, encoder);
	  checkPreAssertion(pre);
	  return declare(pre, lvalExpr, lval.getSourceNode());
  }
	
	@Override
  public StateExpression init(StateExpression pre, IRExpression lval, IRExpression... rvals) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  
	  Node lNode = lval.getSourceNode();
	  Expression lvalExpr = lval.toLval(pre, encoder);
	  
	  List<Node> rNodes = Lists.newArrayListWithExpectedSize(rvals.length);
	  List<Expression> rvalExprs = Lists.newArrayListWithExpectedSize(rvals.length);
	  
	  for(IRExpression rval : rvals) {
	  	rvalExprs.add(rval.toExpression(pre, encoder));
	  	rNodes.add(rval.getSourceNode());
	  }
	  
	  checkPreAssertion(pre);	  
	  updateTraceExpression(lNode, rvalExprs);
	  return init(pre, lvalExpr, lNode, rvalExprs, rNodes);
  }
	
	@Override
  public StateExpression call(StateExpression pre, IRExpression func, IRExpression... args) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  
	  Node funcNode = func.getSourceNode();
	  String funcName = funcNode.getString(0);
	  
	  List<Node> argNodes = Lists.newArrayListWithExpectedSize(args.length);
	  List<Expression> argExprs = Lists.newArrayListWithExpectedSize(args.length);
	  
	  for(IRExpression arg : args) {
	  	argExprs.add(arg.toExpression(pre, encoder));
	  	argNodes.add(arg.getSourceNode());
	  }
	  
	  checkPreAssertion(pre);
	  return call(pre, funcName, funcNode, argExprs, argNodes);
  }
	
  @Override
  public StateExpression assign(StateExpression pre, IRExpression lhs, IRExpression rhs) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression lhsExpr = lhs.toLval(pre, encoder);
    Expression rhsExpr = rhs.toExpression(pre, encoder);
    setValidAccess(pre, lhsExpr, lhs.getSourceNode());
    checkPreAssertion(pre);
    
    updateTraceExpression(lhs.getSourceNode(), rhsExpr);
    return assign(pre, lhsExpr, lhs.getSourceNode(), rhsExpr, rhs.getSourceNode());
  }

  @Override
  public StateExpression assume(StateExpression pre, IRExpression b) throws PathFactoryException {
  	boolean isGuard = b instanceof IRBooleanExpression;
  	Expression guard = b.toBoolean(pre, getExpressionEncoder());
  	checkPreAssertion(pre);
  	updateTraceExpression(null, guard);
    return assume(pre, guard, isGuard);
  }
  
  @Override
  public StateExpression malloc(StateExpression pre, IRExpression ptr, IRExpression size) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression ptrExpr = ptr.toLval(pre, encoder);
    Expression sizeExpr = size.toExpression(pre, encoder);
    setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    checkPreAssertion(pre);
    
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
    setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    checkPreAssertion(pre);
    
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
    setValidAccess(pre, ptrExpr, ptr.getSourceNode());
    checkPreAssertion(pre);
    
    StateExpression post = alloca(pre, ptrExpr, ptr.getSourceNode(), sizeExpr);
    Expression regionExpr = ptr.toExpression(post, encoder);
    updateTraceExpression(ptr.getSourceNode(), regionExpr);
    return post;
  }
  
  @Override
  public StateExpression free(StateExpression pre, IRExpression ptr) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression regionExpr = ptr.toExpression(pre, encoder);
    setValidFree(pre, regionExpr, ptr.getSourceNode());
    checkPreAssertion(pre);
    return free(pre, regionExpr, ptr.getSourceNode());
  }

  @Override
  public StateExpression havoc(StateExpression pre, IRExpression lhs) throws PathFactoryException {
    ExpressionEncoder encoder = getExpressionEncoder();
    Expression lhsExpr = lhs.toLval(pre, encoder);
    setValidAccess(pre, lhsExpr, lhs.getSourceNode());
    checkPreAssertion(pre);
    return havoc(pre, lhsExpr, lhs.getSourceNode());
  }
  
  @Override
	public StateExpression ret(StateExpression pre, IRExpression lhs) throws PathFactoryException {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  lhs.toExpression(pre, encoder);
	  checkPreAssertion(pre);
		return pre;
	}

	@Override
  public ValidityResult<?> checkAssertion(StateExpression path, Expression bool)
      throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    ExpressionManager exprManager = exprEncoding.getExpressionManager();

    try {
      TheoremProver tp = exprManager.getTheoremProver();
      BooleanExpression assertion = assertionToBoolean(path, bool);
      ImmutableSet<? extends BooleanExpression> assumptions = exprEncoding
          .getAssumptions();
      tp.assume(assumptions);
      ValidityResult<?> res = tp.checkValidity(assertion);
      exprEncoding.clearAssumptions();
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    }
  }

  @Override
  public SatResult<?> checkPath(StateExpression path) throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    TheoremProver tp = exprEncoding.getExpressionManager().getTheoremProver();
    try {
      BooleanExpression assertion = pathToBoolean(path);
      ImmutableSet<? extends BooleanExpression> assumptions = exprEncoding
          .getAssumptions();
      tp.assume(assumptions);
      SatResult<?> res = tp.checkSat(assertion);
      exprEncoding.clearAssumptions();
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
  public String getFailReason() {
  	return failReason;
  }
  
  @Override
  public ValidityResult<?> preRunIsValid() {
  	return runIsValid;
  }
  
  @Override 
  public Expression getTraceExpression() {
  	return traceExpression;
  }
	
	private void checkPreAssertion(StateExpression pre) throws PathFactoryException {
	  if(!pre.getPreAssertions().isEmpty()) {
	  	for(Entry<String, BooleanExpression> entry : pre.getPreAssertions().entrySet()) {
	  		ValidityResult<?> result = checkAssertion(pre, entry.getValue());
	  		runIsValid = result;
	  		if (!result.isValid()) {
	  			failReason = entry.getKey(); break;
	  	  }
	  	}
	  	
			pre.getPreAssertions().clear();
	  }
	}
	
	private BooleanExpression setValidAccess(StateExpression pre, Expression lhsExpr, Node lNode) {
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return null;
		BooleanExpression validAccess = getStateFactory().validAccess(pre, lhsExpr, lNode);
		pre.setPreAssertion(Identifiers.VALID_DEREF, validAccess);
		return validAccess;
	}
	
	private BooleanExpression setValidFree(StateExpression pre, Expression regionExpr, Node ptrNode) {
		if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return null;
		BooleanExpression validFree = getStateFactory().applyValidFree(pre, regionExpr, ptrNode);
    pre.setPreAssertion(Identifiers.VALID_FREE, validFree);
    return validFree;
	}
	
	private void updateTraceExpression(Node lNode, Expression rvalExpr) {
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
	
	private void updateTraceExpression(Node lNode, List<Expression> rvalExprs) {
		if(rvalExprs.size() != 1) return;
		
    ExpressionEncoding encoding = encoder.getEncoding();
		xtc.type.Type idxType = CType.getType(lNode);
		boolean isUnsigned = CType.isUnsigned(idxType);
		
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		int size = (int) cTypeAnalyzer.getWidth(
				CType.isScalar(idxType) ? idxType : PointerT.TO_VOID);
		traceExpression = encoding.castToInteger(rvalExprs.get(0), size, !isUnsigned);
	}
}
