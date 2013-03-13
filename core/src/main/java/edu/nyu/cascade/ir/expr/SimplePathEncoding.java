package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state wrapped in a datatype:
 * <code>type path = ok T  | bottom</code>
 * where <code>ok(a)</code> is a feasible path to program state a and bottom is an 
 * infeasible path.
 * 
 * In the documentation below we use the following conventions:
 * <ul>
 * <li>is_ok(P) is a predicate that holds true if the value P is of the form ok(a)</li>
 * <li>val(P) is the value a when P = ok(a)</li>
 * <li>〚E〛(a) is the evaluation of expression e in state a (this is determined by the 
 * ExpressionFactory methods evalExpression and evalBoolean).</li>
 * </ul>
 */

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class SimplePathEncoding extends AbstractPathEncoding {
  public static <Mem extends Expression> SimplePathEncoding create(
      ExpressionEncoder encoder) {
    return new SimplePathEncoding(encoder);
  }

  private Expression stateVal;
  private final Type stateType;
  private Expression assumps;
  
  private SimplePathEncoding(ExpressionEncoder encoder) {
    super(encoder);
    stateVal = null;
    stateType = getExpressionEncoder().getMemoryModel().getStateType();
    assumps = getExpressionManager().tt();
  }

  @Override
  public Expression assign(Expression pre,
      ExpressionClosure var, ExpressionClosure val) {
      return getMemoryModel().assign(pre, 
          var.eval(pre), val.eval(pre));
  }

  @Override
  public Expression assume(Expression pre,
      ExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    Preconditions.checkArgument( expr.getInputType().equals( stateType ));
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));

    ExpressionManager exprManager = getExpressionManager();
    assumps = exprManager.ifThenElse(assumps, expr.eval(pre).asBooleanExpression(), 
        exprManager.ff());
    
    Expression res = pre;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) res = currentState.eval(pre);
    getMemoryModel().resetCurrentState();
    return res;
  }
  
  @Override
  public Expression assumeMemorySafe(Expression pre) {
    ExpressionManager exprManager = getExpressionManager();
    Expression result = exprManager.and(getMemoryModel().getAssumptions(pre));
    assumps = exprManager.ifThenElse(assumps, result, exprManager.ff());
    return pre;
  }
  
  @Override
  public Expression assumeReachRelation(Expression pre) {
    ExpressionManager exprManager = getExpressionManager();
    Expression result = exprManager.tt();
    if(getMemoryModel() instanceof ReachMemoryModel)  
      result = ((ReachMemoryModel) getMemoryModel()).getReachAssumptions(pre);
    assumps = exprManager.ifThenElse(assumps, result, exprManager.ff());
    return pre;
  }
  
//  private Expression addAssumptions(BooleanExpression expr)
//      throws PathFactoryException {
//    try {
//      ExpressionEncoding encoding = getExpressionEncoding();
//      ExpressionManager exprManager = encoding.getExpressionManager();
//      return exprManager.and(exprManager.and(encoding.getAssumptions()),
//          expr);
//    } catch (TheoremProverException e) {
//      throw new PathFactoryException(e);
//    } catch (ExpressionFactoryException e) {
//      throw new PathFactoryException(e);
//    }
//  }

  @Override
  protected BooleanExpression assertionToBoolean(Expression path,
      ExpressionClosure bool) {
    Preconditions.checkArgument( bool.getInputType().equals( stateType ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    return getExpressionManager().implies(assumps, bool.eval(path));
  }

  @Override
  public Expression emptyPath() {
    stateVal = getMemoryModel().initialState();
    return stateVal;
  }

  @Override
  public Type getPathType() {
    return stateType;
  }

  @Override
  protected BooleanExpression pathToBoolean(Expression path) {
    return assumps.asBooleanExpression();
  }
  
  @Override
  public Expression alloc(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression result = getMemoryModel().alloc(pre, lval.eval(pre), rval.eval(pre));
/*  ExpressionManager exprManager = getExpressionManager();
    Expression sideExpr;
    sideExpr = getMemoryModel().getSideAssumption();
    if(sideExpr != null)
      assumps = exprManager.ifThenElse(assumps, sideExpr, exprManager.ff());
*/
    return result;
  }
  
  @Override
  public Expression allocStack(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression result = getMemoryModel().allocStack(pre, lval.eval(pre), rval.eval(pre));
/*  ExpressionManager exprManager = getExpressionManager();
    Expression sideExpr;
    sideExpr = getMemoryModel().getSideAssumption();
    if(sideExpr != null)
      assumps = exprManager.ifThenElse(assumps, sideExpr, exprManager.ff());
*/
    return result;
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure var) {
    return getMemoryModel().free(pre, var.eval(pre));
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval,
      String field, ExpressionClosure rval) {
    if(!(getMemoryModel() instanceof ReachMemoryModel))
      return pre;
    ReachMemoryModel mm = (ReachMemoryModel) getMemoryModel();
    Expression result = mm.fieldAssign(pre, lval.eval(pre), field, rval.eval(pre));
    return result;
  }
  
  @Override
  public Expression havoc(Expression pre, ExpressionClosure lval) {
    Expression result = getMemoryModel().havoc(pre, lval.eval(pre));
    return result;
  }
}
