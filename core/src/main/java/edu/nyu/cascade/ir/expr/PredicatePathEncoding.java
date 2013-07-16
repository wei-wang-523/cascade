package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Path factory that encodes a path as a boolean function on states. I.e., a
 * path π is represented by a predicate P such that P(s) holds iff. state s is
 * reachable along π.
 */

public class PredicatePathEncoding extends
    AbstractPathEncoding {
  public static PredicatePathEncoding create(
      ExpressionEncoder encoder) {
    return new PredicatePathEncoding(encoder);
  }
  
  private static final String STATE_VARIABLE_NAME = "M";
  private static final String STATE_PRIME_VARIABLE_NAME = "M'";

  private final VariableExpression state, statePrime;
  private final FunctionType pathType;
  private final Type stateType;

  public PredicatePathEncoding(ExpressionEncoder encoder) {
    super(encoder);

    stateType = getExpressionEncoder().getMemoryModel().getStateType();
    state = stateType.variable(STATE_VARIABLE_NAME, true);
    statePrime = stateType.variable(STATE_PRIME_VARIABLE_NAME, true);
    
    Type booleanType = getExpressionManager().booleanType();
    pathType = getExpressionManager().functionType("pathType", stateType, booleanType);
  }

  @Override
  protected BooleanExpression assertionToBoolean(Expression path,
      ExpressionClosure bool) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    Preconditions.checkArgument( bool.getInputType().equals( stateType ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    BooleanExpression memorySafe = getExpressionManager().and(getMemoryModel().getAssumptions(path));
    Expression result = bool.eval(state);

    return forceBool(path,state).implies(memorySafe.implies(result));
  }

  /**
   * The assignment <code>x:=E</code> with precondition P(s) results in: P'(s) =
   * ∃s'. P(s') ∧ s = 〚x:=E〛(s')
   * 
   * @throws PathFactoryException
   */
  @Override
  public FunctionExpression assign(Expression path,
      ExpressionClosure lval, ExpressionClosure rval) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    Preconditions.checkArgument( lval.getInputType().equals( stateType ));
    Preconditions.checkArgument( rval.getInputType().equals( stateType ));
    
    return suspendBool(forceBool(path, statePrime).and(
        state.eq(getExpressionEncoder().getMemoryModel().assign(statePrime,
            lval.eval(statePrime), rval.eval(statePrime)))).exists(statePrime));
  }  
  
  @Override
  public FunctionExpression assume(Expression pre,
      ExpressionClosure bool) {
    Preconditions.checkArgument( pre.getType().equals( pathType ) );
    Preconditions.checkArgument( bool.getInputType().equals( stateType ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    Expression result = bool.eval(state);

    return suspendBool( forceBool(pre,state).and( result ));
  }
  
  @Override
  public FunctionExpression check(Expression pre, ExpressionClosure expr) {
    Preconditions.checkArgument( pre.getType().equals( pathType ) );
    return suspendBool( forceBool(pre,state));
  }
  
  @Override
  public FunctionExpression emptyPath()  {
    return suspendBool(getExpressionEncoder().getMemoryModel().initialState()
        .eq(state));
  }

  /* pre should be of pathType, m should be of stateType */
  private BooleanExpression forceBool(Expression pre, Expression m) {
    
/*    Preconditions.checkArgument(pre.getArity() == 1);
    Preconditions.checkArgument(pre.getArgTypes().get(0).equals(m.getType()));
    Preconditions.checkArgument(pre.getRange().isBoolean());
*/
    
    return pre.asFunctionExpression().apply(m).asBooleanExpression();
  }

  @Override
  public BooleanExpression pathToBoolean(Expression path) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    return forceBool(path, state);
  }

  /* expr should be a Boolean */
  private FunctionExpression suspendBool(Expression expr) {
    return expr.lambda(state);
  }

  @Override
  public FunctionType getPathType() {
    return pathType;
  }
  
  @Override
  public Expression alloc(Expression pre, ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("alloc");
  }
  
  @Override
  public Expression declareStruct(Expression pre, ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("declareStruct");
  }
  
  @Override
  public Expression declareArray(Expression pre, ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("declareArray");
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("free");
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval, String field,
      ExpressionClosure rval) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("fieldAssign");
  }
  
  @Override
  public Expression havoc(Expression path, ExpressionClosure lval) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    Preconditions.checkArgument( lval.getInputType().equals( stateType ));
    
    return suspendBool(forceBool(path, statePrime).and(
        state.eq(getExpressionEncoder().getMemoryModel().havoc(statePrime,
            lval.eval(statePrime)))).exists(statePrime));
  }

  @Override
  public Expression noop(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    // TODO Auto-generated method stub
    return null;
  }
}
