package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using lambda expressions.
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
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;

public class LambdaPathEncoding extends AbstractPathEncoding {
  public static <Mem extends Expression> LambdaPathEncoding create(
      ExpressionEncoder encoder) {
    return new LambdaPathEncoding(encoder);
  }
  
  private static final String VALUE_SELECTOR_NAME = "val";
  private static final String BOTTOM_CONSTRUCTOR_NAME = "bottom";
  private static final String OK_CONSTRUCTOR_NAME = "ok";
  private static final String STATE_VARIABLE_NAME = "q";
  
  private final VariableExpression state; //, memoryPrime;
  private final Expression stateVal;
  
  private final Selector valueSelector;
  private final Constructor okConstructor;
  private final Constructor bottomConstructor;
  private Expression bottom;
  private BooleanExpression stateIsOk;
  private final InductiveType pathType;
  private final Type stateType;
  
  private LambdaPathEncoding(ExpressionEncoder encoder) {
    super(encoder);

    ExpressionManager exprManager = getExpressionManager();

    stateType = getExpressionEncoder().getMemoryModel().getStateType();
    valueSelector = exprManager.selector(VALUE_SELECTOR_NAME, stateType);

    okConstructor = exprManager.constructor(OK_CONSTRUCTOR_NAME, valueSelector);
    bottomConstructor = exprManager.constructor(BOTTOM_CONSTRUCTOR_NAME);

    pathType = exprManager.dataType("state", okConstructor,
        bottomConstructor);

    /* The current state, of the above datatype, bound by a lambda for each path */
    state = pathType.variable(STATE_VARIABLE_NAME, false);
    stateIsOk = exprManager.testConstructor(okConstructor, state);

    /*
     * The actual state value, selected from an "ok" state of type "memory".
     * Should be guarded by calls to isOk.
     */
    stateVal = exprManager.select(valueSelector, state);

    /* Bottom, for infeasible paths. */
    bottom = exprManager.construct(bottomConstructor);
  }
  
  /**
   * The assignment <code>x:=E</code> along path P results in:
   * <code>if is_ok(P) then ok(〚x:=E〛(val(P))) else bottom</code>
   * @throws ExpressionFactoryException 
   */

  @Override
  public Expression assign(Expression pre,
      ExpressionClosure var, ExpressionClosure val) {
    return extendPath(
        pre,
        stateIsOk.ifThenElse(
            mkOk(getMemoryModel().assign(stateVal, var.eval(stateVal),
                val.eval(stateVal))), bottom));
  }
  

  /**
   * Adding the assumption E to path P results in:
   * <code>if is_ok(P) => 〚E〛(val(P)) then P else bottom</code>
   * @throws ExpressionFactoryException 
   */

  @Override
  public Expression assume(Expression pre,
      ExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    
    Preconditions.checkArgument( pre.getType().equals( pathType ) );
    Preconditions.checkArgument( expr.getInputType().equals( stateType ));
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));
   
    BooleanExpression result = getExpressionEncoding().toBoolean(
        expr.eval(stateVal));
    
    return extendPath(pre, stateIsOk.and(result).ifThenElse(state, bottom));
  }

  @Override
  public Expression assumeMemorySafe(Expression pre) {
    Preconditions.checkArgument( pre.getType().equals( pathType ) );
   
    BooleanExpression result = getExpressionManager().and(getMemoryModel().getAssumptions(pre));
    
    return extendPath(pre, stateIsOk.and(result).ifThenElse(state, bottom));
  }
  
  /**
   * A path P is feasible iff. <code>is_ok(P)</code> is satisfiable.
   * @throws ExpressionFactoryException 
   */

  @Override
  public BooleanExpression pathToBoolean(Expression path) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    return evalWithPath(path,stateIsOk).asBooleanExpression();
  }
  
  public Expression addAssumptions(BooleanExpression expr)
      throws PathFactoryException {
    try {
      ExpressionEncoding encoding = getExpressionEncoding();
      ExpressionManager exprManager = encoding.getExpressionManager();
      return exprManager.implies(exprManager.and(encoding.getAssumptions()),
          expr);
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    } catch (ExpressionFactoryException e) {
      throw new PathFactoryException(e);
    }
  }
  /**
   * The assertion E holds along path P iff.
   * <code>is_ok(P) ⇒ 〚E〛(val(P))</code>
   * 
   * @throws ExpressionFactoryException
   */
  @Override
  protected BooleanExpression assertionToBoolean(Expression path,
      ExpressionClosure bool) {
    Preconditions.checkArgument( path.getType().equals( pathType ) );
    Preconditions.checkArgument( bool.getInputType().equals( stateType ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    Expression result = bool.eval(stateVal);

    return evalWithPath(path, stateIsOk.implies(result)).asBooleanExpression();
  }  

  @Override
  public Expression emptyPath() {
    Expression innerState = getMemoryModel().initialState();
    Expression startState = okConstructor.apply(innerState);
    return startState;
  }

  /**
   * Evaluate post(P), where post is a path expression with a free variable for
   * the pre-state.
   */
  Expression extendPath(Expression pre, Expression newState) {
    return evalWithPath(pre,newState);
  }


  /*
   * Evaluate an expression E with a free path variable s wrt. the path P via:
   * <code>(λs.E) P</code>. The returned expression will have the same type as
   * <code>expr</code>
   * 
   * In the implementation, the free variable in E will be the variable defined
   * by the field <code>state</code>.
   */
  private Expression evalWithPath(Expression pre, Expression expr) {
    return expr.lambda(state).apply(pre);
  }

  private Expression mkOk(Expression stateValue) {
    return okConstructor.apply(stateValue);
  }

  @Override
  public InductiveType getPathType() {
    return pathType;
  }
  
  @Override
  public Expression alloc(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("alloc");
  }
  
  @Override
  public Expression declareStruct(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("allocStack");
  }
  
  @Override
  public Expression declareArray(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("allocStack");
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("free");
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval, 
      String field, ExpressionClosure rval) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("fieldAssign");
  }
  
  @Override
  public Expression havoc(Expression pre, ExpressionClosure lval) {
	  return extendPath(
		        pre,
		        stateIsOk.ifThenElse(
		            mkOk(getMemoryModel().havoc(stateVal, lval.eval(stateVal))), bottom));
  }

  @Override
  public Expression assume(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure bool) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression assumeMemorySafe(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression assign(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure lval,
      ExpressionClosure rval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression fieldAssign(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure lval,
      String field, ExpressionClosure rval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression alloc(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareArray(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareStruct(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure ptr,
      ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression free(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression havoc(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards, ExpressionClosure lval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression noop(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    // TODO Auto-generated method stub
    return null;
  }
}
