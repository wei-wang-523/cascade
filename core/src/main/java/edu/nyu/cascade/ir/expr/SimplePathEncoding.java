package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
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
//  private Expression assumps;
  
  private SimplePathEncoding(ExpressionEncoder encoder) {
    super(encoder);
    stateVal = null;
    Type memType = getExpressionEncoder().getMemoryModel().getStateType();
    Type pcType = getExpressionManager().booleanType();
    stateType = getExpressionManager().tupleType("pathState", memType, pcType);
  }

  @Override
  public Expression assign(Expression pre,
      ExpressionClosure var, ExpressionClosure val) {
    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().assign(mem, var.eval(mem), val.eval(mem));
    
    return exprManager.tuple(stateType, memPrime, pc);
  }

  @Override
  public Expression assume(Expression pre,
      ExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    Preconditions.checkArgument( expr.getInputType().equals( 
        stateType.asTuple().getElementTypes().get(0) ));
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));

    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = mem;
    ExpressionClosure currentState = getMemoryModel().getCurrentState();
    if(currentState != null) memPrime = currentState.eval(mem);
    getMemoryModel().resetCurrentState();
    
    Expression pcPrime = exprManager.ifThenElse(pc, expr.eval(mem).asBooleanExpression(), 
        exprManager.ff());
    
    return exprManager.tuple(stateType, memPrime, pcPrime);
  }
  
  @Override
  public Expression assumeMemorySafe(Expression pre) {
    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memAssume = exprManager.and(getMemoryModel().getAssumptions(mem));
    Expression pcPrime = exprManager.ifThenElse(pc, memAssume, exprManager.ff());
    
    return exprManager.tuple(stateType, mem, pcPrime);
  }

  @Override
  protected BooleanExpression assertionToBoolean(Expression pre,
      ExpressionClosure bool) {
    Preconditions.checkArgument( bool.getInputType().equals( 
        stateType.asTuple().getElementTypes().get(0) ));
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    return getExpressionManager().implies(pc, bool.eval(mem));
  }

  @Override
  public Expression emptyPath() {
    Expression memState = getMemoryModel().initialState();
    Expression pcState = getExpressionManager().tt();
    stateVal = getExpressionManager().tuple(stateType, memState, pcState);
    return stateVal;
  }

  @Override
  public Type getPathType() {
    return stateType;
  }

  @Override
  protected BooleanExpression pathToBoolean(Expression pre) {
    Expression pc = pre.asTuple().getChild(1);
    return pc.asBooleanExpression();
  }
  
  @Override
  public Expression alloc(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().alloc(mem, lval.eval(mem), rval.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression declareStruct(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().declareStruct(mem, lval.eval(mem), rval.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression declareArray(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().declareArray(mem, lval.eval(mem), rval.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure var) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().free(mem, var.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval,
      String field, ExpressionClosure rval) {
    ExpressionManager exprManager =  getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression pcPrime = pc;
    if(getMemoryModel() instanceof ReachMemoryModel) {
      ReachMemoryModel mm = (ReachMemoryModel) getMemoryModel();
      Expression memAssume = mm.fieldAssign(mem, lval.eval(mem), field, rval.eval(mem));
      pcPrime = exprManager.ifThenElse(pc, memAssume, exprManager.ff());
    }
    
    return exprManager.tuple(stateType, mem, pcPrime);
  }
  
  @Override
  public Expression havoc(Expression pre, ExpressionClosure lval) {
    ExpressionManager exprManager =  getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().havoc(mem, lval.eval(mem));
    return exprManager.tuple(stateType, memPrime, pc);
  }

  @Override
  public Expression assume(Iterable<? extends Expression> prefixes,
      ExpressionClosure bool) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression assumeMemorySafe(Iterable<? extends Expression> prefixes) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression assign(Iterable<? extends Expression> prefixes,
      ExpressionClosure lval, ExpressionClosure rval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression fieldAssign(Iterable<? extends Expression> prefixes,
      ExpressionClosure lval, String field, ExpressionClosure rval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression alloc(Iterable<? extends Expression> prefixes,
      ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareArray(Iterable<? extends Expression> prefixes,
      ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareStruct(Iterable<? extends Expression> prefixes,
      ExpressionClosure ptr, ExpressionClosure size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression free(Iterable<? extends Expression> prefixes,
      ExpressionClosure ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression havoc(Iterable<? extends Expression> prefixes,
      ExpressionClosure lval) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression noop(Iterable<? extends Expression> prefixes) {
    // TODO Auto-generated method stub
    return null;
  }
}
