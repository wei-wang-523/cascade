package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
 */

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.TupleType;
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
  public Expression declareStruct(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().declareStruct(mem, ptr.eval(mem), size.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression declareArray(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().declareArray(mem, ptr.eval(mem), size.eval(mem));
    
    return getExpressionManager().tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure ptr) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().free(mem, ptr.eval(mem));
    
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
  
  private Expression getITEExpression(Iterable<? extends Expression> exprs, 
      Iterable<? extends Expression> guards) {
    Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(guards));
    ExpressionManager exprManager = getExpressionManager();
    Expression resExpr = null;
    // have first case as default case
    for(int i = 1; i < Iterables.size(guards); i++) {
      BooleanExpression guard = Iterables.get(guards, i).asBooleanExpression();
      if(i == 1) {
        Expression case_0 = Iterables.get(exprs, 0);
        Expression case_1 = Iterables.get(exprs, 1);
        resExpr = exprManager.ifThenElse(guard, case_1, case_0);
      } else {
        Expression case_1 = Iterables.get(exprs, i);
        resExpr = exprManager.ifThenElse(guard, case_1, resExpr);
      }
    }
    return resExpr;
  }

  @Override
  public Expression noop(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    Preconditions.checkArgument(Iterables.size(prefixes) == Iterables.size(preGuards));
    ExpressionManager exprManager = getExpressionManager();
    
    
    Expression resMemState = null;
    if(getMemoryModel().getStateType().isTuple()) {
      TupleType tupleType = getMemoryModel().getStateType().asTuple();
      int size = tupleType.getElementTypes().size();
      List<Expression> stateElem = Lists.newArrayListWithCapacity(size);
      for(int i = 0; i < size; i++) {
        List<Expression> mem = Lists.newArrayList();
        for(Expression prefix : prefixes) {
          mem.add(prefix.asTuple().getChild(0).asTuple().getChild(i));   
        }
        stateElem.add(getITEExpression(mem, preGuards));
      }
      resMemState = exprManager.tuple(getMemoryModel().getStateType(), stateElem);
    } else {
      List<Expression> mem = Lists.newArrayList();
      for(Expression prefix : prefixes) {
        mem.add(prefix.asTuple().getChild(0));
      }
      resMemState = getITEExpression(mem, preGuards);
    }
    
    List<Expression> pc = Lists.newArrayList();
    for(Expression prefix : prefixes) {
      pc.add(prefix.asTuple().getChild(1));
    }
    Expression resPC = getITEExpression(pc, preGuards); 
    
    return exprManager.tuple(getPathType(), resMemState, resPC);
  }
}
