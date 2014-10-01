package edu.nyu.cascade.ir.memory.model;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

/**
 * Monolithic memory mode, with a flat memory array. The array type
 * maps pointer type to cell type, where cell type is union of pointer 
 * type and scalar type.
 *  
 * @author Wei
 *
 */
public class LambdaFlatMemoryModel<T> extends AbstractLambdaMemoryModel<T> {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static <T> LambdaFlatMemoryModel<T> create(StateFactory<T> stateFactory)
      throws ExpressionFactoryException {
    return new LambdaFlatMemoryModel<T>(stateFactory);
  }

  private final Type addrType, sizeType;

  private LambdaFlatMemoryModel(StateFactory<T> stateFactory) {
  	super(stateFactory);
  	IRDataFormatter formatter = getDataFormatter();
    addrType = formatter.getAddressType();
    sizeType = formatter.getSizeType();
  }
  
  @Override
  public StateExpression alloc(StateExpression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
		size = getExpressionEncoding().castToInteger(size, sizeType.asBitVectorType().getSize());
    return getStateFactory().alloc(state, ptr, size);
  }
  
  @Override
  public StateExpression free(StateExpression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType )); 
  	IRDataFormatter formatter = getDataFormatter();
    Expression sizeZro = formatter.getSizeZero();
    return getStateFactory().updateSizeState(state, ptr, sizeZro);
  }

  @Override
  public StateExpression assign(
  		StateExpression state, Expression lval, Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));    
    return getStateFactory().updateMemState(state, lval, rval);
  }

  @Override
  public Expression deref(StateExpression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    return getStateFactory().deref(state, p);
  }
  
  @Override
  public StateExpression havoc(
  		StateExpression state, Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    IRDataFormatter formatter = getDataFormatter();
    Expression rval = formatter.getUnknownValue(CType.getType(lval.getNode()));
    return getStateFactory().updateMemState(state, lval, rval);
  }
  
  @Override
  public Expression createLval(String name) {
  	IRDataFormatter formatter = getDataFormatter();
    return formatter.getFreshPtr(name, true);
  }

  @Override
  public StateExpressionClosure suspend(final StateExpression stateVar, final Expression expr) {
    return new StateExpressionClosure() {
      @Override
      public Expression eval(final StateExpression preState) {
        Preconditions.checkArgument(preState.hasSameType(stateVar));
        StateFactory<T> stateFactory = getStateFactory();
        stateFactory.propagateNewInfo(stateVar, preState);
        Expression exprPrime = stateFactory.eval(expr, stateVar, preState);
        return exprPrime.setNode(expr.getNode());
      }

      @Override
      public Type getOutputType() {
        return expr.getType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return expr.getExpressionManager();
      }
      
			@Override
      public Expression getOutput() {
	      return expr;
      }
    };
  }
  
  @Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType ));
    return getStateFactory().validAccess(state, ptr).asBooleanExpression();
  }
  
  @Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    size = getExpressionEncoding().castToInteger(size, sizeType.asBitVectorType().getSize());
    return getStateFactory().validAccessRange(state, ptr, size).asBooleanExpression();
  }
  
  @Override
  public BooleanExpression validMalloc(StateExpression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    size = getExpressionEncoding().castToInteger(size, sizeType.asBitVectorType().getSize());
    return getStateFactory().applyValidMalloc(state, ptr, size).asBooleanExpression();
  }
  
  @Override
  public BooleanExpression validFree(StateExpression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType ));
  	return getStateFactory().applyValidFree(state, ptr);
  }

	@Override
  public StateExpression declare(StateExpression state, Expression lval, IRVarInfo info) {
	  return getStateFactory().addStackVar(state, lval, info);
  }
}