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
 * Lambda partition memory model, multiple memory arrays for various 
 * alias groups.
 * 
 * The state of memory is a record with multiple arrays for various 
 * types. 
 * 
 * 
 * @author Wei
 *
 */
public class LambdaPartitionMemoryModel<T> extends AbstractLambdaMemoryModel<T> {

  public static <T> LambdaPartitionMemoryModel<T> create(
      StateFactory<T> stateFactory)
      throws ExpressionFactoryException {
    return new LambdaPartitionMemoryModel<T>(stateFactory);
  }
  
  private final Type addrType, sizeType;

  private LambdaPartitionMemoryModel(StateFactory<T> stateFactory) {
    super(stateFactory);
  	IRDataFormatter formatter = getDataFormatter();
    addrType = formatter.getAddressType();
    sizeType = formatter.getSizeType();
  }
  
  @Override
  public StateExpression alloc(StateExpression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    StateFactory<T> stateFactory = getStateFactory();
    size = getExpressionEncoding().castToInteger(size, sizeType.asBitVectorType().getSize());
    StateExpression resState = stateFactory.alloc(state, ptr, size);
    return resState;
  }

  @Override
	public StateExpression free(StateExpression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZro = getDataFormatter().getSizeZero();
    return getStateFactory().updateSizeState(state, ptr, sizeZro);
	}

	@Override
	public StateExpression assign(StateExpression state, Expression lval, Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));    
    return getStateFactory().updateMemState(state, lval, rval);
	}

	@Override
	public Expression deref(StateExpression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    return getStateFactory().deref(state, p);
	}

	@Override
	public StateExpression havoc(StateExpression state, Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    
    Expression rval = getDataFormatter().getUnknownValue(CType.getType(lval.getNode()));
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
  	return getStateFactory().applyValidFree(state, ptr).asBooleanExpression();
  }

	@Override
  public StateExpression declare(StateExpression state, Expression lval, IRVarInfo info) {
	  return getStateFactory().addStackVar(state, lval, info);
  }
}
