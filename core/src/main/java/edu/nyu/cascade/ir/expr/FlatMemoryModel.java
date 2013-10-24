package edu.nyu.cascade.ir.expr;

import java.util.Collection;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

/**
 * Monolithic memory mode, with a flat memory array. The array type
 * maps pointer type to cell type, where cell type is union of pointer 
 * type and scalar type.
 *  
 * @author Wei
 *
 */
public class FlatMemoryModel extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static FlatMemoryModel create(ExpressionEncoding encoding, 
  		IRSingleHeapEncoder heapEncoder)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new FlatMemoryModel(encoding, heapEncoder);
  }

  private final Type addrType, valueType;
  private final ArrayType memType, sizeArrType;
  private final TupleType stateType;
  
  private final IRSingleHeapEncoder heapEncoder;
  
  private ExpressionClosure sideEffectMemClosure = null;
  private ExpressionClosure sideEffectSizeClosure = null;

  private FlatMemoryModel(ExpressionEncoding encoding, IRSingleHeapEncoder heapEncoder) {
  	super(encoding);
  	
    this.heapEncoder = heapEncoder;    
    valueType = heapEncoder.getValueType();
    addrType = heapEncoder.getAddressType();
    
    ExpressionManager exprManager = getExpressionManager();
    
    memType = heapEncoder.getMemoryType();
    sizeArrType = heapEncoder.getSizeArrType();
    stateType = exprManager.tupleType(
    		Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    CType.unwrapped(CType.getType(ptr.getNode())).toPointer().getType().mark(regionNode);
    String regionScope = CType.getScopeName(ptr.getNode());
    regionNode.setProperty(CType.SCOPE, regionScope);
    
    Expression region = heapEncoder.freshRegion(regionName, regionNode);
    
    ArrayExpression memory = heapEncoder.updateMemArr(state.getChild(0).asArray(), ptr, region);
    ArrayExpression sizeArr = heapEncoder.updateSizeArr(state.getChild(1).asArray(), region, size);
    return getUpdatedState(state, memory, sizeArr);
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    ArrayExpression sizeArr = heapEncoder.updateSizeArr(state.getChild(1).asArray(), ptr, size);
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    ArrayExpression sizeArr = heapEncoder.updateSizeArr(state.getChild(1).asArray(), ptr, size);
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZro = heapEncoder.getValueZero();
    Expression sizeArr = heapEncoder.updateSizeArr(state.getChild(1).asArray(), ptr, sizeZro);
    
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Preconditions.checkArgument(rval.getType().equals( valueType )
    		|| rval.getType().equals( addrType ));
    
    Expression memory = heapEncoder.updateMemArr(state.getChild(0).asArray(), lval, rval);
    return getUpdatedState(state, memory, state.getChild(1));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    return heapEncoder.indexMemArr(getMemory(state), p);
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    
    Expression rval = heapEncoder.getUnknownValue(CType.getType(lval.getNode()));
    ArrayExpression memory = heapEncoder.updateMemArr(state.getChild(0).asArray(), lval, rval);
    return getUpdatedState(state, memory, state.getChild(1));
  }
  
  @Override
  public Expression createLval(Expression memory, String name, IRVarInfo info, Node node) {
    Expression res = heapEncoder.freshAddress(name, info, CType.unwrapped(CType.getType(node)));
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    CType.unwrapped(CType.getType(ptr.getNode())).toPointer().getType().mark(regionNode);
    regionNode.setProperty(CType.SCOPE, CType.getScopeName(ptr.getNode()));

    Expression region = heapEncoder.freshRegion(regionName, regionNode);
    ArrayExpression mem = heapEncoder.updateMemArr(getMemory(state), ptr, region);
    ArrayExpression sizeArr = heapEncoder.updateSizeArr(getSizeArr(state), region, size);
    
    sideEffectMemClosure = suspend(state, mem);
    sideEffectSizeClosure = suspend(state, sizeArr);
    return heapEncoder.validMalloc(sizeArr, region, size);
  }
  
  @Override
	public Expression addressOf(Expression content) {
  	return heapEncoder.addressOf(content);
	}

	@Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
		return heapEncoder.disjointMemLayout(state.getChild(1).asArray());
  }

  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression sizeArrVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        sizeArrType, true);
    return exprManager.tuple(stateType, memVar, sizeArrVar);
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  @Override
  public boolean setStateType(Type stateType) {
  	Preconditions.checkArgument(this.stateType.equals(stateType));
  	return false;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        Preconditions.checkArgument(!isState(expr));
        // For non-tuple expression evaluation
        Expression exprPrime = expr
        		.subst(memoryVar.getChildren(), memory.getChildren());
        return exprPrime.setNode(expr.getNode());
      }

      @Override
      public Type getOutputType() {
        return expr.getType();
      }

      @Override
      public Type getInputType() {
        return memoryVar.getType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return expr.getExpressionManager();
      }
      
      private boolean isState(Expression expr) {
        return expr.getType().isTuple() 
            && expr.getType().asTuple().getName().startsWith(DEFAULT_STATE_TYPE);
      }
    };
  }
  
  @Override
  public boolean hasSideEffect() {
    return sideEffectMemClosure != null || sideEffectSizeClosure != null;
  }
  
  @Override
  public Expression clearSideEffect(Expression state) {
  	Preconditions.checkArgument(state.isTuple());
  	Expression mem = state.getChild(0);
  	Expression size = state.getChild(1);
  	
  	Expression memPrime = mem;
  	
  	if(sideEffectMemClosure != null) {
  		memPrime = sideEffectMemClosure.eval(state);
  	}
  	
  	Expression sizePrime = size;
  	if(sideEffectSizeClosure != null) {
  		sizePrime = sideEffectSizeClosure.eval(state);
  	}
  	
  	return getUpdatedState(state, memPrime, sizePrime);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType ));
    
    Collection<BooleanExpression> res = heapEncoder
    		.validMemAccess(state.getChild(1).asArray(), ptr);
    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Collection<BooleanExpression> res = heapEncoder
    		.validMemAccess(state.getChild(1).asArray(), ptr, size);
    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    BooleanExpression res = heapEncoder.validMalloc(state.getChild(1).asArray(), ptr, size);
    return res;
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType ));
  	return heapEncoder.validFree(state.getChild(1).asArray(), ptr);
  }
  
  @Override
  public Expression substSizeArr(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialSizeArr = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, sizeArrType, false);
    Expression constSizeArr = heapEncoder.getConstSizeArr(sizeArrType);
    Expression res = expr.subst(initialSizeArr, constSizeArr);
    return res;
  }
	
	private ArrayExpression getMemory(Expression state) {
		if(sideEffectMemClosure != null) { 
			return sideEffectMemClosure.eval(state).asArray();   	
		}	else {
			return state.getChild(0).asArray();
		}
	}
	
	private ArrayExpression getSizeArr(Expression state) {
		if(sideEffectSizeClosure != null) { 
			return sideEffectSizeClosure.eval(state).asArray();   	
		}	else {
			return state.getChild(1).asArray();
		}
	}

	@Override
  public void setPreProcessor(PreProcessor<?> analyzer) {
		throw new UnsupportedOperationException("No pre processor is needed for flat memory model");
  }
}
