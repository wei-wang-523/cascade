package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Type;

public class SimpleMemoryModel extends AbstractMemoryModel {
  private static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  private static final String DEFAULT_MEMORY_STATE_NAME = "memoryState";
  
  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param size the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static SimpleMemoryModel create(
      ExpressionEncoding encoding,
      int size)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    BitVectorType cellType = exprManager.bitVectorType(size);

    return new SimpleMemoryModel(encoding, cellType);
  }
  
  protected final BitVectorType cellType;
  
  /** when allocate a region_x in stack of array or structure, we just 
   * let addr_of_array == region_x, or addr_of_struct == region_x, 
   * which models exactly what happened in C. It means we should remove 
   * addr_of_array or addr_of_struct from arrays, otherwise when do 
   * --sound-alloc or --order-alloc, we will call getAssumptions(), which
   * ensures that addr_of_array/addr_of_struct < region_x or addr_of_array
   * /addr_of_strcut != region_x, and it's conflict with the above equality.
   * Here, we keep rvals to record those removed addr_of_struct and addr_of_array,
   * and remove them from arrays in getAssumptions().
   */
  protected final Map<String, ArrayExpression> newElems;
  protected final Map<String, ArrayExpression> lvals;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;
  private final Expression memVar;
  
  protected SimpleMemoryModel(ExpressionEncoding encoding, BitVectorType cellType) {
    super(encoding);
    IntegerEncoding<?> integerEncoding = encoding.getIntegerEncoding();
    Preconditions.checkArgument(integerEncoding.getType().equals(cellType));
    this.cellType = cellType;

    newElems = Maps.newLinkedHashMap();
    lvals = Maps.newHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    Type statePrimeType = exprManager.recordType(DEFAULT_MEMORY_STATE_NAME, elemNames, elemTypes);
    memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, statePrimeType, true);
  }
  
  @Override
  public Expression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.isRecord());
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();    
    String lvalName = lval.asVariable().getName().substring(8);
    
    /* Check is newElems is non-empty, update the state type by adding new fields */
    RecordExpression stateRecord = state.asRecord();
    List<Expression> elems = Lists.newArrayList(stateRecord.getChildren());
    List<String> elemNames = Lists.newArrayList(stateRecord.getType().getElementNames());
    
    assert(elems.size() == elemNames.size());
    
    /* Update the array of lval either in state or in newElems */
    if(elemNames.contains(lvalName)) { // previously declared variable
      int index = elemNames.indexOf(lvalName);
      Expression lvalArr = elems.get(index);
      Expression lvalIdx = lvalArr.getType().asArrayType().getIndexType().asInductive()
          .getConstructors().iterator().next().apply();
      Expression lvalArrPrime = lvalArr.asArray().update(lvalIdx, rval);
      elems.set(index, lvalArrPrime);
    } else { // newly declared variable
      ArrayExpression lvalArr = newElems.containsKey(lvalName) ? newElems.get(lvalName) :
          lvals.get(lvalName);
      Expression lvalIdx = lvalArr.getType().asArrayType().getIndexType().asInductive()
          .getConstructors().iterator().next().apply();
      ArrayExpression lvalArrPrime = lvalArr.asArray().update(lvalIdx, rval);
      newElems.put(lvalName, lvalArrPrime);
    }
    
    boolean changed = false;    
    for(Entry<String, ArrayExpression> entry : newElems.entrySet()) {
      if(elemNames.contains(entry.getKey()))  
        continue;
      elemNames.add(entry.getKey());
      elems.add(entry.getValue());
      changed = true;
    }
    
    Type statePrimeType = state.getType();
    if(changed) {
      /* Compose the new record of new state */
      Iterable<Type> elemTypes = Iterables.transform(elems, new Function<Expression, Type>(){
        @Override
        public Type apply(Expression expr) {
          return expr.getType();
        }
      });
      statePrimeType = exprManager.recordType(DEFAULT_MEMORY_STATE_NAME, elemNames, elemTypes);
    }
    
    Expression statePrime = exprManager.record(statePrimeType, elems);
    newElems.clear();
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.isRecord());
    String pName = p.asVariable().getName().substring(8);
    
    /* Check is newElems is non-empty, update the state type by adding new fields */
//    RecordExpression stateRecord = state.asRecord();
//    List<String> elemNames = Lists.newArrayList(stateRecord.getType().getElementNames());
    
    Expression res = null;
    
    /* Deref the array of p either in state or in newElems */
//    if(elemNames.contains(pName)) { // previously declared variable
//      Expression pArr = state.asRecord().select(pName);
//      Expression pIdx = pArr.getType().asArrayType().getIndexType().asInductive()
//          .getConstructors().iterator().next().apply();
//      res = pArr.asArray().index(pIdx);
//    } else { // newly declared variable
    
    ArrayExpression pArr = null;
    
    if(!newElems.containsKey(pName))  {
      pArr = lvals.get(pName);
      newElems.put(pName, pArr);
    } else {
      pArr = newElems.get(pName);
    }
    
    Expression pIdx = pArr.getType().asArrayType().getIndexType().asInductive()
        .getConstructors().iterator().next().apply();
    
    res = pArr.asArray().index(pIdx);
//    }
    
    return res;
  }
  
  @Override
  public void addLval(VariableExpression var) {
    ExpressionManager exprManager = getExpressionManager(); 
    
    String varName = var.getName().substring(8);
    Constructor cons = exprManager.constructor("mk_" + varName);
    InductiveType idxType = exprManager.dataType("idx_" + varName, cons);
    // FIXME: cellType is bv(k), k should be dynamic not static
    ArrayExpression varArray = exprManager.
        arrayVar("arr_of_" + varName, idxType, cellType, true).asArray();
    lvals.put(varName, varArray);
  }
  
  @Override
  public Expression freshState() {
    return memVar;
  }
  
  @Override
  public ArrayType getMemoryType() {
    // TODO Auto-generated method stub
    return null;
  }
  
  @Override
  public Type getStateType() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(memoryVar.isRecord());
    Preconditions.checkArgument(!(expr.isTuple()));

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
//        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
        /*  */
        Iterable<String> elemNames = memory.asRecord().getType().getElementNames();
        Iterable<Expression> oldExprs = Iterables.transform(elemNames, new Function<String, Expression>(){
          @Override
          public Expression apply(String elemName) {
            return lvals.get(elemName);
          }
        });
        Iterable<? extends Expression> newExprs = memory.asRecord().getChildren();
        return expr.subst(oldExprs, newExprs);        
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
    };
  }
  
  @Override
  public ExpressionClosure getCurrentState() {
    return currentState;
  }
  
  public Expression updateState(Expression state) {
    if(newElems.isEmpty())  return state;
    
    ExpressionManager exprManager = getExpressionManager();
    RecordExpression stateRecord = state.asRecord();
    List<Expression> elems = Lists.newArrayList(stateRecord.getChildren());
    List<String> elemNames = Lists.newArrayList(stateRecord.getType().getElementNames());
    
    for(Entry<String, ArrayExpression> entry : newElems.entrySet()) {
      if(elemNames.contains(entry.getKey()))  
        continue;
      elemNames.add(entry.getKey());
      elems.add(entry.getValue());
    }
    /* Compose the new record of new state */
    Iterable<Type> elemTypes = Iterables.transform(elems, new Function<Expression, Type>(){
      @Override
      public Type apply(Expression expr) {
        return expr.getType();
      }
    });
    Type statePrimeType = exprManager.recordType(DEFAULT_MEMORY_STATE_NAME, elemNames, elemTypes);
    Expression statePrime = exprManager.record(statePrimeType, elems);
    newElems.clear();
    return statePrime;
  }
  
  @Override
  public void resetCurrentState() {
    currentState = null;
  }
  
  protected void setCurrentState(Expression state) {
    // TODO Auto-generated method stub
    return;
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression alloc(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareStruct(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareArray(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression free(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression havoc(Expression state, Expression lval) {
    // TODO Auto-generated method stub
    return null;
  }
}
