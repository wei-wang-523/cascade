package edu.nyu.cascade.ir.expr.bak;

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.bak.AbstractMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

public class BitVectorMemoryModelOrder extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static BitVectorMemoryModelOrder create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    
    BitVectorType addressType = exprManager.bitVectorType(size);
    BitVectorType cellType = exprManager.bitVectorType(size);

    ArrayType memArrayType = exprManager.arrayType(addressType, cellType);

    return new BitVectorMemoryModelOrder(encoding, memArrayType);
  }
  
  /** Create an expression factory with the given array type to model memory. The size of the 
   * index type of the memory array (i.e., the size of a pointer) must be a multiple of the size
   * of the element type (i.e., the size of a memory word).
   * @param exprManager
   * @param addressSize
   *          the desired size of a pointer
   * @param cellSize
   *          the desired size of a memory word (i.e., the unit of a pointer
   *          "step")
   * 
   * @throws IllegalArgumentException
   *           if <code>addressSize</code> is not a multiple of
   *           <code>cellSize</code>
   */
  public static BitVectorMemoryModelOrder create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(memArrayType.getIndexType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getElementType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getIndexType().asBitVectorType().getSize()
        % memArrayType.getElementType().asBitVectorType().getSize() == 0);
      return new BitVectorMemoryModelOrder(encoding,
          memArrayType);
  }

  public static BitVectorMemoryModelOrder create(
      ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException
  {
    return create(encoding, memArray.getType());
  }

  protected final BitVectorType addressType;
  protected final BitVectorType cellType;
  protected final ArrayType memType;
  protected final TupleType stateType;
  protected final Set<Expression> lvals; // variables in stack
  protected final List<Expression> heapRegions, stackRegions;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;

  protected BitVectorMemoryModelOrder(ExpressionEncoding encoding, ArrayType memType) {
    super(encoding);
    
    IntegerEncoding<?> integerEncoding = encoding.getIntegerEncoding();
    Preconditions.checkArgument(integerEncoding.getType().equals( memType.getIndexType() ));
  
    this.lvals = Sets.newHashSet();
    this.heapRegions = Lists.newArrayList();
    this.stackRegions = Lists.newArrayList();

    this.memType = memType;
    stateType = getExpressionManager().tupleType(DEFAULT_STATE_TYPE, memType, memType);
    addressType = memType.getIndexType().asBitVectorType();
    cellType = memType.getElementType().asBitVectorType();
  }  
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, 
        addressType, true);
    
    heapRegions.add(locVar); // For dynamic memory allocation, add to the end of regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(locVar, size);
    return exprManager.tuple(stateType, memory, alloc, state.getChild(2));
  }
  
  @Override
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    // FIXME: assume size != 0
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return getExpressionManager().tuple(
        stateType, state.getChild(0), alloc, state.getChild(2));
  }
  
  @Override
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    stackRegions.add(ptr);
    // FIXME: assume size != 0
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return getExpressionManager().tuple(
        stateType, state.getChild(0), alloc, state.getChild(2));
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {     
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(heapRegions.size() + lvals.size());
    
    try {
      Expression alloc = state.getChild(1);
      
      // In any stack variable
      Set<Expression> lvals_copy = Sets.newHashSet(lvals);
      lvals_copy.removeAll(stackRegions);
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */  
      for( Expression lval : lvals_copy)    disjs.add(ptr.eq(lval));
      
      // In any stack region
      for(Expression region : stackRegions) {
        Expression regionSize = alloc.asArray().index(region);
        
        BitVectorExpression regionBound = exprManager.plus(addressType
            .getSize(), region, regionSize);
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
      
      // In any heap region
      for( Expression region : heapRegions ) {
        Expression regionSize = alloc.asArray().index(region);
        Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
        Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
        
        BitVectorExpression regionBound = exprManager.plus(addressType
            .getSize(), region, regionSize);
        disjs.add(
            exprManager.and(
                region.neq(nullPtr),
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return exprManager.or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {     
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(heapRegions.size() + lvals.size());
    
    try {
      Expression alloc = state.getChild(1);
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
      
      // In any stack variable
      Set<Expression> lvals_copy = Sets.newHashSet(lvals);
      lvals_copy.removeAll(stackRegions);
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */  
      for( Expression lval : lvals_copy)    disjs.add(exprManager.and(ptr.eq(lval), size.eq(sizeZro)));
      
      // In any stack region
      for(Expression region : stackRegions) {
        Expression regionSize = alloc.asArray().index(region);
        BitVectorExpression ptrBound = exprManager.plus(addressType.getSize(), 
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addressType.getSize(), 
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
      
      // In any heap region
      for( Expression region : heapRegions ) {
        Expression regionSize = alloc.asArray().index(region);
        BitVectorExpression ptrBound = exprManager.plus(addressType.getSize(),
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addressType.getSize(),
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                region.neq(nullPtr), 
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return exprManager.or(disjs);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {   
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    Expression alloc = state.getChild(1);
    
    try {
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      alloc = alloc.asArray().update(ptr, sizeZro);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }   
    return exprManager.tuple(stateType, state.getChild(0), alloc, state.getChild(2));
  }

  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Preconditions.checkArgument(state.getType().equals(stateType));
    Preconditions.checkArgument(lval.getType().equals(cellType));
    
    Expression rval = getExpressionEncoding().getIntegerEncoding().unknown();
    Expression memory = state.getChild(0).asArray().update(lval, rval);
    return getExpressionManager().tuple(stateType, memory, state.getChild(1), state.getChild(2));
  }
  
  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(lval.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    Expression memory = state.getChild(0).asArray().update(lval, rval);  
    return getExpressionManager().tuple(stateType, memory, state.getChild(1), state.getChild(2));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(addressType.equals(p.getType()));
    Expression memory = state.getChild(0);
    return memory.asArray().index(p);
  }
  
  @Override
  public Expression createLval(Expression state, String name,
      IRVarInfo varInfo, Node node) {
    VariableExpression res = getExpressionManager().variable(name, addressType, true);
    lvals.add(res);
    return res;
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());

      /* All the stack regions are not overflow */
      for(Expression region : stackRegions) {
        Expression regionBound = exprManager.plus(addressType.getSize(), 
            region, alloc.asArray().index(region));
        builder.add(exprManager.lessThan(region, regionBound));
      }
      
      /* Assert the ordering on the stack */
      Iterator<Expression> lvalIter = lvals.iterator();
      Expression lval = null;
      if( lvalIter.hasNext() ) {
        lval = lvalIter.next();
      }

      while (lvalIter.hasNext()) {
        Expression lval2 = lvalIter.next();
        if(stackRegions.contains(lval2)) { // stack region variable
          Expression lval2Bound = exprManager.plus(addressType.getSize(), 
              lval2, alloc.asArray().index(lval2));
          builder.add(exprManager.greaterThan(lval, lval2Bound));
        } else {
          builder.add(exprManager.greaterThan(lval, lval2));
        }         
        lval = lval2;
      }
      
      if(lval != null) {
        Expression stackBound = lval;              
        Expression lastRegion = state.getChild(2);
        
        // lastRegionBound = lastRegion != 0 ? lastRegion + Size[lastRegion] : 0;
        Expression heapBound = exprManager.ifThenElse(
            lastRegion.neq(nullPtr),
            exprManager.plus(addressType.getSize(), lastRegion, alloc.asArray().index(lastRegion)),
            nullPtr);
        
        builder.add(exprManager.greaterThan(stackBound, heapBound));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( stateType ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, 
        addressType, true);
    
    heapRegions.add(locVar); // For dynamic memory allocation, add to heap regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(locVar, size);
    Expression lastRegion = state.getChild(2);
    
    Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
    Expression locVarBound = exprManager.plus(addressType.getSize(), locVar, size);
 
    Expression lastRegionBound = exprManager.plus(addressType.getSize(), 
        lastRegion, alloc.asArray().index(lastRegion));
    
    BooleanExpression res = exprManager.implies(
        locVar.neq(nullPtr),
        exprManager.and(
            exprManager.lessThan(locVar, locVarBound), // not overflow
            exprManager.or(
                lastRegion.eq(nullPtr), // last region is null (not allocated)
                exprManager.lessThanOrEqual(lastRegionBound, ptr) // larger than the last allocated region
                )));
    
    lastRegion = exprManager.ifThenElse(locVar.neq(nullPtr), locVar, lastRegion); // update last region
    Expression statePrime = exprManager.tuple(stateType, memory, alloc, lastRegion);
    setCurrentState(state, statePrime);
    
    return res;
  }
  
  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, memType, true);
    Expression allocVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, memType, true);
    Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
    return exprManager.tuple(stateType, memVar, allocVar, nullPtr);
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }

  @Override
  public boolean setStateType(Type stateType) {
  	Preconditions.checkArgument(stateType.isTuple());
    return false;
  }
  
  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(stateType.equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(stateType.equals(memory.getType()) );
        if(!isState(expr)) { 
          // For non-tuple expression evaluation
          Expression exprPrime = expr
              .subst(memoryVar.getChild(0), memory.getChild(0))
              .subst(memoryVar.getChild(1), memory.getChild(1));
          return exprPrime.setNode(expr.getNode());
        } else { 
          // For tuple expression evaluation over memoryVar, since substitution doesn't return
          // right children for as tuple expression for state.
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_alloc = memory.getChild(1);
          
          /* Substitute the alloc of expr to allocPrime */
          Expression memPrime = null;
          
          Expression mem = expr.getChild(0);
          if(mem.isVariable()) { // substitution makes no effect for variable
            assert(mem.equals(memoryVar.getChild(0)));
            memPrime = memory_mem;
          } else {
            memPrime = mem.subst(memoryVar.getChild(0), memory_mem);
            memPrime = mem.subst(memoryVar.getChild(1), memory_alloc);
          }
          
          /* Substitute the alloc of expr to allocPrime */
          Expression allocPrime = null;
          
          Expression alloc = expr.getChild(1);
          if(alloc.isVariable()) { // substitution makes no effect for variable
            assert(alloc.equals(memoryVar.getChild(1)));
            allocPrime = memory_alloc;
          } else {
            allocPrime = alloc.subst(memoryVar.getChild(0), memory_mem);
            allocPrime = alloc.subst(memoryVar.getChild(1), memory_alloc);
          }
          
          Expression last_region = expr.getChild(2);
          Expression last_regionPrime = last_region
              .subst(memoryVar.getChild(0), memory_mem)
              .subst(memoryVar.getChild(1), memory_alloc);
          
          return exprManager.tuple(stateType, memPrime, allocPrime, last_regionPrime);
        }
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
  public ExpressionClosure getCurrentState() {
    return currentState;
  }
  
  @Override
  public void clearCurrentState() {
    currentState = null;
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = CType.getType(content.getNode());
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.resolve();
      type = type.deannotate();
    }
    if(type.isArray() || type.isStruct() || type.isUnion())
      return content;
    else
      return content.getChild(1);
  }
  
  protected void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }

  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    Expression alloc = state.getChild(1);
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
    Expression ptrBound = exprManager.plus(addressType.getSize(), ptr, size);

    Expression lastRegion = state.getChild(2);
    Expression lastRegionBound = exprManager.plus(addressType.getSize(), 
        lastRegion, alloc.asArray().index(lastRegion));
    
    BooleanExpression res = exprManager.implies(
        ptr.neq(nullPtr),
        exprManager.and(
            exprManager.lessThan(ptr, ptrBound), // not overflow
            exprManager.or(
                lastRegion.eq(nullPtr), // last region is null (not allocated)
                exprManager.lessThanOrEqual(lastRegionBound, ptr)  // larger than the last allocated region
                )));
    
    lastRegion = exprManager.ifThenElse(ptr.neq(nullPtr), ptr, lastRegion); // update last region
    Expression statePrime = exprManager.tuple(stateType, state.getChild(0), state.getChild(1), lastRegion);
    setCurrentState(state, statePrime);
    
    return res;
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression size = state.getChild(1).asArray().index(ptr);
    Expression nullPtr = exprManager.bitVectorZero(addressType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
  }
  
  @Override
  public Expression substSizeArr(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, memType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(cellType.getSize()), memType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
  }
}