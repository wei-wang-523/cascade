package edu.nyu.cascade.ir.expr;

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.ArrayVariableExpression;
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
import edu.nyu.cascade.util.Preferences;

public class MonolithicMemoryModel extends AbstractMemoryModel {  
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static MonolithicMemoryModel create(
      ExpressionEncoding encoding,
      int addressSize, int cellSize)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    BitVectorType addressType = exprManager.bitVectorType(addressSize);
    BitVectorType cellType = exprManager.bitVectorType(cellSize);
    TupleType ptrType = exprManager.tupleType("pointerType", addressType, cellType);
    ArrayType memArrayType = exprManager.arrayType(ptrType, ptrType);

    return new MonolithicMemoryModel(encoding, memArrayType);
  }
  
  /** Create an expression factory with the given array type to model memory. The size of the 
   * index type of the memory array (i.e., the size of a pointer) must be a multiple of the size
   * of the element type (i.e., the size of a memory word).
   */
  public static MonolithicMemoryModel create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(memArrayType.getIndexType().isTuple());
    Preconditions.checkArgument(memArrayType.getElementType().isTuple());
    Preconditions.checkArgument(memArrayType.getIndexType().asTuple().
        getElementTypes().get(0).asBitVectorType().getSize()
        % memArrayType.getElementType().asTuple().getElementTypes().get(1).
        asBitVectorType().getSize() == 0);
    
    return new MonolithicMemoryModel(encoding, memArrayType);
  }

  public static MonolithicMemoryModel create(ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException
  {
    return create(encoding, memArray.getType());
  }

  private final TupleType ptrType;
  private final ArrayType memType;
  private final ArrayType sizeType;
  
  private final Set<Expression> lvals;// variables in stack
  
  /** when allocate a region_x in stack of array or structure, we just 
   * let addr_of_array == region_x, or addr_of_struct == region_x, 
   * which models exactly what happened in C. It means we should remove 
   * addr_of_array or addr_of_struct from lvals, otherwise when do 
   * --sound-alloc or --order-alloc, we will call getAssumptions(), which
   * ensures that addr_of_array/addr_of_struct < region_x or addr_of_array
   * /addr_of_strcut != region_x, and it's conflict with the above equality.
   * Here, we keep rvals to record those removed addr_of_struct and addr_of_array,
   * and remove them from lvals in getAssumptions().
   */
  private final Set<Expression> rvals;
  private final List<Expression> stackRegions, heapRegions;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;
  
  /* side-effect assumption, generated in memory operations
   * private BooleanExpression sideAssump;
   */

  private MonolithicMemoryModel(ExpressionEncoding encoding, ArrayType memType) {
    super(encoding);
    
    PointerEncoding<?> pointerEncoding = ((PointerExpressionEncoding) encoding)
        .getPointerEncoding();
    Preconditions.checkArgument(pointerEncoding.getType().equals(memType.getIndexType()));
    Preconditions.checkArgument(pointerEncoding.getType().equals(memType.getElementType()));
    Preconditions.checkArgument(pointerEncoding.getType().isTuple());
    Preconditions.checkArgument(pointerEncoding.getType().asTuple().size() == 2);
  
    this.lvals = Sets.newHashSet();
    this.rvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();

    this.memType = memType;
    this.ptrType = memType.getIndexType().asTuple();
    this.sizeType = getExpressionManager().arrayType(
        ptrType.getElementTypes().get(0), ptrType.getElementTypes().get(1));
  }  
  
  private BitVectorType getRefType() {
    return this.ptrType.getElementTypes().get(0).asBitVectorType();
  }
  
  private BitVectorType getOffType() {
    return this.ptrType.getElementTypes().get(1).asBitVectorType();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar.asBitVector(), offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end of regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(
        refVar, size.asTuple().index(1));
    return exprManager.tuple(getStateType(), memory, alloc);
  }
  
  @Override
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();

    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add((VariableExpression) ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size.asTuple().index(1));   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }
  
  @Override
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();

    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add((VariableExpression) ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size.asTuple().index(1));   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }
  
  /* TODO: This will fail for automatically allocated addresses (e.g., the
   * address of a local variable).
   */
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {   
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    
    /* Collect all the regions. */
    List<Expression> regions = Lists.newArrayList();
    regions.addAll(stackRegions);
    regions.addAll(heapRegions);
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(regions.size());
    
    try {
      PointerExpressionEncoding ptrEncoding = (PointerExpressionEncoding) 
          getExpressionEncoding();
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      
      for( Expression refVar : regions ) {
        Expression sizeZro = exprManager.bitVectorZero(getOffType().getSize());
        Expression startPos = exprManager.tuple(ptrType, refVar, sizeZro);
        Expression sizeVar = alloc.asArray().index(refVar);
        Expression endPos = exprManager.tuple(ptrType, refVar, sizeVar);
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        disjs.add(ptrEncoding.lessThanOrEqual(startPos, ptr)
          .and(ptrEncoding.lessThan(ptr, endPos)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {   
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression sizeZero = exprManager.bitVectorZero(getOffType().getSize());
    Expression alloc = state.getChild(1);
    
    try {
        for( Expression locVar : heapRegions )
          alloc = exprManager.ifThenElse(ptr.asTuple().index(0).eq(locVar), 
              alloc.asArray().update(locVar, sizeZero), alloc);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    if(!rval.getType().equals(ptrType)) {
      PointerExpressionEncoding ptrEncoding = (PointerExpressionEncoding) 
          getExpressionEncoding();
      rval = ptrEncoding.castToInteger(rval).asBitVector();
      rval = ptrEncoding.castToPointer(rval);
    }
    Expression memory = state.getChild(0).asArray().update(lval, rval);   
    
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    Expression memory = state.getChild(0);
    return memory.asArray().index(p);
  }
  
  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression rval = getExpressionEncoding().unknown();
    Expression memory = state.getChild(0).asArray().update(lval, rval);   
    
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1));
  }
  
  @Override
  public VariableExpression createLval(String name) {
    VariableExpression res = getExpressionManager().variable(name, ptrType, true);
    lvals.add(res);
    return res;
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      ExpressionManager exprManager = getExpressionManager();
      PointerExpressionEncoding ptrEncoding = (PointerExpressionEncoding) getExpressionEncoding();
      Expression alloc = state.getChild(1);
      List<Expression> regions = Lists.newArrayList();
      /* Collect all the regions. */
      regions.addAll(stackRegions);
      regions.addAll(heapRegions);
      /* Remove all the variable in structVals from lvals. */
      lvals.remove(rvals);
      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        /* The sound allocation encoding doesn't assume anything about the ordering
         * of lvals and regions. This may lead a blow-up due to case splits.
         */
        if (lvals.size() > 1) {
          builder.add(exprManager.distinct(lvals));
        }
        /* Collect constraints for memory regions */
        for (Expression locVar : regions) {
          Expression sizeVar = alloc.asArray().index(locVar);
          Expression regionBound = exprManager.plus(getRefType().getSize(), 
              locVar, sizeVar);

          /* The upper bound of the region won't overflow */
          builder.add(exprManager.implies(
              exprManager.greaterThan(sizeVar, exprManager.bitVectorZero(0)),
              exprManager.greaterThan(regionBound, locVar)));
          
          /* Every lval is outside of the region */
          for (Expression lval : lvals) {
            builder.add(lval.neq(locVar));
          }
          /* Every other allocated region is non-overlapping */
          // TODO: Could optimize using commutativity
          for (Expression locVar2 : regions) {
            if (!locVar.equals(locVar2)) {
              builder.add(locVar.neq(locVar2));
            }
          }
        }
      } else if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
        /* Unsound allocation encoding: just pick an order and assert that
         * the lvals and regions are allocated in that order. 
         */
        Expression lval = null;
       
        /* Assert the ordering on the lvals */
        Iterator<Expression> lvalIter = lvals.iterator();
        if( lvalIter.hasNext() ) {
          lval = lvalIter.next();
        }
        
        while (lvalIter.hasNext()) {
          Expression lval2 = lvalIter.next();
          builder.add(ptrEncoding.lessThan(lval, lval2));
          lval = lval2;
        }

        Expression refVar;
        if( lval != null )
          refVar = lval.asTuple().index(0);
        else
          refVar = exprManager.bitVectorZero(getOffType().getSize());

        for (Expression locVar : regions) {
          /* locVar : region_x, refVar : region_y - region_y < region_x */
          builder.add(exprManager.lessThan(refVar, locVar));

          /* The upper bound of the region won't overflow */
          Expression sizeVar = alloc.asArray().index(locVar);
          Expression regionBound = exprManager.plus(getRefType().getSize(),
              locVar, sizeVar);
          refVar = locVar;
          builder.add(exprManager.greaterThan(regionBound, locVar));
        }
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
  }

  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression allocVar = exprManager.variable(DEFAULT_REGION_SIZE_VARIABLE_NAME, 
        sizeType, true);
    return exprManager.tuple(getStateType(), memVar, allocVar);
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return getExpressionManager().tupleType("stateType", memType, sizeType);
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression memory) {
        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
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
    };
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar.asBitVector(), offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end of regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(
        refVar, size.asTuple().index(1));

    setCurrentState(state, exprManager.tuple(getStateType(), memory, alloc));
    return exprManager.tt();
  }
  
  @Override
  public ExpressionClosure getCurrentState() {
    return currentState;
  }
  
  @Override
  public void resetCurrentState() {
    currentState = null;
  }
  
  protected void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
}
