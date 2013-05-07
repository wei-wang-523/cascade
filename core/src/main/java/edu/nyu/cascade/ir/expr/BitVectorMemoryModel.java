package edu.nyu.cascade.ir.expr;

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

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
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

public class BitVectorMemoryModel extends AbstractMemoryModel {  
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param size the desired size of a pointer
   * @param size2 the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static BitVectorMemoryModel create(
      ExpressionEncoding encoding,
      int size, int size2)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    BitVectorType addressType = exprManager.bitVectorType(size);
    BitVectorType cellType = exprManager.bitVectorType(size2);

    ArrayType memArrayType = exprManager.arrayType(addressType, cellType);

    return new BitVectorMemoryModel(encoding, memArrayType);
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
  public static BitVectorMemoryModel create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(memArrayType.getIndexType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getElementType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getIndexType().asBitVectorType().getSize()
        % memArrayType.getElementType().asBitVectorType().getSize() == 0);
      return new BitVectorMemoryModel(encoding,
          memArrayType);
  }

  public static BitVectorMemoryModel create(
      ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException
  {
    return create(encoding, memArray.getType());
  }

  protected final BitVectorType addressType;
  protected final BitVectorType cellType;
  protected final ArrayType memType;
  protected final Set<Expression> lvals; // variables in stack
  
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
  protected final Set<Expression> rvals;
  protected final List<Expression> heapRegions, stackRegions;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;

  protected BitVectorMemoryModel(ExpressionEncoding encoding, ArrayType memType) {
    super(encoding);
    
    IntegerEncoding<?> integerEncoding = encoding.getIntegerEncoding();
    Preconditions.checkArgument(integerEncoding.getType().equals( memType.getIndexType() ));
  
    this.lvals = Sets.newHashSet();
    this.rvals = Sets.newHashSet();
    this.heapRegions = Lists.newArrayList();
    this.stackRegions = Lists.newArrayList();

    this.memType = memType;
    addressType = memType.getIndexType().asBitVectorType();
    cellType = memType.getElementType().asBitVectorType();
  }  
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, 
        addressType, true);
    
    heapRegions.add(locVar); // For dynamic memory allocation, add to the end of regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(locVar, size);    
    return exprManager.tuple(getStateType(), memory, alloc);
  }
  
  @Override
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
       
    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add((VariableExpression) ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }
  
  @Override
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
       
    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add((VariableExpression) ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }
  
  /* TODO: This will fail for automatically allocated addresses (e.g., the
   * address of a local variable). */  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {     
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    
    /* Collect all the regions. */
    List<Expression> regions = Lists.newArrayList();
    regions.addAll(stackRegions);
    regions.addAll(heapRegions);
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(regions.size());
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      
      for( Expression locVar : regions ) {
        Expression sizeVar = alloc.asArray().index(locVar);
        BitVectorExpression regionBound = exprManager.plus(addressType
            .getSize(), locVar, sizeVar);
        disjs.add(locVar.asBitVector().lessThanOrEqual(ptr)
          .and(ptr.asBitVector().lessThan(regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {   
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    Expression alloc = state.getChild(1);
    
    try {
      BitVectorExpression regionZero = getExpressionEncoding().getIntegerEncoding()
          .zero().asBitVector();
      alloc = alloc.asArray().update(ptr, regionZero);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }

  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Preconditions.checkArgument(state.getType().equals(getStateType()));
    Preconditions.checkArgument(lval.getType().equals(cellType));
    Expression rval = getExpressionEncoding().unknown();
    Expression memory = state.getChild(0).asArray().update(lval, rval);
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1));
  }
  
  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    Expression memory = state.getChild(0); 
    memory = memory.asArray().update(lval, rval);  
    
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(addressType.equals(p.getType()));
    Expression memory = state.getChild(0);
    return memory.asArray().index(p);
  }
  
  @Override
  public void addLval(VariableExpression p) {
    lvals.add(p);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      List<Expression> regions = Lists.newArrayList();
      /* Collect all the regions. */
      regions.addAll(stackRegions);
      regions.addAll(heapRegions);
      /* Remove all the variable in rvals from lvals. */
      lvals.removeAll(rvals);
      
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
          BitVectorExpression regionBound = exprManager.plus(addressType
              .getSize(), locVar, sizeVar);

          /* The upper bound of the region won't overflow */
          builder.add(exprManager.implies(exprManager.greaterThan(sizeVar, exprManager
              .bitVectorZero(cellType.getSize())), exprManager.greaterThan(regionBound, locVar)));
       
          /* Every lval is outside of the region */
          for (Expression lval : lvals) {
            builder.add(exprManager.or(exprManager.lessThan(lval, locVar),
                exprManager.lessThanOrEqual(regionBound, lval)));
          }
          /* Every other allocated region is non-overlapping */
          // TODO: Could optimize using commutativity
          for (Expression locVar2 : regions) {
            if (!locVar.equals(locVar2)) {
              Expression sizeVar2 = alloc.asArray().index(locVar2);

              builder.add(exprManager.or(exprManager.lessThanOrEqual(exprManager.plus(
                  addressType.getSize(), locVar2, sizeVar2), locVar),
                  exprManager.lessThanOrEqual(regionBound, locVar2)));
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
          builder.add(exprManager.lessThan(lval, lval2));
          lval = lval2;
        }

        BitVectorExpression regionBound;
        if( lval != null ) {
          regionBound = exprManager.asBitVector(lval);
        } else {
          regionBound = getExpressionEncoding().getIntegerEncoding().zero()
              .asBitVector();
        }

        for (Expression locVar : regions) {
          builder.add(exprManager.lessThan(regionBound, locVar));

          Expression sizeVar = alloc.asArray().index(locVar);
          regionBound = exprManager
              .plus(addressType.getSize(), locVar, sizeVar);

          /* The upper bound of the region won't overflow */
          builder.add(exprManager.greaterThanOrEqual(regionBound, locVar));
        }
      } // else nothing to assume memory is safe without aliasing or region overlapping
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, 
        addressType, true);
    
    heapRegions.add(locVar); // For dynamic memory allocation, add to heap regions;
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(locVar, size);
    Expression statePrime = exprManager.tuple(getStateType(), memory, alloc);
    
    setCurrentState(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression allocVar = exprManager.variable(DEFAULT_REGION_SIZE_VARIABLE_NAME, 
        memType, true);
    return exprManager.tuple(getStateType(), memVar, allocVar);
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return getExpressionManager().tupleType("memState", memType, memType);
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
        if(!expr.isTuple()) { 
          // For non-tuple expression evaluation
          Expression exprPrime = expr
              .subst(memoryVar.getChildren(), memory.getChildren());
          return exprPrime.setNode(expr.getNode());
        } else { 
          // For tuple expression evaluation over memoryVar, since substitution doesn't return
          // right children for as tuple expression for state.
          ExpressionManager exprManager = getExpressionManager();
          return exprManager.tuple(getStateType(), RecursionStrategies.unaryRecursionOverList(
              expr.getChildren(),
              new UnaryRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression e) {
              Expression ePrime = e.subst(ImmutableList.of(memoryVar.getChild(0)), 
                  ImmutableList.of(memory.getChild(0)));
              ePrime = ePrime.subst(ImmutableList.of(memoryVar.getChild(1)), 
                  ImmutableList.of(memory.getChild(1)));
              return ePrime;
            }
          }));
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
    };
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
