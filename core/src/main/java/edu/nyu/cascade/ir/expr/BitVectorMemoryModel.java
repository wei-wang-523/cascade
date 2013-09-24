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

public class BitVectorMemoryModel extends AbstractMemoryModel {  
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_ALLOC_VARIABLE_NAME = "alloc";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static BitVectorMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    
    BitVectorType addressType = exprManager.bitVectorType(size);
    BitVectorType cellType = exprManager.bitVectorType(size);

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
    return exprManager.tuple(getStateType(), memory, alloc, state.getChild(2));
  }
  
  @Override
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
       
    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add(ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return exprManager.tuple(getStateType(), state.getChild(0), alloc, state.getChild(2));
  }
  
  @Override
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
       
    stackRegions.add(ptr); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add(ptr); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(ptr, size);  
    return exprManager.tuple(getStateType(), state.getChild(0), alloc, state.getChild(2));
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
    
    ExpressionManager exprManager = getExpressionManager();
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(regions.size());
    
    try {
      Expression alloc = state.getChild(1);
      
      for( Expression locVar : regions ) {
        Expression sizeVar = alloc.asArray().index(locVar);
        Expression sizeZro = exprManager.bitVectorZero(addressType.getSize());
        
        BitVectorExpression regionBound = exprManager.plus(addressType
            .getSize(), locVar, sizeVar);
        disjs.add(
            exprManager.ifThenElse(
                exprManager.and(locVar.neq(sizeZro), sizeVar.neq(sizeZro)), 
                exprManager.and(
                    locVar.asBitVector().lessThanOrEqual(ptr),
                    ptr.asBitVector().lessThan(regionBound)), 
                    exprManager.ff()).asBooleanExpression());
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return exprManager.or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {     
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    
    /* Collect all the regions. */
    List<Expression> regions = Lists.newArrayList();
    regions.addAll(stackRegions);
    regions.addAll(heapRegions);
    
    ExpressionManager exprManager = getExpressionManager();
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(regions.size());
    
    try {
      Expression alloc = state.getChild(1);
      
      for( Expression locVar : regions ) {
        Expression sizeVar = alloc.asArray().index(locVar);
        Expression sizeZro = exprManager.bitVectorZero(addressType.getSize());
        
        BitVectorExpression ptrBound = exprManager.plus(addressType.getSize(), ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addressType
            .getSize(), locVar, sizeVar);
        disjs.add(
            exprManager.ifThenElse(
                exprManager.and(locVar.neq(sizeZro), sizeVar.neq(sizeZro)), 
                exprManager.and(
                    locVar.asBitVector().lessThanOrEqual(ptr),
                    ptrBound.lessThan(regionBound)), 
                    exprManager.ff()).asBooleanExpression());
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return exprManager.or(disjs);
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
    return exprManager.tuple(getStateType(), state.getChild(0), alloc, state.getChild(2));
  }

  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Preconditions.checkArgument(state.getType().equals(getStateType()));
    Preconditions.checkArgument(lval.getType().equals(cellType));
    Expression rval = getExpressionEncoding().unknown();
    Expression memory = state.getChild(0).asArray().update(lval, rval);
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1), state.getChild(2));
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
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1), state.getChild(2));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(addressType.equals(p.getType()));
    Expression memory = state.getChild(0);
    return memory.asArray().index(p);
  }
  
  @Override
  public VariableExpression createLval(String name) {
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
        ImmutableList<Expression> vars = new ImmutableList.Builder<Expression>()
            .addAll(lvals).addAll(regions).build();
        
        if (!vars.isEmpty())   builder.add(exprManager.distinct(vars));
        
        /* Collect constraints for memory regions */
        for (Expression region : regions) {
          Expression sizeVar = alloc.asArray().index(region);
          BitVectorExpression regionBound = exprManager.plus(addressType.getSize(), region, sizeVar);
          
          Expression zro = exprManager.bitVectorZero(addressType.getSize());
//          /* The upper bound of the region won't overflow */
//          builder.add(exprManager.implies(exprManager.greaterThan(sizeVar, exprManager
//              .bitVectorZero(cellType.getSize())), exprManager.greaterThan(regionBound, locVar)));
       
          /* Every lval is outside of the region */
          for (Expression lval : lvals) {            
            builder.add(exprManager.implies(
                exprManager.and(region.neq(zro)),
                exprManager.or(exprManager.lessThan(lval, region),
                    exprManager.lessThanOrEqual(regionBound, lval))));
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
          builder.add(exprManager.greaterThan(lval, lval2));
          lval = lval2;
        }
        
        BitVectorExpression stackBound = (lval != null) ? exprManager.asBitVector(lval) : null;
        
        if(stackBound != null) {
          Expression lastRegion = state.asTuple().getChild(2);
          Expression sizeZro = getExpressionManager().bitVectorZero(addressType.getSize());
          
          
          // lastRegionBound = lastRegion != 0 ? lastRegion + Alloc[lastRegion] : 0;
          Expression heapBound = exprManager.ifThenElse(
              lastRegion.neq(sizeZro),
                exprManager.plus(addressType.getSize(), lastRegion, alloc.asArray().index(lastRegion)),
                sizeZro); // 0
          builder.add(exprManager.greaterThan(stackBound, heapBound));
        } 

//        BitVectorExpression regionBound;
//        if( lval != null ) {
//          regionBound = exprManager.asBitVector(lval);
//        } else {
//          regionBound = getExpressionEncoding().getIntegerEncoding().zero()
//              .asBitVector();
//        }
//
//        for (Expression locVar : regions) {
//          builder.add(exprManager.lessThan(regionBound, locVar));
//
//          Expression sizeVar = alloc.asArray().index(locVar);
//          regionBound = exprManager
//              .plus(addressType.getSize(), locVar, sizeVar);
//
//          /* The upper bound of the region won't overflow */
//          builder.add(exprManager.greaterThanOrEqual(regionBound, locVar));
//        }
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
    Expression statePrime = exprManager.tuple(getStateType(), memory, alloc, state.getChild(2));
    
    setCurrentState(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression allocVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        memType, true);
    Expression last_region = exprManager.bitVectorZero(addressType.getSize());
    return exprManager.tuple(getStateType(), memVar, allocVar, last_region);
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return getExpressionManager().tupleType(DEFAULT_STATE_TYPE, memType, memType, memType.getIndexType());
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
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
          
          Expression last_region = expr.asTuple().getChild(2);
          Expression last_regionPrime = last_region
              .subst(memoryVar.getChild(0), memory_mem)
              .subst(memoryVar.getChild(1), memory_alloc);
          
          return exprManager.tuple(getStateType(), memPrime, allocPrime, last_regionPrime);
          
//          return exprManager.tuple(getStateType(), RecursionStrategies.unaryRecursionOverList(
//              expr.getChildren(),
//              new UnaryRecursionStrategy<Expression, Expression>() {
//            @Override
//            public Expression apply(Expression e) {
//              Expression ePrime = e;
//              if(e.isVariable()) {
//                assert(memoryVar.getChildren().contains(e));
//              } else {
//                ePrime = e.subst(memoryVar.getChild(0), memory.getChild(0));
//                ePrime = ePrime.subst(memoryVar.getChild(1), memory.getChild(1));
//              }
//              return ePrime;
//            }
//          }));
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
    xtc.type.Type type = (xtc.type.Type) content.getNode().getProperty(TYPE);
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
    Expression zro = exprManager.bitVectorZero(addressType.getSize());
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      Expression lastRegion = state.getChild(2);
      BooleanExpression res = exprManager.implies(
          exprManager.neq(ptr, zro),
          exprManager.and(
              exprManager.greaterThan(ptr, zro),
              exprManager.lessThan(ptr, exprManager.plus(addressType.getSize(), ptr, size)),
              exprManager.or(
                  exprManager.eq(lastRegion, zro),
                  exprManager.lessThanOrEqual(
                      exprManager.plus(addressType.getSize(), lastRegion, alloc.asArray().index(lastRegion)), 
                      ptr)
                  )));
      
      lastRegion = exprManager.ifThenElse(
          ptr.neq(zro), ptr, lastRegion);
      Expression statePrime = exprManager.tuple(getStateType(), 
          state.getChild(0), state.getChild(1), lastRegion);
      setCurrentState(state, statePrime);
      
      return res;
    } else {
      ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
      
      Expression assump = exprManager.neq(ptr, zro);
      
      builder.add(exprManager.greaterThan(ptr, zro));
      builder.add(exprManager.lessThan(ptr, exprManager.plus(addressType.getSize(), ptr, size)));
      
      List<Expression> regions = Lists.newArrayList();
      /* Collect all the regions. */
      regions.addAll(stackRegions);
      regions.addAll(heapRegions);
      
      for(Expression region : regions) {
        Expression assump_local = exprManager.and(
            exprManager.greaterThan(alloc.asArray().index(region), zro),
            exprManager.neq(region, zro),
            exprManager.neq(region, ptr));
        Expression assert_local = exprManager.or(
            exprManager.lessThanOrEqual(
                exprManager.plus(addressType.getSize(), ptr, size), region),
            exprManager.lessThanOrEqual(
                exprManager.plus(addressType.getSize(), region, alloc.asArray().index(region)), ptr));
        builder.add(exprManager.implies(assump_local, assert_local));
      }
      
      BooleanExpression res = exprManager.implies(assump, exprManager.and(builder.build()));
      return res;
    }
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression size = state.getChild(1).asArray().index(ptr);
    Expression zro = exprManager.bitVectorZero(addressType.getSize());
    return exprManager.or(exprManager.eq(ptr, zro), exprManager.greaterThan(size, zro));
  }
  
  public Expression substAlloc(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, memType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(cellType.getSize()), memType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
  }
}
