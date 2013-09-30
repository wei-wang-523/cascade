package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

/**
 * Monolithic memory mode, with a flat memory array. The array maps
 * a reference to a nested array which maps offset to actual 
 * cell, where cell type is union of pointer type and scalar type.
 *  
 * @author Wei
 *
 */
public class MonolithicVer1MemoryModel extends AbstractMonoMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static MonolithicVer1MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new MonolithicVer1MemoryModel(encoding);
  }

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType;
  private final ArrayType allocType; // ref-type -> off-type
  private final ArrayType memType;
  private TupleType stateType;
  
  private static final String CELL_TYPE_NAME = "cell";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final InductiveType cellType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    return BitVectorMemoryModel.create(encoding);
  }
  
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
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> heapRegions;
  private ExpressionClosure currentState = null;

  private MonolithicVer1MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.heapRegions = Lists.newArrayList();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.scalarType = exprManager.bitVectorType(size);
    
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    this.refType = ptrType.getElementTypes().get(0);
    this.offType = ptrType.getElementTypes().get(1).asBitVectorType();
    this.allocType = exprManager.arrayType(refType, offType);
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, scalarType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    /* Create datatype */
    this.cellType = exprManager.dataType(CELL_TYPE_NAME, scalarConstr, ptrConstr);
    this.memType = exprManager.arrayType(ptrType.getElementTypes().get(0), 
        exprManager.arrayType(ptrType.getElementTypes().get(1), cellType));
    this.stateType = exprManager.tupleType(DEFAULT_STATE_TYPE, memType, allocType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression memory = updateMemoryState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    TupleExpression statePrime = exprManager.tuple(stateType, memory, alloc);
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getExpressionManager().tuple(stateType, state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getExpressionManager().tuple(stateType, state.getChild(0), alloc);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression sizeZero = exprManager.bitVectorZero(offType.getSize());
    Expression alloc = state.getChild(1);
    
    try {
      for( Expression locVar : heapRegions )
        alloc = exprManager.ifThenElse(ptr.asTuple().index(0).eq(locVar), 
            alloc.asArray().update(locVar, sizeZero), alloc);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return exprManager.tuple(stateType, state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    
    ExpressionManager em = getExpressionManager();
    Expression memoryPrime = updateMemoryState(state.getChild(0), lval, rval);
    TupleExpression statePrime = em.tuple(stateType, memoryPrime, state.getChild(1));  
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    Expression cell = state.getChild(0).asArray()
        .index(p.asTuple().index(0)).asArray()
        .index(p.asTuple().index(1));
    
    xtc.type.Type pType = (xtc.type.Type) p.getNode().getProperty(TYPE);
    CellKind kind = CType.getCellKind(pType);
    if(CellKind.SCALAR.equals(kind) || CellKind.BOOL.equals(kind)) {
      return cell.asInductive().select(scalarSel);
    } else if(CellKind.POINTER.equals(kind)){
      return cell.asInductive().select(ptrSel);
    } else {
      throw new IllegalArgumentException("Invalid kind " + kind);
    }
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    
    ExpressionManager em = getExpressionManager();   
    Expression rval = null;
    
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = CType.getCellKind(lvalType);
    if(CellKind.SCALAR.equals(kind)) {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    } else if(CellKind.POINTER.equals(kind)) {
      rval = getExpressionEncoding().unknown();
    } else if(CellKind.BOOL.equals(kind)) {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    } else {
      throw new IllegalArgumentException("Invalid kind " + kind);
    }
    
    Expression memory = updateMemoryState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = em.tuple(stateType, memory, state.getChild(1));
        
    return statePrime;
  }
  
  @Override
  public Expression createLval(String name) {
    ExpressionManager exprManager = getExpressionManager();
    VariableExpression ref = exprManager.variable(name, refType, true);
    Expression off = exprManager.bitVectorZero(offType.getSize());
    Expression res = exprManager.tuple(ptrType, ref, off);
    lvals.add(ref);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType) );
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression mem = updateMemoryState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);
    
    Expression statePrime = exprManager.tuple(stateType, mem, alloc);
    setCurrentState(state, statePrime);
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      /* No comparable predicate defined in uninterpreted type */
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in monolithic memory model");
    }
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        ExpressionManager exprManager = getExpressionManager();
        
        { /* The disjointness of stack variables, and != nullRef*/
          Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr().getChild(0);
          ImmutableList<Expression> distinctRef = new ImmutableList.Builder<Expression>()
              .addAll(lvals).add(nullRef).build();
          if(distinctRef.size() > 1)  builder.add(exprManager.distinct(distinctRef));
        }
        
        { /* The disjointness between heap region and stack variable. */
          for(Expression heapRegion : heapRegions) {
            for(Expression lval : lvals) {
              builder.add(lval.neq(heapRegion));
            }
          }
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
    Expression allocVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        allocType, true);
    return exprManager.tuple(stateType, memVar, allocVar);
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        if(!isState(expr)) {
          // For non-tuple expression evaluation
          Expression exprPrime = expr
              .subst(memoryVar.getChildren(), memory.getChildren());
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          return exprManager.tuple(expr.getType(), RecursionStrategies.unaryRecursionOverList(
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
    Preconditions.checkArgument(content.getNode().hasProperty(TYPE));
    xtc.type.Type contentType = CType.unwrapped((xtc.type.Type) 
        (content.getNode().getProperty(TYPE)));
    
    if(contentType.isUnion() || contentType.isStruct()) {
      return content;
    } else {
      Expression cellVal = content.getChild(0);
      Expression off = cellVal.getChild(1);
      Expression ref = cellVal.getChild(0).getChild(1);
      return getExpressionManager().tuple(ptrType, ref, off);
    }
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      Expression ref_ptr = ptr.asTuple().index(0);
      Expression off_ptr = ptr.asTuple().index(1);
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr().asTuple().getChild(0);
      
      // Valid stack access
      for( Expression lval : lvals) {
        Expression sizeVar = alloc.asArray().index(lval);
        disjs.add(
            exprManager.and(
                ref_ptr.eq(lval), 
                /* aggregate variable: size > 0; scalar variable: size = 0 */
                exprManager.ifThenElse( 
                    exprManager.greaterThan(sizeVar, sizeZro),
                    exprManager.and(
                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
                        exprManager.lessThan(off_ptr, sizeVar)),
                    off_ptr.eq(sizeVar))));
      }
      
      // Valid heap access
      for( Expression refVar : heapRegions ) {
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        Expression sizeVar = alloc.asArray().index(refVar);
        disjs.add(
            exprManager.and(
                refVar.neq(nullRef),
                ref_ptr.eq(refVar),
                exprManager.lessThanOrEqual(sizeZro, off_ptr),
                exprManager.lessThan(off_ptr, sizeVar)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      Expression ref_ptr = ptr.asTuple().index(0);
      Expression off_ptr = ptr.asTuple().index(1);
      Expression off_bound = exprManager.plus(offType.getSize(), off_ptr, size);
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr().asTuple().getChild(0);
      
      // Valid stack access
      for( Expression lval : lvals) {
        Expression sizeVar = alloc.asArray().index(lval);
        disjs.add(
            exprManager.and(
                ref_ptr.eq(lval), 
                /* aggregate variable: size > 0; scalar variable: size = 0 */
                exprManager.ifThenElse( 
                    exprManager.greaterThan(sizeVar, sizeZro),
                    exprManager.and(        
                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
                        exprManager.lessThan(off_bound, sizeVar)),
                    off_ptr.eq(sizeVar)))); 
      }
      
      // Valid heap access
      for( Expression refVar : heapRegions ) {
        Expression sizeVar = alloc.asArray().index(refVar);
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        disjs.add(
            exprManager.and(
                refVar.neq(nullRef),
                ref_ptr.eq(refVar), 
                exprManager.lessThanOrEqual(sizeZro, off_ptr),
                exprManager.lessThan(off_bound, sizeVar)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    ExpressionManager exprManager = getExpressionManager();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in monolithic memory model");
    } 
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
      Expression alloc = state.getChild(1);
      
      ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
      
      Expression nullPtr = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr();
      Expression nullRef = nullPtr.asTuple().getChild(0);
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      builder.add(exprManager.neq(ptr, nullPtr)); // ptr != null
      
      /* Only analyze heap part */
      
      List<Expression> regions = Lists.newArrayList(heapRegions);
      
      /* Collect all heap regions except the last one, the one just allocated. */
      regions.remove(regions.size()-1);
      
      for(Expression region : regions) {
        Expression region_size = alloc.asArray().index(region);
        
        Expression assump_local = exprManager.and(
            exprManager.greaterThan(region_size, sizeZro),
            exprManager.neq(region, nullRef)); // nullRef may also have non-zero size
        
        Expression assert_local = exprManager.neq(region, ptr.asTuple().index(0));
        
        builder.add(exprManager.implies(assump_local, assert_local));
      }
      
      return exprManager.implies(assump, exprManager.and(builder.build()));
    }
    
    return exprManager.tt();
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression alloc = state.getChild(1); 
    Expression ref = ptr.asTuple().index(0);
    Expression size = alloc.asArray().index(ref);
    Expression nullPtr = ((PointerExpressionEncoding) getExpressionEncoding())
        .getPointerEncoding().nullPtr();
    return exprManager.or(exprManager.eq(ptr, nullPtr), exprManager.greaterThan(size, 
        exprManager.bitVectorZero(offType.getSize())));
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, allocType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(offType.getSize()), allocType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
  }
  
  @Override
  protected ArrayExpression updateMemoryState(Expression memory, Expression lval, Expression rval) {
    Preconditions.checkArgument(memory.getType().equals(memType));
    Preconditions.checkArgument(lval.getType().equals(ptrType));
    Preconditions.checkArgument(rval.getType().equals(ptrType) || rval.getType().equals(scalarType) || rval.isBoolean());
    
    ExpressionManager em = getExpressionManager();
    // Compose the cell value with rval
    Expression cellVal = null;
    
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = CType.getCellKind(lvalType);
    if(CellKind.SCALAR.equals(kind) || CellKind.BOOL.equals(kind)) {
      cellVal = em.construct(scalarConstr, rval);
    } else if(CellKind.POINTER.equals(kind)) {
      if(rval.isBitVector()) {
        assert(rval.isConstant());
        rval = ((PointerExpressionEncoding) getExpressionEncoding())
            .getPointerEncoding().nullPtr();
      }
      cellVal = em.construct(ptrConstr, rval);
    } else {
      throw new IllegalArgumentException("Invalid kind " + kind);
    }
    
    Expression refExpr = lval.asTuple().index(0);
    Expression offExpr = lval.asTuple().index(1);
    
    Expression block = memory.asArray().index(refExpr);
    Expression blockPrime = block.asArray().update(offExpr, cellVal);
    
    return memory.asArray().update(refExpr, blockPrime);    
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
}
