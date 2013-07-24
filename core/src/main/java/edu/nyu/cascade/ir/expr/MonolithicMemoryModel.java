package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Set;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

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

public class MonolithicExtendMemoryModel extends AbstractMemoryModel {
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";
  protected static final String TEST_VAR = "TEST_VAR";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static MonolithicExtendMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new MonolithicExtendMemoryModel(encoding);
  }

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final BitVectorType scalarType;
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
  private final List<Expression> stackRegions, heapRegions;
  private ExpressionClosure currentState = null;

  private MonolithicExtendMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.scalarType = exprManager.bitVectorType(size);
    
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    this.allocType = exprManager.arrayType(
        ptrType.getElementTypes().get(0), ptrType.getElementTypes().get(1));
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, scalarType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    /* Create datatype */
    this.cellType = exprManager.dataType(CELL_TYPE_NAME, scalarConstr, ptrConstr);
    this.memType = exprManager.arrayType(ptrType, cellType);
    this.stateType = exprManager.tupleType(DEFAULT_STATE_TYPE, memType, allocType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( getOffType() ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
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
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( getOffType() ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0); 
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion);
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getExpressionManager().tuple(stateType, state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( getOffType() ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    
    return getExpressionManager().tuple(stateType, state.getChild(0), alloc);
  }

  /* TODO: This will fail for automatically allocated addresses (e.g., the
   * address of a local variable).
   */
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));

    /* Collect all the regions. */
    List<Expression> regions = Lists.newArrayList();
    regions.addAll(stackRegions);
    regions.addAll(heapRegions);
    
    List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(regions.size());
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      
      Expression ref_ptr = ptr.asTuple().index(0);
      Expression off_ptr = ptr.asTuple().index(1);
      
      for( Expression refVar : regions ) {        
        Expression sizeZro = exprManager.bitVectorZero(getOffType().getSize());
        Expression sizeVar = alloc.asArray().index(refVar);
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        disjs.add(
            exprManager.and(
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
  public TupleExpression free(Expression state, Expression ptr) {
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
    Expression cell = state.getChild(0).asArray().index(p);
    
    if(isScalarType(p.getNode())) {
      return cell.asInductive().select(scalarSel);
    } else {
      return cell.asInductive().select(ptrSel);
    }
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    
    ExpressionManager em = getExpressionManager();
    
    Expression rval = null;
    if(isScalarType(lval.getNode())) {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    } else {
      rval = getExpressionEncoding().unknown();
    }
    
    Expression memory = updateMemoryState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = em.tuple(stateType, memory, state.getChild(1));
        
    return statePrime;
  }
  
  @Override
  public Expression createLval(String name) {
    ExpressionManager exprManager = getExpressionManager();
    VariableExpression ref = exprManager.variable(name, getRefType(), true);
    Expression off = exprManager.bitVectorZero(getOffType().getSize());
    Expression res = exprManager.tuple(ptrType, ref, off);
    lvals.add(ref);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( allocType.getElementType()) );
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression mem = updateMemoryState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);
    
    Expression statePrime = exprManager.tuple(stateType, mem, alloc);
    setCurrentState(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        ExpressionManager exprManager = getExpressionManager();
        /* The sound allocation encoding doesn't assume anything about the ordering
         * of lvals and regions. This may lead a blow-up due to case splits.
         */
        ImmutableList<Expression> distinctRef = new ImmutableList.Builder<Expression>()
            .addAll(heapRegions).addAll(lvals).build();
        if(distinctRef.size() > 1) {
          builder.add(exprManager.distinct(distinctRef));
        }
        
      } else if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
        throw new UnsupportedOperationException("--order-alloc is not supported in burstall memory model");
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
  
  private boolean isScalarType(Node node) {
    xtc.type.Type type = (xtc.type.Type) node.getProperty(xtc.Constants.TYPE);
    
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type.isInteger() || type.isBoolean() || type.isFloat() || type.isNumber();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    return content.getChild(0).getChild(1);
  }
  
  private Type getRefType() {
    return ptrType.getElementTypes().get(0);
  }
  
  private BitVectorType getOffType() {
    return ptrType.getElementTypes().get(1).asBitVectorType();
  }
  
  private ArrayExpression updateMemoryState(Expression memory, Expression lval, Expression rval) {
    Preconditions.checkArgument(memory.getType().equals(memType));
    Preconditions.checkArgument(lval.getType().equals(ptrType));
    Preconditions.checkArgument(rval.getType().equals(ptrType) || rval.getType().equals(scalarType));
    
    ExpressionManager em = getExpressionManager();
    
    // Compose the cell value with rval
    Expression cellVal = null;
    if(isScalarType(lval.getNode())) {
      cellVal = em.construct(scalarConstr, rval);
    } else {
      if(rval.isBitVector()) {
        assert(rval.isConstant() 
            && Integer.parseInt(rval.getNode().getString(0)) == 0);
        rval = ((PointerExpressionEncoding) getExpressionEncoding())
            .getPointerEncoding().nullPtr();
      }
      cellVal = em.construct(ptrConstr, rval);
    }
    
    return memory.asArray().update(lval, cellVal);    
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
}
