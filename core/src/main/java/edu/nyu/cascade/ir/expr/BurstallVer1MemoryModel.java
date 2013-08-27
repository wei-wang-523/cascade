package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/**
 * Burstall memory model, multiple memory arrays for various type.
 * These arrays types map pointer type to either pointer type or 
 * scalar type. 
 * 
 * The state of memory is a record with multiple arrays for various 
 * types. 
 * 
 * Different type has different cell type size: CharT is 8, IntegerT 
 * and ShorT is 16, LongT is 32.
 * 
 * @author Wei
 *
 */
public class BurstallVer1MemoryModel extends AbstractBurstallMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallVer1MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallVer1MemoryModel(encoding);
  }

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final Type refType;
  private final BitVectorType offType; // offset type
  private final ArrayType allocType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;

  private BurstallVer1MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    this.refType = ptrType.getElementTypes().get(0);
    this.offType = ptrType.getElementTypes().get(1).asBitVectorType();
    this.allocType = exprManager.arrayType(refType, offType);
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), elemNames, elemTypes);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: element size and integer size don't agree: cast integer to cell type?
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    RecordExpression memory = updateMemState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    TupleExpression statePrime = getUpdatedState(state, memory, alloc);
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: element size and integer size don't agree: cast integer to cell type
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0); 
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion);
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getUpdatedState(state, state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: element size and integer size don't agree: cast integer to cell type
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    
    return getUpdatedState(state, state.getChild(0), alloc);
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
      
      for( Expression refVar : regions ) {
        Expression ref_ptr = ptr.asTuple().index(0);
        Expression off_ptr = ptr.asTuple().index(1);
        
        Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
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
    
    Expression sizeZero = exprManager.bitVectorZero(offType.getSize());
    Expression alloc = state.getChild(1);
    
    try {
      for( Expression locVar : heapRegions )
        alloc = exprManager.ifThenElse(ptr.asTuple().index(0).eq(locVar), 
            alloc.asArray().update(locVar, sizeZero), alloc);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getUpdatedState(state, state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    xtc.type.Type lType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    xtc.type.Type rType = (xtc.type.Type) rval.getNode().getProperty(TYPE);
    if(CellKind.SCALAR.equals(getCellKind(lType)) 
        && CellKind.SCALAR.equals(getCellKind(rType))) {
      int lval_size = getSizeofType(lType);
      int rval_size = getSizeofType(rType);
      if(lval_size > rval_size) {
        rval = rval.asBitVector().zeroExtend(lval_size);
      } else if(lval_size < rval_size) {
        IOUtils.debug().pln("Explicit cast is missing");
        rval = rval.asBitVector().extract(lval_size-1, 0);
      }
    }
    RecordExpression memory = updateMemState(state.getChild(0), lval, rval);
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    
    // Initialization
    if(currentMemElems.isEmpty() || state != prevDerefState) {
      currentMemElems.putAll(getMemElems(state.getChild(0)));
      prevDerefState = state;
    }
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    xtc.type.Type pType = (xtc.type.Type) p.getNode().getProperty(TYPE);
    String typeName = getTypeName(pType);
  
    if(currentMemElems.containsKey(typeName)) {
      return currentMemElems.get(typeName).asArray().index(p);
    }
    
    // Add an element to currentMemElem
    CellKind kind = getCellKind(pType);
    if(CellKind.TEST_VAR.equals(kind)) {
      ArrayType arrType = em.arrayType(ptrType, em.booleanType());
      tgtArray = em.variable(typeName, arrType, false).asArray();
    } else if(CellKind.SCALAR.equals(kind)) {
      int size = getSizeofType(pType);
      ArrayType arrType = em.arrayType(ptrType, em.bitVectorType(size));
      tgtArray = em.variable(typeName, arrType, false).asArray();
    } else {
      ArrayType arrType = em.arrayType(ptrType, ptrType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
    }
    currentMemElems.put(typeName, tgtArray);
    
    Type currentMemType = getCurrentMemoryType();
    
    Expression memPrime = em.record(currentMemType, currentMemElems.values());
    Expression statePrime = getUpdatedState(state, memPrime, currentAlloc);
    currentState = suspend(state, statePrime);
    return tgtArray.index(p);
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression rval = null;
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = getCellKind(lvalType);
    if(CellKind.SCALAR.equals(kind)) {
      int size = getSizeofType(lvalType);
      Type bvType = getExpressionManager().bitVectorType(size);
      rval = getExpressionEncoding().getIntegerEncoding().unknown(bvType);
    } else if(CellKind.TEST_VAR.equals(kind)) {
      rval = getExpressionEncoding().getBooleanEncoding().unknown();
    } else {
      rval = getExpressionEncoding().unknown();
    }
    
    RecordExpression memory = updateMemState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    
    memType = memory.getType();
    stateType = statePrime.getType();
        
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
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemState(state.getChild(0), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc);
    currentState = suspend(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = unwrapped((xtc.type.Type) content.getNode()
        .getProperty(TYPE));
    if(type.isStruct() || type.isUnion() || type.isArray())
      return content;
    else
      return content.getChild(1);
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
    Expression allocVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        allocType, true);
    return exprManager.tuple(stateType, memVar, allocVar);
  }
  
  @Override
  public RecordType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  @Override
  public void setStateType(TupleType stateType) {
    this.stateType = stateType;
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
//    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
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
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_alloc = memory.getChild(1);
          
          /* Substitute the memory of expr to memPrime */
          Expression expr_mem = expr.getChild(0);
          RecordType expr_mem_type = expr_mem.getType().asRecord();
          
          /* Initialize elemMap from the expr_mem */
          Map<String, Expression> elemMap = Maps.newLinkedHashMap();
          
          Iterator<String> nameItr = expr_mem_type.getElementNames().iterator();
          Iterator<? extends Expression> elemItr = expr_mem.getChildren().iterator();
          while(nameItr.hasNext() && elemItr.hasNext()) {
            String name = nameItr.next();
            Expression elem = elemItr.next();
            elem = elem.subst(memoryVar.getChild(0), memory_mem);
            elem = elem.subst(memoryVar.getChild(1), memory_alloc);
            elemMap.put(name, elem);
          }
          
          Expression memPrime = memory_mem;
          if(!elemMap.isEmpty()) memPrime = exprManager.record(expr_mem_type, elemMap.values());
          
          /* Substitute the alloc of expr to allocPrime */
          Expression allocPrime = null;
          
          Expression alloc = expr.getChild(1);
          if(alloc.isVariable()) { // substitution makes no effect for variable
            assert(alloc.equals(memoryVar.getChild(1)));
            allocPrime = memory.getChild(1);
          } else {
            allocPrime = alloc.subst(memoryVar.getChild(0), memory_mem);
            allocPrime = alloc.subst(memoryVar.getChild(1), memory_alloc);
          }
          
          /* Update memType, allocType and stateType -- static member of memory model */
          memType = memPrime.getType().asRecord();
          stateType = expr.getType().asTuple();
          
          return exprManager.tuple(expr.getType(), memPrime, allocPrime);
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
    currentMemElems.clear();
    currentAlloc = null;
    currentState = null;
  }
  
  @Override
  public Expression castConstant(int value, xtc.type.Type type) {
    int size = getSizeofType(type);
    return getExpressionManager().bitVectorConstant(value, size);
  }
  
  @Override
  public Expression castExpression(Expression state, Expression src, xtc.type.Type type) {
    Preconditions.checkArgument(
        getCellKind(
            (xtc.type.Type) src.getNode().getProperty(TYPE))
            .equals(getCellKind(type)));
    //TODO: ignore pointer cast for now
    if(!CellKind.SCALAR.equals(getCellKind(type)))  return src;
    int srcSize = src.getType().asBitVectorType().getSize();
    int targetSize = getSizeofType(type);
    if(srcSize < targetSize)
      return src.asBitVector().zeroExtend(targetSize);
    else
      return src.asBitVector().extract(targetSize-1, 0);
  }
  
  private Map<String, Expression> getMemElems(Expression memState) {
    Preconditions.checkArgument(memState.isRecord());
    Map<String, Expression> resMap = Maps.newLinkedHashMap();
    RecordExpression mem = memState.asRecord();
    for(String elemName : mem.getType().getElementNames()) {
      int index = elemName.indexOf('@') + 1;
      resMap.put(elemName.substring(index), mem.select(elemName));
    }
    return resMap;
  }
  
  private RecordType getCurrentMemoryType() {
    ExpressionManager em = getExpressionManager();
    
    Iterable<Type> elemTypes = Iterables.transform(currentMemElems.values(), 
        new Function<Expression, Type>(){
      @Override
      public Type apply(Expression expr) {
        return expr.getType();
      }
    });
    
    if(elemTypes == null)
      throw new ExpressionFactoryException("Update memory type failed.");
    
    final String typeName = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
    
    Iterable<String> elemNames = Iterables.transform(currentMemElems.keySet(), 
        new Function<String, String>(){
      @Override
      public String apply(String elemName) {
        int index = elemName.indexOf('@')+1;
        return typeName + '@' + elemName.substring(index);
      }
    });
    
    return em.recordType(typeName, elemNames, elemTypes);
  }
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  @Override
  public TupleExpression getUpdatedState(Expression state, Expression...elems) {
    Preconditions.checkArgument(elems.length == 2);
    Expression memoryPrime = elems[0];
    Expression allocPrime = elems[1];
    
    ExpressionManager em = getExpressionManager();
    Type stateTypePrime = null;
    
    if(state != null 
        && state.getType().asTuple().getElementTypes().get(0).equals(memoryPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType());
    }
    
    return em.tuple(stateTypePrime, memoryPrime, allocPrime);
  }
  
  private RecordExpression updateMemState(Expression memState, Expression lval, Expression rval) {
    currentMemElems.putAll(getMemElems(memState));
    ExpressionManager em = getExpressionManager();
    boolean isMemUpdated = false;
    ArrayExpression tgtArray = null;
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    String lvalTypeName = getTypeName(lvalType);
    if(currentMemElems.containsKey(lvalTypeName)) { // declared type name
      CellKind kind = getCellKind(lvalType);
      if(CellKind.TEST_VAR.equals(kind)) { // TEST_VAR_X
        rval = getExpressionEncoding().castToBoolean(rval);
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
      } else if(CellKind.POINTER.equals(kind)) {
        if(!ptrType.equals(rval.getType())) {
          // for assign null to pointer int* ptr = 0;
          assert(rval.isConstant() 
              && Integer.parseInt(rval.getNode().getString(0)) == 0);
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
      } else {
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
      }
      
    } else { // new type name
      isMemUpdated = true;
      CellKind kind = getCellKind(lvalType);
      ArrayType arrType = null;
      
      if(CellKind.TEST_VAR.equals(kind)) {
        rval = getExpressionEncoding().castToBoolean(rval);
        arrType = em.arrayType(ptrType, em.booleanType());
      } else if(CellKind.SCALAR.equals(kind)) {
        int size = getSizeofType(lvalType);
        arrType = em.arrayType(ptrType, em.bitVectorType(size));
      } else {
        arrType = em.arrayType(ptrType, ptrType);
        if(!ptrType.equals(rval.getType())) {
          assert(rval.isConstant() 
            && Integer.parseInt(rval.getNode().getString(0)) == 0);
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
            .getPointerEncoding().nullPtr();
        }
      }
      
      tgtArray = em.variable(lvalTypeName, arrType, false).asArray().update(lval, rval);
    }      
    currentMemElems.put(lvalTypeName, tgtArray);
    
    Type currentMemType = isMemUpdated? getCurrentMemoryType() : memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  private int getSizeofType(xtc.type.Type type) {
    ExpressionEncoding encoding = getExpressionEncoding();
    return (int) encoding.getCAnalyzer().getSize(type) * encoding.getCellSize();
  }
}
