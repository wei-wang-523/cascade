package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;

import xtc.tree.Node;
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
 * Keep an array for the current active view of a bunch of cells.
 * char *q; int *p = (int *)q; 
 * *p = 10; 
 * scalarView[p] = $IntegerT;
 * 
 * @author Wei
 *
 */

public class BurstallVer3MemoryModel extends AbstractBurstallMemoryModel {
  protected static final String DEFAULT_VIEW_VARIABLE_NAME = "view";
  protected static final String DEFAULT_VIEW_STATE_TYPE = "viewType";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallVer3MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallVer3MemoryModel(encoding);
  }

  private final TupleType ptrType; // tuple (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // cell type
  private final ArrayType allocType; // Array refType offType
  private final ArrayType scalarViewType; 
  private final ArrayType ptrViewType;
  private final TupleType viewType;
  private RecordType memType; // Record type w/ multiple array types
  private TupleType stateType;
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private final Map<String, ArrayExpression> viewVars;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;

  private BurstallVer3MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    this.viewVars = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    scalarType = exprManager.bitVectorType(size);
    
    ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    refType = ptrType.getElementTypes().get(0);
    offType = ptrType.getElementTypes().get(1).asBitVectorType();
    
    ArrayType scalarArrayType = exprManager.arrayType(ptrType, scalarType);
    ArrayType ptrArrayType = exprManager.arrayType(ptrType, ptrType);
    
    scalarViewType = exprManager.arrayType(ptrType, scalarArrayType);
    ptrViewType = exprManager.arrayType(ptrType, ptrArrayType);
    viewType = exprManager.tupleType(DEFAULT_VIEW_STATE_TYPE, scalarViewType, ptrViewType);
    
    allocType = exprManager.arrayType(refType, offType);
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), elemNames, elemTypes);
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType, viewType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    RecordExpression memory = updateMemState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc, state.getChild(2));
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0); 
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion);
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
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
    return getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    RecordExpression mem = state.getChild(0).asRecord();
    TupleExpression view = state.getChild(2).asTuple();
    
    RecordExpression memPrime = updateMemState(mem, lval, rval);
    Expression viewPrime = updateView(mem, view, lval);
    
    TupleExpression statePrime = getUpdatedState(state, memPrime, state.getChild(1), viewPrime);
    
    memType = memPrime.getType();
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
    xtc.type.Type pType = (xtc.type.Type) p.getNode().getProperty(TYPE);
    String typeName = getTypeName(pType);
    
    if(currentMemElems.containsKey(typeName)) {
      ArrayExpression tgtArray = currentMemElems.get(typeName).asArray();
      if(!hasView(p.getNode())) {
        return tgtArray.index(p);
      } else {
        Expression viewState = state.getChild(2);
        Expression scalarViewState = viewState.asTuple().index(0);
        Expression ptrViewState = viewState.asTuple().index(1);
        if(scalarType.equals(tgtArray.getType().getElementType())) {
          ArrayExpression viewArr = scalarViewState.asArray().index(p).asArray();
          return viewArr.index(p);
        } else {
          ArrayExpression viewArr = ptrViewState.asArray().index(p).asArray();
          return viewArr.index(p);
        }
      }
    } else {
      CellKind kind = getCellKind(pType);
      ArrayExpression tgtArray = null;
      if(CellKind.SCALAR.equals(kind)) {
        ArrayType arrType = em.arrayType(ptrType, scalarType);
        tgtArray = em.variable(typeName, arrType, false).asArray();
      } else if(CellKind.POINTER.equals(kind)){
        ArrayType arrType = em.arrayType(ptrType, ptrType);
        tgtArray = em.variable(typeName, arrType, false).asArray();
      } else {
        ArrayType arrType = em.arrayType(ptrType, em.booleanType());
        tgtArray = em.variable(typeName, arrType, false).asArray();
      }
      currentMemElems.put(typeName, tgtArray);
      Type currentMemType = getCurrentMemoryType();      
      Expression memPrime = em.record(currentMemType, currentMemElems.values());
      Expression statePrime = getUpdatedState(state, memPrime, currentAlloc, state.getChild(2));
      currentState = suspend(state, statePrime);
      return tgtArray.index(p);
    }
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression rval = null;
    xtc.type.Type lvalType = (xtc.type.Type) 
        lval.getNode().getProperty(TYPE);
    CellKind kind = getCellKind(lvalType);
    if(CellKind.SCALAR.equals(kind)) {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    } else if(CellKind.POINTER.equals(kind)){
      rval = getExpressionEncoding().unknown();
    } else {
      rval = getExpressionEncoding().getBooleanEncoding().unknown();
    }
    
    RecordExpression memory = updateMemState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1), state.getChild(2));
    
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

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, state.getChild(2));
    currentState = suspend(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = (xtc.type.Type) content.getNode()
        .getProperty(TYPE);
    while(type.isAlias() || type.isAnnotated()) {
      type = type.resolve();
      type = type.deannotate();
    }
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
    Expression viewVar = exprManager.variable(DEFAULT_VIEW_VARIABLE_NAME, 
        viewType, true);
    return exprManager.tuple(stateType, memVar, allocVar, viewVar);
  }
  
  @Override
  public RecordType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  public void setStateType(TupleType stateType) {
    this.stateType = stateType;
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        if(!isState(expr)) {
          // For non-tuple expression evaluation
          Map<String, Expression> memElems = getMemElems(memory.getChild(0));
          List<Expression> oldArgs = Lists.newLinkedList();
          List<Expression> newArgs = Lists.newLinkedList();
          for(String typeName : viewVars.keySet()) {
            if(memElems.containsKey(typeName)) {
              oldArgs.add(viewVars.get(typeName));
              newArgs.add(memElems.get(typeName));
            }
          }
          Expression exprPrime = expr.subst(memoryVar.getChildren(), memory.getChildren());
          if(!oldArgs.isEmpty())
            exprPrime = exprPrime.subst(oldArgs, newArgs);
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
          
          return exprManager.tuple(expr.getType(), memPrime, allocPrime, memory.getChild(2));
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
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime, @param viewPrime 
   * and create a new state type if state type is changed from the type of state
   * @return a new state
   */
  @Override
  public TupleExpression getUpdatedState(Expression state, Expression... elems) {
    Preconditions.checkArgument(elems.length == 3);
    Expression memoryPrime = elems[0];
    Expression allocPrime = elems[1];
    Expression viewPrime = elems[2];
    
    ExpressionManager em = getExpressionManager();
    Type stateTypePrime = null;
    
    Type memType = state.getType().asTuple().getElementTypes().get(0);
    
    if(state != null && memType.equals(memoryPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType(), viewPrime.getType());
    }
    
    // update viewPrime
    Map<String, Expression> prevMemElemsMap = getMemElems(state.getChild(0));
    Map<String, Expression> currentMemElemsMap = getMemElems(memoryPrime);
    List<Expression> oldElems = Lists.newLinkedList();
    List<Expression> newElems = Lists.newLinkedList();
    for(String elemName : prevMemElemsMap.keySet()) {
      Expression oldElem = prevMemElemsMap.get(elemName);
      Expression newElem = currentMemElemsMap.get(elemName);
      if(!oldElem.equals(newElem)) {
        oldElems.add(oldElem);
        newElems.add(newElem);
      }
    }
    if(!oldElems.isEmpty())
      viewPrime = viewPrime.subst(oldElems, newElems);
    
    return em.tuple(stateTypePrime, memoryPrime, allocPrime, viewPrime);
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
  
  private RecordExpression updateMemState(Expression memState, Expression lval, Expression rval) { 
    currentMemElems.putAll(getMemElems(memState));
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    boolean isMemUpdated = false;
    String lvalTypeName = getTypeName(lvalType);
    if(currentMemElems.containsKey(lvalTypeName)) { // previously declared variable
      CellKind kind = getCellKind(lvalType);
      if(CellKind.POINTER.equals(kind)) {
        if(!ptrType.equals(rval.getType())) {
          // for assign null to pointer int* ptr = 0;
          assert(rval.isConstant() 
              && Integer.parseInt(rval.getNode().getString(0)) == 0);
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
      } else if(CellKind.TEST_VAR.equals(kind)) {
        rval= getExpressionEncoding().castToBoolean(rval);        
      }
      tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
    } else { // newly type name
      isMemUpdated = true;
      CellKind kind = getCellKind(lvalType);
      ArrayType arrType = null;
      if(CellKind.TEST_VAR.equals(kind)) {
        arrType = em.arrayType(ptrType, em.booleanType());
        rval = getExpressionEncoding().castToBoolean(rval);
      } else if(CellKind.SCALAR.equals(kind)) {
        arrType = em.arrayType(ptrType, scalarType);
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
  
  private Expression updateView(RecordExpression memState, TupleExpression viewState, 
      Expression indexExpr) {
    if(!hasView(indexExpr.getNode()))  return viewState;
    xtc.type.Type indexType = (xtc.type.Type) 
        indexExpr.getNode().getProperty(TYPE);
    String indexTypeName = getTypeName(indexType);
    
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);
    ExpressionManager em = getExpressionManager();
    CellKind kind = getCellKind(indexType);
    
    if(CellKind.SCALAR.equals(kind)) {
      Expression newView = getViewVar(indexTypeName, scalarType);
      scalarViewState = scalarViewState.asArray().update(indexExpr, newView);
    } else if(CellKind.POINTER.equals(kind)){
      Expression newView = getViewVar(indexTypeName, ptrType);
      ptrViewState = ptrViewState.asArray().update(indexExpr, newView);
    }
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }

  private boolean hasView(Node node) {
    Preconditions.checkArgument(node.hasProperty(TYPE));
    CellKind kind = getCellKind((xtc.type.Type) node.getProperty(TYPE));
    return CellKind.SCALAR.equals(kind);
  }
  
  private ArrayExpression getViewVar(String typeName, Type elemType) {
    if(viewVars.containsKey(typeName))  return viewVars.get(typeName);
    
    ArrayExpression elemArr = getExpressionManager()
        .arrayVar(typeName, ptrType, elemType, false);
    viewVars.put(typeName, elemArr);
    return elemArr;
  }
}
