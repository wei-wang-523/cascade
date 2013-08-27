package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
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
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/**
 * Monolithic memory mode, with a multiple memory arrays for multiple
 * variables. These arrays map a offset to actual cell, where cell type 
 * is union of pointer type and scalar type. We also have a default
 * Merge Array, whenever an alias relation is detected among two arrays
 * by pointer assignment, just put the (ref, array(off, cell)) into
 * the Merge Array, where ref is picked from the pointer expression,
 * array is picked from currentMemElems. However, it is very slow.
 *  
 * @author Wei
 *
 */

public class MonolithicVer2MemoryModel extends AbstractMonoMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static MonolithicVer2MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new MonolithicVer2MemoryModel(encoding);
  }
  
  private static final String CELL_TYPE_NAME = "cell";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  private static final String DEFAULT_MERGE_ARRAY_NAME = "mergeArray";

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // const type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
  private final InductiveType cellType;
  private final ArrayType mergeArrType;
  
  private final ArrayType allocType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final Set<String> mergedArrayNames;
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;

  private MonolithicVer2MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.mergedArrayNames = Sets.newHashSet();
    this.currentMemElems = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.scalarType = exprManager.bitVectorType(size);
    
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    this.refType = ptrType.getElementTypes().get(0);
    this.offType = ptrType.getElementTypes().get(1).asBitVectorType();
    this.allocType = exprManager.arrayType(refType, offType);
    
    this.scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, scalarType);
    this.scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    this.ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    this.ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);
    
    /* Create datatype for cell */
    this.cellType = exprManager.dataType(CELL_TYPE_NAME, scalarConstr, ptrConstr);
    
    List<String> elemNames = Lists.newArrayList(DEFAULT_MERGE_ARRAY_NAME);
    // Array ref (Array int cell)
    this.mergeArrType = exprManager.arrayType(refType, exprManager.arrayType(scalarType, cellType));
    List<? extends Type> elemTypes = Lists.newArrayList(mergeArrType);
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), elemNames, elemTypes);
    
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
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
    
    RecordExpression memory = updateMemoryState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    TupleExpression statePrime = getUpdatedState(state, memory, alloc);
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
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
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
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
      initCurrentMemElems(state.getChild(0));
      prevDerefState = state;
    }
    
    Expression pValCell = null;
    Expression pRef = p.asTuple().index(0);
    Expression pOff = p.asTuple().index(1);
    
    if(isInMergeArray(p)) {
      pValCell = currentMemElems.get(DEFAULT_MERGE_ARRAY_NAME).asArray()
          .index(pRef).asArray().index(pOff);
    } else {
      String pArrName = getArrName(p);
      if(currentMemElems.containsKey(pArrName)) {
        pValCell = currentMemElems.get(pArrName).asArray().index(pOff);
      } else { // Add an element to currentMemElem
        ExpressionManager em = getExpressionManager();
        ArrayType arrType = em.arrayType(scalarType, cellType);
        ArrayExpression pArray = em.variable(pArrName, arrType, false).asArray();
        currentMemElems.put(pArrName, pArray);
        
        Type currentMemType = getCurrentMemoryType();
        Expression memPrime = em.record(currentMemType, currentMemElems.values());
        if(currentAlloc == null)    currentAlloc = state.getChild(1);
        Expression statePrime = getUpdatedState(state, memPrime, currentAlloc);
        currentState = suspend(state, statePrime);    
        pValCell = pArray.index(pOff);
      }
    }
    
    xtc.type.Type pType = (xtc.type.Type) p.getNode().getProperty(TYPE);
    CellKind kind = getCellKind(pType);
    assert (CellKind.SCALAR.equals(kind) || CellKind.POINTER.equals(kind));
    if(CellKind.POINTER.equals(kind)) {
      return pValCell.asInductive().select(ptrSel);
    } else {
      return pValCell.asInductive().select(scalarSel);
    }
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    Expression rval = null;
    
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = getCellKind(lvalType);
    assert (CellKind.SCALAR.equals(kind) || CellKind.POINTER.equals(kind));
    if(CellKind.POINTER.equals(kind)) {
      rval = getExpressionEncoding().unknown();
    } else {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    }
    
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval); 
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
    Preconditions.checkArgument(size.getType().equals( offType) );
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, refType, true);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc);
    currentState = suspend(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    Preconditions.checkArgument(content.getArity() == 1);
    Preconditions.checkArgument(cellType.equals(content.getChild(0).getType()));
    Preconditions.checkArgument(content.getChild(0).getArity() == 2);
    Preconditions.checkArgument(scalarType.equals(content.getChild(0).getChild(1).getType()));
    Expression value = content.getChild(0).getChild(1);
    Expression pointer = value.getChild(0);
    return pointer;
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
          
          Expression memPrime = exprManager.record(expr_mem_type, elemMap.values());
          
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
  
  public Expression combinePreMemoryStates(BooleanExpression guard, 
      RecordExpression mem_1, RecordExpression mem_0) {    
    
    RecordType memType_1 = mem_1.getType();
    Iterable<String> elemNames_1 = Iterables.transform(memType_1.getElementNames(),
        new Function<String, String>() {
      @Override
      public String apply(String elemName) {
        return elemName.substring(elemName.indexOf('@')+1);
      }
    });
    
    RecordType memType_0 = mem_0.getType();
    final Iterable<String> elemNames_0 = Iterables.transform(memType_0.getElementNames(),
        new Function<String, String>() {
      @Override
      public String apply(String elemName) {
        return elemName.substring(elemName.indexOf('@')+1);
      }
    });
    
    Iterable<String> commonElemNames = Iterables.filter(elemNames_1, 
        new Predicate<String>(){
      @Override
      public boolean apply(String elemName) {
        return Iterables.contains(elemNames_0, elemName);
      }
    });
    
    List<Expression> elems = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    List<Type> elemTypes = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    
    ExpressionManager em = getExpressionManager();
    final String arrName_1 = memType_1.getName();
    final String arrName_0 = memType_0.getName();
    
    for(String elemName : commonElemNames) {
      String elemName_1 = arrName_1 + '@' + elemName;
      String elemName_0 = arrName_0 + '@' + elemName;
      Expression elem = em.ifThenElse(guard, mem_1.select(elemName_1), mem_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    final String arrName = Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME);
    Iterable<String> elemNames = Iterables.transform(commonElemNames, 
        new Function<String, String>(){
      @Override
      public String apply(String elemName) {
        return elemName + '@' + arrName;
      }
    });
    
    RecordType recordType = em.recordType(Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME), 
        elemNames, elemTypes);
    Expression res = em.record(recordType, elems);
    
    return res;
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
    
    final String arrName = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
    
    Iterable<String> elemNames = Iterables.transform(currentMemElems.keySet(), 
        new Function<String, String>(){
      @Override
      public String apply(String elemName) {
        int index = elemName.indexOf('@')+1;
        return arrName + '@' + elemName.substring(index);
      }
    });
    
    return em.recordType(arrName, elemNames, elemTypes);
  }
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  public TupleExpression getUpdatedState(Expression state, Expression memoryPrime, Expression allocPrime) {
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
  
  private void initCurrentMemElems(Expression memState) {
    Preconditions.checkArgument(memState.isRecord());
    RecordExpression mem = memState.asRecord();
    for(String elemName : mem.getType().getElementNames()) {
      int index = elemName.indexOf('@') + 1;
      currentMemElems.put(elemName.substring(index), mem.select(elemName));
    }
  }
  
  @Override
  protected RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {   
    initCurrentMemElems(memState);
    
    String lvalArrName = getArrName(lval);
    String rvalArrName = getArrName(rval);
    
    Expression lvalRef = lval.asTuple().index(0);
    Expression lvalOff = lval.asTuple().index(1);
    
    ExpressionManager em = getExpressionManager();
    boolean memTypeChanged = false;
    
    ArrayExpression mergeArray = currentMemElems.get(DEFAULT_MERGE_ARRAY_NAME).asArray();
    
    // if either is in merged array, both should be merged
    if(isInMergeArray(lval) || isInMergeArray(rval)) {
      if(!isInMergeArray(lval)) {
        if(currentMemElems.containsKey(lvalArrName)) {
          ArrayExpression lvalArr = currentMemElems.remove(lvalArrName).asArray();
          memTypeChanged = true;
          mergeArray = mergeArray.update(lvalRef, lvalArr); 
        }
        if(lvalArrName != null)  mergedArrayNames.add(lvalArrName);
      }
      
      if(!isInMergeArray(rval)) {
        if(currentMemElems.containsKey(rvalArrName)) {
          ArrayExpression rvalArr = currentMemElems.remove(rvalArrName).asArray();
          memTypeChanged = true;
          Expression rvalRef = rval.asTuple().index(0);
          mergeArray = mergeArray.update(rvalRef, rvalArr); 
        }
        if(rvalArrName != null)  mergedArrayNames.add(rvalArrName);
      }
      
      Expression rvalInCell = castRvalToLvalType(lval, rval);
      mergeArray = mergeArray.update(lvalRef, mergeArray.index(lvalRef).asArray()
          .update(lvalOff, rvalInCell));
      currentMemElems.put(DEFAULT_MERGE_ARRAY_NAME, mergeArray);
      
    } else { // none of then is in the currentMemElems
      
      xtc.type.Type rvalType = (xtc.type.Type) rval.getNode().getProperty(TYPE);
      CellKind kind = getCellKind(rvalType);
      assert (CellKind.SCALAR.equals(kind) || CellKind.POINTER.equals(kind));
      if(CellKind.POINTER.equals(kind)) { // okay, alias occurs, merge them into merge array        
        if(currentMemElems.containsKey(lvalArrName)) {
          ArrayExpression lvalArr = currentMemElems.remove(lvalArrName).asArray();
          memTypeChanged = true;
          mergeArray = mergeArray.update(lvalRef, lvalArr);
        }     
        if(lvalArrName != null)  mergedArrayNames.add(lvalArrName);
        
        if(currentMemElems.containsKey(rvalArrName)) {
          ArrayExpression rvalArr = currentMemElems.remove(rvalArrName).asArray();
          memTypeChanged = true;
          Expression rvalRef = rval.asTuple().index(0);
          mergeArray = mergeArray.update(rvalRef, rvalArr);
        }     
        if(rvalArrName != null)  mergedArrayNames.add(rvalArrName);
        
        Expression rvalInCell = castRvalToLvalType(lval, rval);
        mergeArray = mergeArray.update(lvalRef, mergeArray.index(lvalRef).asArray()
            .update(lvalOff, rvalInCell));
        currentMemElems.put(DEFAULT_MERGE_ARRAY_NAME, mergeArray);
        
      } else { // don't bother merge array
        if(currentMemElems.containsKey(lvalArrName)) {
          Expression rvalInCell = castRvalToLvalType(lval, rval);
          ArrayExpression lvalArr = currentMemElems.get(lvalArrName).asArray()
              .update(lvalOff, rvalInCell);
          currentMemElems.put(lvalArrName, lvalArr);
        } else {
          Expression rvalInCell = castRvalToLvalType(lval, rval);
          ArrayType arrType = em.arrayType(scalarType, cellType);
          ArrayExpression lvalArr = em.variable(lvalArrName, arrType, false).asArray();
          lvalArr = lvalArr.update(lvalOff, rvalInCell);
          currentMemElems.put(lvalArrName, lvalArr);
          memTypeChanged = true;
        }
      }
    }
    
    Type currentMemType = memTypeChanged ? getCurrentMemoryType() : memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  private String getArrName(Expression expr) {
    String resName = null;
    if(expr.isTuple()) {
      assert(expr.getType().equals(ptrType));
      Expression refExpr = expr.getChild(0);
      if(refExpr.isVariable()) {
        resName = refExpr.asVariable().getName();
      } else {
        if(Kind.TUPLE_INDEX.equals(refExpr.getKind())) {
          Expression arrExpr = refExpr.getChild(0).getChild(0);
          if(arrExpr.isVariable()) {
            resName = arrExpr.asVariable().getName();
          }
        } else if(Kind.ARRAY_INDEX.equals(refExpr.getKind())) {
          Expression arrExpr = refExpr.getChild(0);
          if(arrExpr.isVariable()) {
            resName = arrExpr.asVariable().getName();
          } else {
            resName = DEFAULT_MERGE_ARRAY_NAME;
          }
        }
      }
    }
    return resName == null ? resName : resName.replace("addr", "array");
  }
  
  private boolean isInMergeArray(Expression e) {
    String arrName = getArrName(e);
    if(DEFAULT_MERGE_ARRAY_NAME.equals(arrName))    return true;
    if(mergedArrayNames.contains(arrName))          return true;
    return false;
  }
  
  private Expression castRvalToLvalType(Expression lval, Expression rval) {
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(xtc.Constants.TYPE);
    CellKind lvalKind = getCellKind(lvalType);
    xtc.type.Type rvalType = (xtc.type.Type) rval.getNode().getProperty(xtc.Constants.TYPE);
    CellKind rvalKind = getCellKind(rvalType);
    
    if(lvalKind.equals(rvalKind)) {
      if(CellKind.POINTER.equals(rvalKind))
        return ptrConstr.apply(rval);
      else
        return scalarConstr.apply(rval);
    } else if(CellKind.POINTER.equals(lvalKind) && CellKind.SCALAR.equals(rvalKind)) {
      return ptrConstr.apply(getNullExpr(rval));
    } else {
      throw new IllegalArgumentException("Assign pointer " + rval + " to constant " + lval);
    }
  }
  
  private Expression getNullExpr(Expression e) {
    Preconditions.checkArgument(e.isConstant() && e.isBitVector()
        && Integer.parseInt(e.getNode().getString(0)) == 0);
    return ptrConstr.apply(((PointerExpressionEncoding) getExpressionEncoding())
        .getPointerEncoding().nullPtr());
  }
}
