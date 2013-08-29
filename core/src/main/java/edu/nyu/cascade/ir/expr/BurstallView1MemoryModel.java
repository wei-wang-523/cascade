package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Iterator;

import xtc.tree.Node;
import xtc.type.*;

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
 * Keep an array of array to array for record alias relations.
 * char *q; int *p = (int *)q; 
 * scalarView[$Integer] = scalarView[$CharT];
 * *p = 10; 
 * scalarView[scalarView[$IntegerT]] = $IntegerT; 
 * scalarView[$IntegerT] = $IntegerT
 * 
 * @author Wei
 *
 */

public class BurstallView1MemoryModel extends AbstractBurstallMemoryModel {
  protected static final String DEFAULT_VIEW_VARIABLE_NAME = "view";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_VIEW_STATE_TYPE = "viewType";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallView1MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallView1MemoryModel(encoding);
  }

  private final TupleType ptrType; // tuple (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // off type
  private final ArrayType allocType; // Array refType offType
  private final TupleType viewType;
  private RecordType memType; // Record type w/ multiple array types
  private TupleType stateType;
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private final Map<String, ArrayExpression> typeArrVarInView;
  private Expression currentAlloc = null;
  private Expression currentView = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private BurstallView1MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    this.typeArrVarInView = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    scalarType = exprManager.bitVectorType(size);
    
    ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    refType = ptrType.getElementTypes().get(0);
    offType = ptrType.getElementTypes().get(1).asBitVectorType();
    
    
    ArrayType scalarArrayType = exprManager.arrayType(ptrType, scalarType);
    ArrayType ptrArrayType = exprManager.arrayType(ptrType, ptrType);
    
    ArrayType scalarViewType = exprManager.arrayType(ptrType, 
        exprManager.arrayType(scalarArrayType, scalarArrayType));
    ArrayType ptrViewType = exprManager.arrayType(ptrType, 
        exprManager.arrayType(ptrArrayType, ptrArrayType));
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
    Expression viewState = initializeViewState(state.getChild(2), ptr, locVar);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc, viewState);
    
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
    Expression ptrView = initializeViewState(state.getChild(2), ptr);
    return getUpdatedState(state, state.getChild(0), alloc, ptrView);
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
    xtc.type.Type lvalType = unwrapped(
        (xtc.type.Type) lval.getNode().getProperty(TYPE));
    viewPrime = updateViewState(viewPrime, lvalType, rval);
    
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
    if(currentAlloc == null)  currentAlloc = state.getChild(1);
    if(currentView == null)    currentView = state.getChild(2);
    
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
        ArrayExpression viewArr = null;
        Type elemType = tgtArray.getType().getElementType();
        assert(scalarType.equals(elemType) || ptrType.equals(elemType));
        if(scalarType.equals(elemType)) {
          viewArr = scalarViewState.asArray().index(p).asArray();
        } else {
          viewArr = ptrViewState.asArray().index(p).asArray();
        }
        return viewArr.index(tgtArray).asArray().index(p);
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
      Expression statePrime = getUpdatedState(state, memPrime, currentAlloc, currentView);
      currentState = suspend(state, statePrime);
      return tgtArray.index(p);
    }
  }
  
  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression rval = null;
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
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
    Expression ptrView = initializeViewState(state.getChild(2), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, ptrView);
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
          Map<String, Expression> memElems = getMemElems(memory.getChild(0));
          List<Expression> oldArgs = Lists.newLinkedList();
          List<Expression> newArgs = Lists.newLinkedList();
          for(String typeName : typeArrVarInView.keySet()) {
            if(memElems.containsKey(typeName)) {
              oldArgs.add(typeArrVarInView.get(typeName));
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
          Expression memory_view = memory.getChild(2);
          
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
            elem = elem.subst(memoryVar.getChild(2), memory_view);
            elemMap.put(name, elem);
          }
          
          Expression memPrime = memory_mem;
          if(!elemMap.isEmpty()) memPrime = exprManager.record(expr_mem_type, elemMap.values());
          
          /* Substitute the alloc of expr to allocPrime */
          
          Expression alloc = expr.getChild(1);
          Expression allocPrime = alloc;
          if(alloc.isVariable()) { // substitution makes no effect for variable
            assert(alloc.equals(memoryVar.getChild(1)));
            allocPrime = memory.getChild(1);
          } else {
            allocPrime = allocPrime.subst(memoryVar.getChild(0), memory_mem);
            allocPrime = allocPrime.subst(memoryVar.getChild(1), memory_alloc);
            allocPrime = allocPrime.subst(memoryVar.getChild(2), memory_view);
          }
          
          /* Substitute the view of expr to viewPrime */
          
          Expression view = expr.getChild(2);
          Expression viewPrime = view;
          viewPrime = viewPrime.subst(memoryVar.getChild(0), memory_mem);
          viewPrime = viewPrime.subst(memoryVar.getChild(1), memory_alloc);
          viewPrime = viewPrime.subst(memoryVar.getChild(2), memory_view);
          
          /* Update memType, allocType and stateType -- static member of memory model */
          memType = memPrime.getType().asRecord();
          stateType = expr.getType().asTuple();
          
          return exprManager.tuple(expr.getType(), memPrime, allocPrime, viewPrime);
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
    currentView = null;
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
  
  @Override
  public Expression castExpression(Expression state, Expression src, xtc.type.Type targetType) {
    Preconditions.checkArgument(
        getCellKind(
            (xtc.type.Type) src.getNode().getProperty(TYPE))
            .equals(getCellKind(targetType)));
    //FIXME: scalar type has same cell size in this model, ignore cast cast
    if(CellKind.POINTER.equals(getCellKind(targetType))) {
      // Initialization
      if(currentMemElems.isEmpty() || state != prevDerefState) {
        currentMemElems.putAll(getMemElems(state.getChild(0)));
        prevDerefState = state;
      }
      if(currentAlloc == null)  currentAlloc = state.getChild(1);
      if(currentView == null)    currentView = state.getChild(2);
      
      Type currentMemType = getCurrentMemoryType();
      Expression memPrime = getExpressionManager().record(currentMemType, currentMemElems.values());
      Expression viewPrime = updateViewState(currentView, unwrapped(targetType), src);     
      TupleExpression statePrime = getUpdatedState(state,
          memPrime, currentAlloc, viewPrime);
      currentState = suspend(state, statePrime);
    }
    return src;
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
          assert(rval.isConstant());
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
      } else if(CellKind.BOOL.equals(kind)) {
        rval= getExpressionEncoding().castToBoolean(rval);        
      }
      tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
    } else { // newly type name
      isMemUpdated = true;
      CellKind kind = getCellKind(lvalType);
      ArrayType arrType = null;
      if(CellKind.BOOL.equals(kind)) {
        arrType = em.arrayType(ptrType, em.booleanType());
        rval = getExpressionEncoding().castToBoolean(rval);
      } else if(CellKind.SCALAR.equals(kind)) {
        arrType = em.arrayType(ptrType, scalarType);
      } else {
        arrType = em.arrayType(ptrType, ptrType);
        if(!ptrType.equals(rval.getType())) {
          assert(rval.isConstant());
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
  
  /**
   * Initialize @param viewState with allocate statement
   * @param lval = malloc(...). The region assign to lval is
   * @param rval; and structure declare statement with @param
   * lval == null
   */
  private Expression initializeViewState(Expression viewState, Expression rval) {
    return initializeViewState(viewState, null, rval);
  }
  
  private Expression initializeViewState(Expression viewState, Expression lval, Expression rval) {
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);
    
    Expression startAddr = rval;
    xtc.type.Type regionType = null;
    if(lval != null) {
      xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
      assert(CellKind.POINTER.equals(getCellKind(lvalType)));
      regionType = unwrapped(unwrapped(lvalType).toPointer().getType());
    } else {
      regionType = unwrapped((xtc.type.Type) rval.getNode().getProperty(TYPE));
    }
    
    ExpressionManager em = getExpressionManager();
    if(regionType.isStruct()) {
      Map<String, Type> elemTypes = getElemTypeOfStructUnionField(regionType);
      Map<String, Expression> elemOffsets = getOffsetOfStructField(regionType);
      for(Entry<String, Expression> entry : elemOffsets.entrySet()) {
        String elemArrName = entry.getKey();
        Expression elemOffset = entry.getValue();
        Expression indexExpr = getExpressionEncoding().plus(startAddr, elemOffset);
        if(scalarType.equals(elemTypes.get(elemArrName))) { //
          Expression scalarView = scalarViewState.asArray().index(indexExpr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
          scalarView = scalarView.asArray().update(elemArr, elemArr);
          scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
        } else {
          Expression ptrView = ptrViewState.asArray().index(indexExpr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
          ptrView = ptrView.asArray().update(elemArr, elemArr);
          ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
        }
      } 
    } else if(regionType.isUnion()) { 
      Map<String, Type> elemTypes = getElemTypeOfStructUnionField(regionType);
      Map<String, Integer> elemTypeSizes = getSizeOfUnionField(regionType);
      // FIXME: to find the minimal type elem to be the View, or the maximal one?
      int minTypeSize = Integer.MAX_VALUE;
      String viewTypeName = null;
      for(String elemName : elemTypeSizes.keySet()) {
        int elemTypeSize = elemTypeSizes.get(elemName);
        if(minTypeSize > elemTypeSize) {
          minTypeSize = elemTypeSize; 
          viewTypeName = elemName;
        }
      }
      
      boolean isAllScalarType = Iterables.all(elemTypes.values(), new Predicate<Type>(){
        @Override
        public boolean apply(Type argType) {
          return scalarType.equals(argType);
        }
      });
      
      boolean isAllPtrType = Iterables.all(elemTypes.values(), new Predicate<Type>(){
        @Override
        public boolean apply(Type argType) {
          return ptrType.equals(argType);
        }
      });
      
      if(isAllScalarType) {
        ArrayExpression viewArr = getTypeArrVar(viewTypeName, scalarType);
        for(Entry<String, Type> entry : elemTypes.entrySet()) {
          String elemArrName = entry.getKey();
          Expression scalarView = scalarViewState.asArray().index(startAddr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
          scalarView = scalarView.asArray().update(elemArr, viewArr);
          scalarViewState = scalarViewState.asArray().update(startAddr, scalarView);
        }
      } else if(isAllPtrType) {
        ArrayExpression viewArr = getTypeArrVar(viewTypeName, ptrType);
        for(Entry<String, Type> entry : elemTypes.entrySet()) {
          String elemArrName = entry.getKey();
          Expression ptrView = ptrViewState.asArray().index(startAddr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
          ptrView = ptrView.asArray().update(elemArr, viewArr);
          scalarViewState = scalarViewState.asArray().update(startAddr, ptrView);
        }
      } else {
        throw new ExpressionFactoryException("Don't support cast pointer to scalar type in Cascade.");
      }      
    } else { // lval point to a non-structure type
      String elemArrName = getTypeName(regionType);
      Expression indexExpr = startAddr;
      CellKind kind = getCellKind(regionType);
      if(CellKind.SCALAR.equals(kind)) {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
        Expression scalarView = scalarViewState.asArray().index(indexExpr);
        scalarView = scalarView.asArray().update(elemArr, elemArr);
        scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
      } else if(CellKind.POINTER.equals(kind)) {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
        Expression ptrView = ptrViewState.asArray().index(indexExpr);
        ptrView = ptrView.asArray().update(elemArr, elemArr);
        ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
      }
    }
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }
  
  /**
   * Update @param viewState if @param lval and @param rval are both pointers,
   * and they point to different type, otherwise, just @return viewState
   */
  private Expression updateViewState(Expression viewState, xtc.type.Type lvalType, Expression rval) {
    xtc.type.Type rvalType = unwrapped((xtc.type.Type) rval.getNode().getProperty(TYPE));
    
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);
    
    if(!(lvalType.isPointer() && rvalType.isPointer())) return viewState;
    
    xtc.type.Type lvalPtrToType = unwrapped(lvalType.toPointer().getType());
    xtc.type.Type rvalPtrToType = unwrapped(rvalType.toPointer().getType());
    if(lvalPtrToType.equals(rvalPtrToType)) return viewState;
    
    ExpressionEncoding encoding = getExpressionEncoding();
    ExpressionManager em = getExpressionManager();
    
    Map<String, Expression> lvalFieldOffset = getOffsetOfStructField(lvalPtrToType);
    Map<String, Type> lvalMemberTypeOfField = getElemTypeOfStructUnionField(lvalPtrToType);
    Map<String, Type> rvalMemberTypeOfField = getElemTypeOfStructUnionField(rvalPtrToType);
    Iterator<Entry<String, Type>> lItr = lvalMemberTypeOfField.entrySet().iterator();
    Iterator<Entry<String, Type>> rItr = rvalMemberTypeOfField.entrySet().iterator();
    while(lItr.hasNext() && rItr.hasNext()) {
      Entry<String, Type> lMember = lItr.next();
      Entry<String, Type> rMember = rItr.next();
      Type lMemberType = lMember.getValue();
      Type rMemberType = rMember.getValue();
      // TODO: to analyze more complicated structure type
      if(!lMemberType.equals(rMemberType))
        throw new ExpressionFactoryException("Inconsistent structure type pointer casting");
      Expression indexExpr = encoding.plus(rval, lvalFieldOffset.get(lMember.getKey()));
      Expression lMemberTypeArr = getTypeArrVar(lMember.getKey(), lMemberType);
      Expression rMemberTypeArr = getTypeArrVar(rMember.getKey(), rMemberType);
      if(scalarType.equals(lMemberType)) {
        Expression scalarView = scalarViewState.asArray().index(indexExpr);
        Expression viewresentative = scalarView.asArray().index(rMemberTypeArr);
        scalarView = scalarView.asArray().update(lMemberTypeArr, viewresentative);
        scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
      } else {
        Expression ptrView = ptrViewState.asArray().index(indexExpr);
        Expression viewresentative = ptrView.asArray().index(rMemberTypeArr);
        ptrView = ptrView.asArray().update(lMemberTypeArr, viewresentative);
        ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
      }
    }   
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }
  
  private Expression updateView(RecordExpression memState, TupleExpression viewState, 
      Expression indexExpr) {    
    if(!hasView(indexExpr.getNode()))  return viewState;
    
    xtc.type.Type indexType = (xtc.type.Type) 
        indexExpr.getNode().getProperty(TYPE);
    ExpressionManager em = getExpressionManager();
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);

    String indexTypeName = getTypeName(indexType);
    CellKind kind = getCellKind(indexType);
    if(CellKind.SCALAR.equals(kind)) {
      Expression scalarView = scalarViewState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, scalarType);
      Expression previousView = scalarView.asArray().index(tgtArray);
      scalarView = scalarView.asArray().update(previousView, tgtArray);
      scalarView = scalarView.asArray().update(tgtArray, tgtArray);
      scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
    } else if(CellKind.POINTER.equals(kind)) {
      Expression ptrView = ptrViewState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, ptrType);
      Expression previousView = ptrView.asArray().index(tgtArray);
      ptrView = ptrView.asArray().update(previousView, tgtArray);
      ptrView = ptrView.asArray().update(tgtArray, tgtArray);
      ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
    }
    
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }
  
  private boolean hasView(Node node) {
    CellKind kind = getCellKind((xtc.type.Type) node.getProperty(TYPE));
    if(!CellKind.SCALAR.equals(kind))    return false;
    return true;
  }
  
  /**
   * Get the member types of each field of structure type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to member types.
   */
  private Map<String, Type> getElemTypeOfStructUnionField(xtc.type.Type type) {
    Map<String, Type> elemTypes = Maps.newLinkedHashMap();
    String typeName = getTypeName(type);
    if(!(type.isStruct() || type.isUnion())) {
      CellKind kind = getCellKind(type);
      if(CellKind.SCALAR.equals(kind))
        elemTypes.put(typeName, scalarType);
      else if(CellKind.POINTER.equals(kind))
        elemTypes.put(typeName, ptrType);
    } else {
      StructOrUnionT structUnionType = type.toStructOrUnion();
      for(VariableT elem : structUnionType.getMembers()) {
        // TODO: nested structure type
        String elemName = new StringBuilder().append(typeName)
            .append('.').append(elem.getName()).toString();
        xtc.type.Type elemType = elem.getType();
        CellKind kind = getCellKind(elemType);
        if(CellKind.SCALAR.equals(kind))
          elemTypes.put(elemName, scalarType);
        else if(CellKind.POINTER.equals(kind))
          elemTypes.put(elemName, ptrType);
        else
          elemTypes.put(elemName, getExpressionManager().booleanType());
      }
    }
    return elemTypes;
  }
  
  /**
   * Get the member offset of each field of structure type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to corresponding offsets.
   */
  private Map<String, Expression> getOffsetOfStructField(xtc.type.Type type) {
    Map<String, Expression> elemOffsets = Maps.newLinkedHashMap();
    ExpressionManager em = getExpressionManager();
    ExpressionEncoding encoding = getExpressionEncoding();
    String typeName = getTypeName(type);
    int cellSize = encoding.getCellSize();
    if(!type.isStruct()) {
      Expression offsetExpr = em.bitVectorConstant(0, cellSize);
      elemOffsets.put(typeName, offsetExpr);
    } else {
      for(VariableT elem : type.toStruct().getMembers()) {
        // TODO: nested structure type
        int offset = getOffset(type.toStruct(), elem.getName());
        String elemName = new StringBuilder().append(typeName)
            .append('.').append(elem.getName()).toString();
        elemOffsets.put(elemName, 
            em.bitVectorConstant(offset, cellSize));
      }
    }
    return elemOffsets;
  }
  
  /**
   * Get the member type size of each field of union type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to corresponding offsets.
   */
  private Map<String, Integer> getSizeOfUnionField(xtc.type.Type type) {    
    Preconditions.checkArgument(type.isUnion()); 
    Map<String, Integer> elemOffsets = Maps.newLinkedHashMap();
    ExpressionEncoding encoding = getExpressionEncoding();
    xtc.type.C cAnalyzer = encoding.getCAnalyzer();
    String typeName = getTypeName(type);
    int cellSize = encoding.getCellSize();
    for(VariableT elem : type.toUnion().getMembers()) {
      String elemName = new StringBuilder().append(typeName)
          .append('.').append(elem.getName()).toString();
      int size = (int) cAnalyzer.getSize(elem.getType()) * cellSize;
      elemOffsets.put(elemName, size);
    }
    return elemOffsets;
  }
  
  private ArrayExpression getTypeArrVar(String typeName, Type elemType) {
    if(typeArrVarInView.containsKey(typeName))
      return typeArrVarInView.get(typeName);
    
    ArrayExpression elemArr = getExpressionManager()
        .arrayVar(typeName, ptrType, elemType, false);
    typeArrVarInView.put(typeName, elemArr);
    return elemArr;
  }
  
  private int getOffset(StructOrUnionT t, String name) {    
    StructOrUnionT struct = t.toStructOrUnion();
    if(struct.isUnion()) return 0;
    
    Iterator<VariableT> itr = struct.getMembers().iterator();
    int offset = 0;
    while(itr.hasNext()) {
      VariableT elem = (VariableT) itr.next();
      String elemName = elem.getName();
      if(elemName.equals(name)) {
        return offset;
      }
      int elemTypeSize = sizeofType(elem.getType());
      offset += elemTypeSize;
    }
    throw new IllegalArgumentException("Unknown offset for " + name);
  }
  
  private int sizeofType(xtc.type.Type t) {
    if (t.isInteger()) {
      return 1;
    } else if (t.isPointer()) {
      return 1;
    } else if (t.isStruct()) {
      int res = 0;
      for(VariableT elem : t.toStruct().getMembers()) {
        res += sizeofType(elem.getType());
      }
      return res;
    } else if(t.isUnion()) {
      int res = 0;
      for(VariableT elem : t.toUnion().getMembers()) {
        res = Math.max(res, sizeofType(elem.getType()));
      }
      return res;
    } else if(t.isArray()) {
      ArrayT array = t.toArray();
      return (int) (array.getLength()) * sizeofType(array.getType());
    } else if(t.isAlias() || t.isVariable()) {
      return sizeofType(t.resolve());
    } else if(t.isAnnotated()) {
      return sizeofType(t.deannotate());
    } else {
      throw new IllegalArgumentException("Unknown type.");
    }
  }
}
