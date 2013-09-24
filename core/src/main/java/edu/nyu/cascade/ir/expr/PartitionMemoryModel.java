package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.type.StructOrUnionT;
import xtc.type.VariableT;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

/**
 * Monolithic memory mode, with a multiple memory arrays for multiple
 * variables. These arrays map a pointer to actual cell, where cell type 
 * is union of pointer type and scalar type. We also have a default
 * Merge Array, whenever an alias relation is detected among two arrays
 * by pointer assignment, just put both of them into the Merge Array.
 * However, currently, we have no clue how to merge arrays based on smtlib.
 *  
 * @author Wei
 *
 */

public class PartitionMemoryModel extends AbstractMonoMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModel(encoding);
  }

  private static final String ARRAY_PREFIX = "arr_of_";

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // const type
  
  private final ArrayType allocType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final InductiveType mixType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  
  private AliasAnalysis analyzer = null;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });

  private PartitionMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.scalarType = exprManager.bitVectorType(size);
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, scalarType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    /* Create datatype */
    this.mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
    
    this.refType = ptrType.getElementTypes().get(0);
    this.offType = ptrType.getElementTypes().get(1).asBitVectorType();
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNames, elemTypes);
    this.allocType = exprManager.arrayType(refType, offType);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
    
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    
    this.currentMemElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));

    ExpressionManager em = getExpressionManager();
    
    Expression refVar = em.variable(Identifiers.uniquify(REGION_VARIABLE_NAME), refType, false);
    Expression offZero = em.bitVectorZero(offType.getSize());
    // locVar: (region_x, 0)
    Expression locVar = em.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    /* Update memory state */
    initCurrentMemElems(state.getChild(0));
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar region_var = analyzer.getPointsToLoc(ptr_var);
    { /* Add newly allocated region array to current memory elements */
      String regionArrName = getArrayElemName(region_var);
      if(!currentMemElems.containsKey(regionArrName)) {
        Type cellType = getArrayElemType(region_var.getType());
        ArrayType arrType = em.arrayType(ptrType, cellType);
        ArrayExpression regionArr = em.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
    
    { /* Update the pointer array in current memory elements */  
      String ptrRepArrName = getArrayElemName(ptr_var);
      if(currentMemElems.containsKey(ptrRepArrName)) {
        ArrayExpression ptrRepArr = currentMemElems.get(ptrRepArrName).asArray();
        Type cellType = ptrRepArr.getType().getElementType();
        locVar = castExprToCell(locVar, cellType);
        ptrRepArr = ptrRepArr.update(ptr, locVar);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      } else {
        xtc.type.Type ptrRepVarType = ptr_var.getType();
        CellKind ptrRepVarKind = CType.getCellKind(ptrRepVarType);
        
        Type cellType = CellKind.POINTER.equals(ptrRepVarKind) ? ptrType : scalarType;
        ArrayType arrType = em.arrayType(ptrType, cellType);
        ArrayExpression ptrRepArr = em.variable(ptrRepArrName, arrType, false).asArray();
        assert(cellType.equals(locVar.getType()));
        ptrRepArr = ptrRepArr.update(ptr, locVar);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      }
    } 
    
    Type currentMemType = getCurrentMemoryType();
    
    RecordExpression memory = em.record(currentMemType, currentMemElems.values());
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
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));

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
        Expression off_bound = exprManager.plus(offType.getSize(), off_ptr, size);
        
        Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
        Expression sizeVar = alloc.asArray().index(refVar);
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        disjs.add(
            exprManager.and(
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
    
    ExpressionManager em = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getArrayElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName).asArray();
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type cellType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = em.arrayType(ptrType, cellType);
      ArrayExpression pArray = em.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      Type currentMemType = getCurrentMemoryType();
      Expression memPrime = em.record(currentMemType, currentMemElems.values());
      if(currentAlloc == null)    currentAlloc = state.getChild(1);
      Expression statePrime = getUpdatedState(state, memPrime, currentAlloc);
      currentState = suspend(state, statePrime);    
    }
    
    if(mixType.equals(pValCell.getType())) {
      CellKind kind = CType.getCellKind(CType.unwrapped((xtc.type.Type) p.getNode().getProperty(TYPE)));
      assert(CellKind.POINTER.equals(kind) || CellKind.SCALAR.equals(kind));
      if(CellKind.POINTER.equals(kind)) {
        pValCell = em.select(ptrSel, pValCell);
      } else {
        pValCell = em.select(scalarSel, pValCell);
      }
    }
    return pValCell;
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    Expression rval = null;
    
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = CType.getCellKind(lvalType);
    
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
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar repVar = loadRepVar(ptr.getNode());
    analyzer.heapAssign(repVar, (xtc.type.Type) ptr.getNode().getProperty(TYPE));
    IOUtils.debug().pln(analyzer.displaySnapShort());
    
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
    Preconditions.checkArgument(content.getNode().hasProperty(TYPE));
    
    if(Kind.APPLY.equals(content.getKind())) {
      return content.getChild(0).getChild(1);
    } else {
      xtc.type.Type contentType = (xtc.type.Type) (content.getNode().getProperty(TYPE));
      CellKind kind = CType.getCellKind(contentType);
      switch(kind) {
      case STRUCTORUNION: 
      case ARRAY:   return content;
      default: return content.getChild(1);
      }
    }
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
        throw new UnsupportedOperationException("--order-alloc is not supported in this memory model");
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
    Iterable<String> elemNames_1 = pickFieldNames(memType_1.getElementNames());
    
    RecordType memType_0 = mem_0.getType();
    final Iterable<String> elemNames_0 = pickFieldNames(memType_0.getElementNames());
    
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
    
    Iterable<String> elemNames_1_prime = recomposeFieldNames(arrName_1, commonElemNames);
    Iterable<String> elemNames_0_prime = recomposeFieldNames(arrName_0, commonElemNames);
    Iterator<String> elemNames_1_prime_itr = elemNames_1_prime.iterator();
    Iterator<String> elemNames_0_prime_itr = elemNames_0_prime.iterator();
    
    while(elemNames_1_prime_itr.hasNext() && elemNames_0_prime_itr.hasNext()) {
      String elemName_1 = elemNames_1_prime_itr.next();
      String elemName_0 = elemNames_0_prime_itr.next();
      Expression elem = em.ifThenElse(guard, mem_1.select(elemName_1), mem_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    final String arrName = Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME);
    Iterable<String> elemNames = recomposeFieldNames(arrName, commonElemNames);
    
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
    
    Iterable<String> elemNames = recomposeFieldNames(arrName, currentMemElems.keySet());
    
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
    Iterable<String> elemNames = mem.getType().getElementNames();
    Iterable<String> fieldNames = pickFieldNames(elemNames);
    assert(Iterables.size(elemNames) == Iterables.size(fieldNames));
    Iterator<String> elemNameItr = elemNames.iterator();
    Iterator<String> fieldNameItr = fieldNames.iterator();
    while(elemNameItr.hasNext() && fieldNameItr.hasNext()) {
      String elemName = elemNameItr.next();
      String fieldName = fieldNameItr.next();
      Expression value = mem.select(elemName);
      currentMemElems.put(fieldName, value);
    }
  }
  
  @Override
  protected RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    initCurrentMemElems(memState);
    
    ExpressionManager em = getExpressionManager();
    boolean memTypeChanged = false;

    AliasVar lvalRepVar = loadRepVar(lval.getNode());
    xtc.type.Type lvalRepType = lvalRepVar.getType();
    
    String lvalRepArrName = getArrayElemName(lvalRepVar);
    if(currentMemElems.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = currentMemElems.get(lvalRepArrName).asArray();
      Type cellType = lvalRepArr.getType().getElementType();
      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalRepArr);
    } else {
      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(ptrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalArr);
      memTypeChanged = true;
    }
    
    Type currentMemType = memTypeChanged ? getCurrentMemoryType() : memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  @Override
  public Expression castExpression(Expression state, Expression src, xtc.type.Type type) {
    if(type.isPointer() && src.isBitVector()) {
      return ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr();
    }
    return src;
  }
  
  /**
   * Get representative alias variable in the pointer analyzer
   * @param gnode
   * @return
   */
  private AliasVar getRepVar(GNode gnode) {
    Preconditions.checkArgument(gnode.hasProperty(TYPE) && gnode.hasProperty(SCOPE));
    
    xtc.type.Type type = (xtc.type.Type) gnode.getProperty(TYPE);
    String scope = gnode.getStringProperty(SCOPE);
    String refName = CType.getReferenceName(type);
    
    AliasVar repVar = analyzer.getRepVar(refName, scope, type);
    if(repVar.isNullLoc()) {
      throw new NullPointerException("null pointer reference of " + type.getShape());
    }
    return repVar;
  }
  
  /**
   * Load representative alias variable from cache
   * @param gnode
   */
  private AliasVar loadRepVar(GNode gnode) {
    try {
      String scope = gnode.getStringProperty(SCOPE);
      Pair<GNode, String> key = Pair.of(gnode, scope);
      return cache.get(key);
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  private enum ElemType {
    SCALAR,
    POINTER,
    MIX
  }
  
  private ElemType getElemType(xtc.type.Type type) {
    Preconditions.checkArgument(CellKind.STRUCTORUNION.equals(CType.getCellKind(type)));
    StructOrUnionT su = CType.unwrapped(type).toStructOrUnion();
    boolean scalar = true, pointer = true;
    for(VariableT v : su.getMembers()) {
      switch(CType.getCellKind(v)) {
      case SCALAR :         pointer = false; break;
      case POINTER:         scalar = false; break;
      // FIXME: struct { int a[100] }, get the mix types?
      case ARRAY:
      case STRUCTORUNION:   scalar = false; pointer = false; break;
      default:              throw new IllegalArgumentException("Unsupported type " + v);
      }
    }
    assert(!(pointer && scalar));
    if(pointer)         return  ElemType.POINTER;
    else if(scalar)     return  ElemType.SCALAR;
    else                return  ElemType.MIX;
  }
  
  private Expression castExprToCell(Expression rval, Type cellType) {
    if(rval.getType().equals(cellType)) return rval;
    else {
      ExpressionManager em = getExpressionManager();
      assert(scalarType.equals(rval.getType()) || ptrType.equals(rval.getType()));
      if(scalarType.equals(rval.getType())) {
        if(ptrType.equals(cellType)) {
          xtc.type.Type type = (xtc.type.Type) rval.getNode().getProperty(TYPE);
          assert(type.hasConstant());
          if(type.getConstant().bigIntValue().intValue() == 0) {
            rval = ((PointerExpressionEncoding) getExpressionEncoding())
                .getPointerEncoding().nullPtr();
          } else {
            rval = getExpressionEncoding().unknown();
          }
        } else { // mixType
          rval = em.construct(scalarConstr, rval);
        }
      } else {
        assert(mixType.equals(cellType));
        rval = em.construct(ptrConstr, rval);
      }
      return rval;
    }
  }
  
  private String getArrayElemName(AliasVar var) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_PREFIX).append(var.getName()).append('_').append(var.getScope());
    return Identifiers.toValidId(sb.toString());
  }
  
  /**
   * Get the cell tyoe of the array in memory record for node with certain type
   * @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type cellType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     cellType = scalarType; break;
    case ARRAY : {
      xtc.type.Type contentType = CType.unwrapped(type).toArray().getType();
      cellType = getArrayElemType(contentType);
      break;
    }
    case POINTER :  cellType = ptrType; break;
    case STRUCTORUNION : {
      ElemType elemType = getElemType(type);
      switch(elemType) {
      case SCALAR:  cellType = scalarType; break;
      case POINTER: cellType = ptrType; break;
      default:      cellType = mixType; 
      }
      break;
    }
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return cellType;
  }
  
  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShort());
  }
}
