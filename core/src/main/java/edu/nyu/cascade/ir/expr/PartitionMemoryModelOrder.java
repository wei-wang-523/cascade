package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
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
import edu.nyu.cascade.util.Pair;

/**
 * Partition memory mode, with a multiple memory arrays for multiple
 * variables. These arrays map a pointer to actual cell, where cell type 
 * is union of pointer type and scalar type. We also have a default
 * Merge Array, whenever an alias relation is detected among two arrays
 * by pointer assignment, just put both of them into the Merge Array.
 * However, currently, we have no clue how to merge arrays based on smtlib.
 *  
 * @author Wei
 *
 */

public class PartitionMemoryModelOrder extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelOrder create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelOrder(encoding);
  }
  
  private BitVectorType addrType, cellType;
  private RecordType memType, allocType; // with multiple array types
  private TupleType stateType;
  
  // Keep track of stack variables and allocated heap regions
  private final Map<Pair<String, String>, Expression> lvals, heapRegions;
  private final Set<Expression> stackRegions; // track the stack region variable
  private final Map<String, ArrayExpression> currentMemElems, currentAllocElems;
  
  private AliasAnalysis analyzer = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });
  
  private PartitionMemoryModelOrder(ExpressionEncoding encoding) {
    super(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.cellType = exprManager.bitVectorType(size);
    this.addrType = exprManager.bitVectorType(size);
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNames, elemTypes);
    this.allocType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE), 
        elemNames, elemTypes);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType, addrType);
    
    this.lvals = Maps.newLinkedHashMap();
    this.heapRegions = Maps.newLinkedHashMap();
    this.stackRegions = Sets.newHashSet();
    
    this.currentMemElems = Maps.newLinkedHashMap();
    this.currentAllocElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));

    ExpressionManager em = getExpressionManager();
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar region_var = analyzer.getAllocRegion(ptr_var);
    
    final String regionName = region_var.getName();
    Expression region = em.variable(regionName, addrType, false);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    region_var.getType().mark(regionNode);
    final String regionScope = region_var.getScope();
    regionNode.setProperty(CType.SCOPE, regionScope);
    region.setNode(regionNode);
    
    // For dynamic memory allocation, add to the end
    heapRegions.put(Pair.of(regionName, regionScope), region);
    
    { /* Add newly allocated region array to current memory elements */
      Iterable<String> elemNames = state.getChild(0).asRecord().getType().getElementNames();
      boolean definedRegionVar = Iterables.any(elemNames, new Predicate<String>() {
      	@Override
      	public boolean apply(String elemName) {
      		return elemName.contains(regionName) && elemName.contains(regionScope);
      	}
      });
      
      if(!definedRegionVar) {
        Type cellType = getArrayElemType(region_var.getType());
        ArrayType arrType = em.arrayType(addrType, cellType);
        String regionArrName = getMemArrElemName(region_var);
        ArrayExpression regionArr = em.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
      
    RecordExpression memory = updateMemoryState(state.getChild(0), ptr, region);
    RecordExpression alloc = updateAllocState(state.getChild(1), region, size);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc, state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    Expression alloc = updateAllocState(state.getChild(1), ptr, 
        getExpressionManager().bitVectorZero(cellType.getSize()));
    
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc, state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1), state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    
    // Initialization
    if(currentMemElems.isEmpty() || state != prevDerefState) {
      initCurrentMemElems(state.getChild(0));
      prevDerefState = state;
    }
    
    ExpressionManager em = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getMemArrElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName);
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type cellType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression pArray = em.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      String memTypePrime = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
      Type currentMemType = getRecordTypeFromMap(memTypePrime, currentMemElems);
      Expression memPrime = em.record(currentMemType, currentMemElems.values());
      Expression allocPrime = updateAllocState(state.getChild(1));
      Expression statePrime = getUpdatedState(state, memPrime, allocPrime, state.getChild(2));
      setCurrentState(state, statePrime);    
    }
    return pValCell;
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Expression rval = getExpressionEncoding().getIntegerEncoding().unknown(); 
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1), state.getChild(2));
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public Expression createLval(String prefix, Node node) {
    Preconditions.checkArgument(node.hasName("PrimaryIdentifier") 
        || node.hasName("SimpleDeclarator"));
    ExpressionManager exprManager = getExpressionManager();
    String name = node.getString(0);
    String scope = CType.getScope(node);
    VariableExpression res = exprManager.variable(prefix+name, addrType, true);
    lvals.put(Pair.of(name, scope), res);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar ptr_var = loadRepVar(ptr.getNode());
    analyzer.heapAssign(ptr_var, CType.getType(ptr.getNode()));
    AliasVar region_var = analyzer.getAllocRegion(ptr_var);
    
    String regionName = region_var.getName();
    Expression region = exprManager.variable(regionName, addrType, false);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    xtc.type.Type regionType = region_var.getType();
    regionType.mark(regionNode);
    String regionScope = region_var.getScope();
    regionNode.setProperty(CType.SCOPE, regionScope);
    region.setNode(regionNode);
    
    heapRegions.put(Pair.of(regionName, regionScope), region); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, region);
    Expression currentAlloc = updateAllocState(state.getChild(1), region, size);
    Expression lastRegion = state.getChild(2);
    
    String allocArrName = getSizeArrElemName(region_var);
    assert currentAllocElems.containsKey(allocArrName);
    ArrayExpression allocArr = currentAllocElems.get(allocArrName);
    
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression regionBound = exprManager.plus(addrType.getSize(), region, size);
    Expression lastRegionBound = exprManager.plus(addrType.getSize(), 
        lastRegion, allocArr.index(lastRegion));
    
    BooleanExpression res = exprManager.implies(
    		region.neq(nullPtr),
        exprManager.and(
            exprManager.lessThan(region, regionBound), // not overflow
            exprManager.or(
                lastRegion.eq(nullPtr), // last region is null (not allocated)
                exprManager.lessThanOrEqual(lastRegionBound, ptr) // larger than the last allocated region
                )));
    
    lastRegion = exprManager.ifThenElse(region.neq(nullPtr), region, lastRegion); // update last region

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, lastRegion);
    setCurrentState(state, statePrime);
    
    return res;
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = CType.getType(content.getNode());
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.resolve();
      type = type.deannotate();
    }
    if(type.isArray() || type.isStruct() || type.isUnion())
      return content;
    else
      return content.getChild(1);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      initCurrentMemElems(state.getChild(0));
      initCurrentAllocElems(state.getChild(1));
      
      ExpressionManager exprManager = getExpressionManager();
      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      
      ImmutableMap<AliasVar, Set<AliasVar>> map = analyzer.snapshot();
      for(AliasVar repVar : map.keySet()) {
        String repVarMemArrName = getMemArrElemName(repVar);
        
        /* If the repVar is referred in the execution paths */
        if(!currentMemElems.containsKey(repVarMemArrName)) continue;
        
        /* Categorize vars into stVar, stReg, and hpReg */
        Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(repVar);
        Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);
        
        /* Unsound allocation encoding: just pick an order and assert that
         * the lvals and regions are allocated in that order. 
         */
        
        /* All the stack vars are ordered */
        Iterator<Expression> stVarsItr = Iterables.get(varSets, 0).iterator();
        Expression stackBound = null;
        
        if( stVarsItr.hasNext() ) {
        	stackBound = stVarsItr.next();
        }

        while (stVarsItr.hasNext()) {
          Expression stVal2 = stVarsItr.next();
          builder.add(exprManager.greaterThan(stackBound, stVal2));   
          stackBound = stVal2;
        }
        
        String allocArrName = getSizeArrElemName(repVar);
        
        if(currentAllocElems.containsKey(allocArrName)) {            
          ArrayExpression allocArr = currentAllocElems.get(allocArrName);
          
          /* The soundness of stack regions */
          
          /* The upper bound of the stack region won't overflow */
          Iterable<Expression> stRegs = Iterables.get(varSets, 1);
          for (Expression region : stRegs) {
            Expression regionSize = allocArr.index(region);
            BitVectorExpression regionBound = exprManager.plus(addrType
                .getSize(), region, regionSize);
            
            builder.add(exprManager.greaterThan(regionBound, region));
          }
          
          /* All the stack regions are ordered */
          Iterator<Expression> stRegsItr = Iterables.get(varSets, 1).iterator();
          if( stackBound == null && stRegsItr.hasNext() ) {
          	stackBound = stRegsItr.next();
          }
          
          while (stRegsItr.hasNext()) {
            Expression stReg = stRegsItr.next();
            Expression stRegBound = exprManager.plus(addrType.getSize(), 
            		stReg, allocArr.index(stReg));
            builder.add(exprManager.greaterThan(stackBound, stRegBound));       
            stackBound = stReg;
          }
          
          if(stackBound != null) {            
            Expression lastRegion = state.getChild(2);
            
            // lastRegionBound = lastRegion != 0 ? lastRegion + Alloc[lastRegion] : 0;
            Expression heapBound = exprManager.ifThenElse(
                lastRegion.neq(nullPtr),
                exprManager.plus(addrType.getSize(), lastRegion, allocArr.index(lastRegion)),
                nullPtr);
            
            builder.add(exprManager.greaterThan(stackBound, heapBound));
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
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    return exprManager.tuple(stateType, memVar, allocVar, nullPtr);
  }
  
  @Override
  public RecordType getMemoryType() {
    return memType;
  }
  
  @Override
  public RecordType getAllocType() {
    return allocType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  @Override
  public boolean setStateType(Type stateType) {
  	Preconditions.checkArgument(stateType.isTuple());
  	if(this.stateType.equals(stateType))	return false;
    this.stateType = stateType.asTuple();
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
    this.allocType = stateType.asTuple().getElementTypes().get(1).asRecord();
    return true;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
//    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
//        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        if(!isState(expr)) {
          // For non-tuple expression evaluation
          Expression exprPrime = expr;
          
          /* Substitute the memory of expr */
          Expression memVar_mem = memoryVar.getChild(0);
          Expression memory_mem = memory.getChild(0);
          
          Map<String, ArrayExpression> memVarMemMap = getRecordElems(memVar_mem.asRecord());
          Map<String, ArrayExpression> memoryMemMap = getRecordElems(memory_mem.asRecord());
          
          List<Expression> oldArgs_mem = Lists.newLinkedList();
          List<Expression> newArgs_mem = Lists.newLinkedList();
          
          for(String name : memVarMemMap.keySet()) {
            if(memoryMemMap.containsKey(name)) {
              oldArgs_mem.add(memVarMemMap.get(name));
              newArgs_mem.add(memoryMemMap.get(name));
            }
          }
          
          if(!oldArgs_mem.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs_mem, newArgs_mem);
            oldArgs_mem.clear(); newArgs_mem.clear();
          }
          
          /* Substitute the alloc of expr */
          Expression memVar_alloc = memoryVar.getChild(1);
          Expression memory_alloc = memory.getChild(1);
          
          Map<String, ArrayExpression> memVarAllocMap = getRecordElems(memVar_alloc.asRecord());
          Map<String, ArrayExpression> memoryAllocMap = getRecordElems(memory_alloc.asRecord());
          
          List<Expression> oldArgs_alloc = Lists.newLinkedList();
          List<Expression> newArgs_alloc = Lists.newLinkedList();
          
          for(String name : memVarAllocMap.keySet()) {
            if(memoryAllocMap.containsKey(name)) {
              oldArgs_alloc.add(memVarAllocMap.get(name));
              newArgs_alloc.add(memoryAllocMap.get(name));
            }
          }
          
          if(!oldArgs_alloc.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs_alloc, newArgs_alloc);
            oldArgs_alloc.clear(); newArgs_alloc.clear();
          }
          
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_alloc = memory.getChild(1);
          Expression expr_mem = expr.getChild(0);
          Expression expr_alloc = expr.getChild(1);
          Expression memPrime = memory_mem, allocPrime = memory_alloc;
          
          if(!memory_mem.getType().equals(expr_mem.getType())){
            /* Substitute the memory of expr to memPrime */
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
            memPrime = exprManager.record(expr_mem_type, elemMap.values());
          }

          if(!memory_alloc.getType().equals(expr_alloc.getType())){
            /* Substitute the alloc of expr to memPrime */
            RecordType expr_alloc_type = expr_alloc.getType().asRecord();
          
            /* Initialize elemMap from the expr_mem */
            Map<String, Expression> elemMap = Maps.newLinkedHashMap();
          
            Iterator<String> nameItr = expr_alloc_type.getElementNames().iterator();
            Iterator<? extends Expression> elemItr = expr_alloc.getChildren().iterator();
            while(nameItr.hasNext() && elemItr.hasNext()) {
              String name = nameItr.next();
              Expression elem = elemItr.next();
              elem = elem.subst(memoryVar.getChild(0), memory_mem);
              elem = elem.subst(memoryVar.getChild(1), memory_alloc);
              elemMap.put(name, elem);
            }
          
            allocPrime = exprManager.record(expr_alloc_type, elemMap.values());
          }
          
          Expression last_region = expr.getChild(2);
          Expression last_regionPrime = last_region
              .subst(memoryVar.getChild(0), memory_mem)
              .subst(memoryVar.getChild(1), memory_alloc);
          
          /* Update stateType -- static member of memory model */
          setStateType(expr.getType().asTuple());
          
          return exprManager.tuple(expr.getType(), memPrime, allocPrime, last_regionPrime);
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
    currentAllocElems.clear();
    currentState = null;
  }

  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShort());
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
                  
      /* Find related heap regions and alloc array */
      AliasVar pRepVar = loadRepVar(ptr.getNode());
      AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
      Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
      
      Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);
      
      /* Get the related alloc array */
      initCurrentAllocElems(state.getChild(1));
      String allocArrName = getSizeArrElemName(ptr2RepVar);
      assert currentAllocElems.containsKey(allocArrName);
      ArrayExpression allocArr = currentAllocElems.get(allocArrName);
      
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */
      Iterable<Expression> stVars = Iterables.get(varSets, 0);
      for( Expression stVar : stVars)    disjs.add(ptr.eq(stVar));
      
      // In any stack region
      Iterable<Expression> stRegs = Iterables.get(varSets, 1);
      for(Expression region : stRegs) {
        Expression regionSize = allocArr.index(region);
        
        BitVectorExpression regionBound = exprManager.plus(addrType
            .getSize(), region, regionSize);
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
      
      // In any heap region
      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
      for( Expression region : hpRegs ) {
        Expression regionSize = allocArr.index(region);        
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
            region, regionSize);
        disjs.add(
            exprManager.and(
                region.neq(nullPtr),
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      
      /* Find related heap regions and alloc array */
      AliasVar pRepVar = loadRepVar(ptr.getNode());
      AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
      Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
      Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);

      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      /* Get the related alloc array */
      initCurrentAllocElems(state.getChild(1));
      String allocArrName = getSizeArrElemName(ptr2RepVar);
      assert currentAllocElems.containsKey(allocArrName);
      ArrayExpression allocArr = currentAllocElems.get(allocArrName);
      
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */ 
      Iterable<Expression> stVars = Iterables.get(varSets, 0);
      for( Expression stVar : stVars)    
        disjs.add(exprManager.and(ptr.eq(stVar), size.eq(sizeZro)));
      
      // In any stack region
      Iterable<Expression> stRegs = Iterables.get(varSets, 1);
      for(Expression region : stRegs) {
        Expression regionSize = allocArr.index(region);
        BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
      
      // In any heap region
      Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
      for( Expression region : hpRegs ) {
        Expression regionSize = allocArr.index(region);
        BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(),
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(),
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                region.neq(nullPtr), 
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    return valid_malloc(state, ptr, size, false);
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    /* Find related heap regions and alloc array */
    AliasVar pRepVar = loadRepVar(ptr.getNode());
    AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
    
    initCurrentAllocElems(state.getChild(1));
    String allocArrName = getSizeArrElemName(ptr2RepVar);
    assert currentAllocElems.containsKey(allocArrName);
    ArrayExpression allocArr = currentAllocElems.get(allocArrName);
    
    ExpressionManager exprManager = getExpressionManager();
    Expression size = allocArr.index(ptr);
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    return expr;
  }
  
  private RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    return updateRecord(memState.asRecord(), lval, rval, true);
  }
  
  private RecordExpression updateAllocState(Expression allocState, Expression lval, Expression rval) {
    return updateRecord(allocState.asRecord(), lval, rval, false);
  }
  
  private RecordExpression updateAllocState(Expression allocState) {
  	Preconditions.checkArgument(allocState.isRecord());
    Map<String, ArrayExpression> map = getRecordElems(allocState);
    int preSize = map.size();
    map.putAll(currentAllocElems);
    
    if(map.size() > preSize) { // type changed
    	String recordTypeName = Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
    	RecordType recordPrimeType = getRecordTypeFromMap(recordTypeName, map);
    	return getExpressionManager().record(recordPrimeType, map.values());
    } else {
    	if(!map.isEmpty()) // content changed
    		return getExpressionManager().record(allocState.getType(), map.values());
    	else
    		return allocState.asRecord();
    }    
  }
  
  private RecordExpression updateRecord(RecordExpression record, Expression lval, Expression rval, boolean mem) {
    Map<String, ArrayExpression> map = mem ? currentMemElems : currentAllocElems;
    boolean stateTypeChanged = !map.isEmpty();
    map.putAll(getRecordElems(record));
    
    ExpressionManager em = getExpressionManager();

    AliasVar lvalRepVar = loadRepVar(lval.getNode());    
    String lvalRepArrName = mem ? getMemArrElemName(lvalRepVar) : getSizeArrElemName(lvalRepVar);
    
    if(map.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = map.get(lvalRepArrName);
//      Type cellType = lvalRepArr.getType().getElementType();
//      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      map.put(lvalRepArrName, lvalRepArr);
    } else {
      xtc.type.Type lvalRepType = lvalRepVar.getType();
      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
//      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      map.put(lvalRepArrName, lvalArr);
      stateTypeChanged = true;
    }
    
    Type recordTypePrime = record.getType();
    
    if(stateTypeChanged) {
      String recordTypeName = mem ? Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE) :
      	Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
      recordTypePrime = getRecordTypeFromMap(recordTypeName, map);
    }
    return em.record(recordTypePrime, map.values());
  }
  
  /**
   * Get representative alias variable in the pointer analyzer
   * @param gnode
   */
  private AliasVar getRepVar(GNode gnode) {
    xtc.type.Type type = CType.getType(gnode);
    String scope = CType.getScope(gnode);
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
      String scope = CType.getScope(gnode);
      Pair<GNode, String> key = Pair.of(gnode, scope);
      return cache.get(key);
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  /**
   * Get the cell tyoe of the array in memory record for node with @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type resType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     resType = cellType; break;
    case ARRAY : 
    case POINTER :  
    case STRUCTORUNION : resType = addrType; break;
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return resType;
  }
  
  private void initCurrentMemElems(Expression memState) {
    Preconditions.checkArgument(memState.isRecord());
    currentMemElems.putAll(getRecordElems(memState.asRecord()));
  }
  
  private void initCurrentAllocElems(Expression allocState) {
    Preconditions.checkArgument(allocState.isRecord());
    currentAllocElems.putAll(getRecordElems(allocState.asRecord()));
  }
  
  private ImmutableList<ImmutableList<Expression>> getCategorizedVars(
      Iterable<AliasVar> equivVars) {
    ImmutableList.Builder<Expression> stVarsBuilder, stRegsBuilder, hpRegsBuilder;
    stVarsBuilder = new ImmutableList.Builder<Expression>();
    stRegsBuilder = new ImmutableList.Builder<Expression>();
    hpRegsBuilder = new ImmutableList.Builder<Expression>();
 
    for(AliasVar var : equivVars) {
      String varName = var.getName();
      String varScope = var.getScope();
      Pair<String, String> varKey = Pair.of(varName, varScope);
      if(CType.CONSTANT.equals(varName)) continue;
      if(lvals.containsKey(varKey)) {
        Expression expr = lvals.get(varKey);
        if(stackRegions.contains(expr)) {
          stRegsBuilder.add(expr);
        } else {
          stVarsBuilder.add(expr);
        }
      } else if(heapRegions.containsKey(varKey)) {
        hpRegsBuilder.add(heapRegions.get(varKey));
      } else {
        IOUtils.out().println("Variable " + varName + " @" + var.getScope() + " not yet be analyzed");
      }
    }
    
    ImmutableList.Builder<ImmutableList<Expression>> builder = 
        new ImmutableList.Builder<ImmutableList<Expression>>();
    builder.add(stVarsBuilder.build());
    builder.add(stRegsBuilder.build());
    builder.add(hpRegsBuilder.build());
    return builder.build();
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
  
  /**
   * Get the valid allocated assumption
   * @param allocated: indicate whether this method is called inside allocated. If true, the ptr node is
   * actually the region node, otherwise, the ptr node is like m[ptr], whose source node is ptr node
   * we need analyzer to get the points to node.
   */
  private BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size, boolean allocated) {
    ExpressionManager exprManager = getExpressionManager();

    /* Find related heap regions and alloc array */
    AliasVar pRepVar = loadRepVar(ptr.getNode());
    if(!allocated) pRepVar = analyzer.getPointsToRepVar(pRepVar);
    
    Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(pRepVar);
    List<Expression> regions = Lists.newArrayListWithCapacity(Iterables.size(equivAliasVars));  
    
    for(AliasVar var : equivAliasVars) {
      Pair<String, String> varKey = Pair.of(var.getName(), var.getScope());
      if(heapRegions.containsKey(varKey)) {
        regions.add(heapRegions.get(varKey));
      }
    }
    
    initCurrentAllocElems(state.getChild(1));
    String allocArrName = getSizeArrElemName(pRepVar);
    assert currentAllocElems.containsKey(allocArrName);
    ArrayExpression allocArr = currentAllocElems.get(allocArrName);
    
    Expression lastRegion = state.getChild(2);
    Expression lastRegionBound = exprManager.plus(addrType.getSize(), 
        lastRegion, allocArr.index(lastRegion));
    
    Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    
    BooleanExpression res = exprManager.implies(
        ptr.neq(nullPtr),
        exprManager.and(
            exprManager.lessThan(ptr, ptrBound), // not overflow
            exprManager.or(
                lastRegion.eq(nullPtr), // last region is null (not allocated)
                exprManager.lessThanOrEqual(lastRegionBound, ptr)  // larger than the last allocated region
                )));
    
    lastRegion = exprManager.ifThenElse(ptr.neq(nullPtr), ptr, lastRegion); // update last region
    Expression statePrime = exprManager.tuple(getStateType(), state.getChild(0), state.getChild(1), lastRegion);
    setCurrentState(state, statePrime);

    return res;
  }
}
