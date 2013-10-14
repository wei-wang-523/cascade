package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CTypeNameAnalyzer;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.TypeCastAnalysis;
import edu.nyu.cascade.ir.IRVarInfo;
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
 * Keep an array for the current active view of a bunch of cells.
 * char *q; int *p = (int *)q; 
 * *p = 10; 
 * scalarView[p] = $IntegerT;
 * 
 * @author Wei
 *
 */

public class BurstallView2MemoryModel extends AbstractMemoryModel {
  protected static final String DEFAULT_VIEW_VARIABLE_NAME = "view";
  protected static final String DEFAULT_VIEW_STATE_TYPE = "viewType";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallView2MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallView2MemoryModel(encoding);
  }

  private final TupleType ptrType; // tuple (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // cell type
  private final ArrayType sizeArrType; // Array refType offType
  private final ArrayType scalarViewType; 
  private final ArrayType ptrViewType;
  private final TupleType viewType;
  private RecordType memType; // Record type w/ multiple array types
  private TupleType stateType;
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, ArrayExpression> currentMemElems;
  private final Map<String, ArrayExpression> viewVars;
  
  private TypeCastAnalysis analyzer = null;
  private ArrayExpression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;

  private BurstallView2MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    this.viewVars = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    scalarType = exprManager.bitVectorType(size);
    
    ptrType = encoding.getPointerEncoding().getType();
    refType = ptrType.getElementTypes().get(0);
    offType = ptrType.getElementTypes().get(1).asBitVectorType();
    
    ArrayType scalarArrayType = exprManager.arrayType(ptrType, scalarType);
    ArrayType ptrArrayType = exprManager.arrayType(ptrType, ptrType);
    
    scalarViewType = exprManager.arrayType(ptrType, scalarArrayType);
    ptrViewType = exprManager.arrayType(ptrType, ptrArrayType);
    viewType = exprManager.tupleType(DEFAULT_VIEW_STATE_TYPE, scalarViewType, ptrViewType);
    
    sizeArrType = exprManager.arrayType(refType, offType);
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), elemNames, elemTypes);
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType, viewType);
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
    Expression view = updateViewWithMem(state, memory, state.getChild(2));
    TupleExpression statePrime = getUpdatedState(state, memory, alloc, view);
    
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
      Expression nullRef = getExpressionEncoding().getPointerEncoding().getNullPtr().getChild(0);
      
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
      Expression nullRef = getExpressionEncoding().getPointerEncoding().getNullPtr().getChild(0);
      
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
          "--order-alloc is not supported in burstall memory model");
    } 
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
      Expression alloc = state.getChild(1);
      
      ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
      
      Expression nullPtr = getExpressionEncoding().getPointerEncoding().getNullPtr();
      Expression nullRef = nullPtr.getChild(0);
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
    Expression nullPtr = getExpressionEncoding().getPointerEncoding().getNullPtr();
    return exprManager.or(exprManager.eq(ptr, nullPtr), exprManager.greaterThan(size, 
        exprManager.bitVectorZero(offType.getSize())));
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType )); 
    Expression sizeZero = getExpressionManager().bitVectorZero(offType.getSize());
    Expression alloc = state.getChild(1).asArray().update(ptr, sizeZero);
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
    viewPrime = updateViewWithMem(state, memPrime, viewPrime);
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
      currentMemElems.putAll(getRecordElems(state.getChild(0)));
      prevDerefState = state;
    }
    if(currentAlloc == null)    currentAlloc = state.getChild(1).asArray();
    
    ExpressionManager em = getExpressionManager();
    xtc.type.Type pType = CType.getType(p.getNode());
    String typeName = CTypeNameAnalyzer.getTypeName(pType);
    
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
      CellKind kind = CType.getCellKind(pType);
      ArrayExpression tgtArray = null;
      switch(kind) {
      case SCALAR:
        tgtArray = em.variable(
            typeName, em.arrayType(ptrType, scalarType), false).asArray();
        break;
      case POINTER:
        tgtArray = em.variable(
            typeName, em.arrayType(ptrType, ptrType), false).asArray();
        break;
      case BOOL: 
        tgtArray = em.variable(
            typeName, em.arrayType(ptrType, em.booleanType()), false).asArray();
        break;
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
      currentMemElems.put(typeName, tgtArray);
      Type memPrimeType = getRecordTypeFromMap(
      		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
      Expression memPrime = em.record(memPrimeType, currentMemElems.values());
      Expression viewPrime = updateViewWithMem(state, memPrime, state.getChild(2));
      Expression statePrime = getUpdatedState(state, memPrime, currentAlloc, viewPrime);
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
    CellKind kind = CType.getCellKind(CType.getType(lval.getNode()));
    switch(kind) {
    case SCALAR:
      rval = getExpressionEncoding().getIntegerEncoding().unknown(); break;
    case POINTER:
      rval = getExpressionEncoding().getPointerEncoding().unknown(); break;
    case BOOL:
      rval = getExpressionEncoding().getBooleanEncoding().unknown(); break;
    default:
      throw new IllegalArgumentException("Invalid kind " + kind);
    }
    
    RecordExpression memory = updateMemState(state.getChild(0), lval, rval); 
    Expression viewPrime = updateViewWithMem(state, memory, state.getChild(2));
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1), viewPrime);
    
    memType = memory.getType();
    stateType = statePrime.getType();
        
    return statePrime;
  }
  
  @Override
  public Expression createLval(Expression state, String name,
      IRVarInfo varInfo, Node node) {
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
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1).asArray();
    currentAlloc = currentAlloc.asArray().update(refVar, size);
    Expression viewPrime = updateViewWithMem(state, currentMem, state.getChild(2));
    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, viewPrime);
    currentState = suspend(state, statePrime);
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = CType.getType(content.getNode());
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
    if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      /* No comparable predicate defined in uninterpreted type */
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in burstall memory model");
    }
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        ExpressionManager exprManager = getExpressionManager();
        
        { /* The disjointness of stack variables, and != nullRef*/
          Expression nullRef = getExpressionEncoding().getPointerEncoding().getNullPtr().getChild(0);
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
        sizeArrType, true);
    Expression viewVar = exprManager.variable(DEFAULT_VIEW_VARIABLE_NAME, 
        viewType, true);
    return exprManager.tuple(stateType, memVar, allocVar, viewVar);
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
    return true;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
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
          
          Map<String, ArrayExpression> memVarMemMap = getRecordElems(memVar_mem);
          Map<String, ArrayExpression> memoryMemMap = getRecordElems(memory_mem);
          
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
          
          exprPrime = exprPrime.subst(memVar_alloc, memory_alloc);
          
          /* Substitute the view of expr */
          List<Expression> oldArgs = Lists.newLinkedList();
          List<Expression> newArgs = Lists.newLinkedList();
          for(String typeName : viewVars.keySet()) {
            if(memoryMemMap.containsKey(typeName)) {
              oldArgs.add(viewVars.get(typeName));
              newArgs.add(memoryMemMap.get(typeName));
            }
          }
          
          if(!oldArgs.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs, newArgs);
            oldArgs.clear(); newArgs.clear();
          }
          
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
          
          /* Update memType, sizeArrType and stateType -- static member of memory model */
          setStateType(expr.getType());
          
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
  
  @Override
  public Expression substSizeArr(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, sizeArrType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(offType.getSize()), sizeArrType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
  }

	@Override
	public void setTypeCastAnalyzer(TypeCastAnalysis analyzer) {
	  this.analyzer = analyzer;
	  IOUtils.debug().pln(analyzer.displaySnapShot());
	}
	
	/**
   * Substitute the old memory elems to new memory elems in view only
   */
  private Expression updateViewWithMem(Expression state, Expression mem, Expression view) {    
    // update viewPrime
    Map<String, ArrayExpression> prevMemElemsMap = getRecordElems(state.getChild(0));
    Map<String, ArrayExpression> currentMemElemsMap = getRecordElems(mem);
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
    
    Expression viewPrime = view;
    if(!oldElems.isEmpty())
      viewPrime = viewPrime.subst(oldElems, newElems);
    
    return viewPrime;
  }
  
  private RecordExpression updateMemState(Expression memState, Expression lval, Expression rval) { 
    currentMemElems.putAll(getRecordElems(memState));
    xtc.type.Type lvalType = CType.getType(lval.getNode());
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    boolean isMemUpdated = false;
    String lvalTypeName = CTypeNameAnalyzer.getTypeName(lvalType);
    if(currentMemElems.containsKey(lvalTypeName)) { // previously declared variable
      CellKind kind = CType.getCellKind(lvalType);
      switch(kind) {
      case POINTER: {
        if(!ptrType.equals(rval.getType())) {
          assert rval.isConstant();  // for assign null to pointer int* ptr = 0;
          rval = getExpressionEncoding().getPointerEncoding().getNullPtr();
        }
        break;
      }
      case BOOL:
        rval= getExpressionEncoding().castToBoolean(rval); break;
      default: break;
      }
      tgtArray =  currentMemElems.get(lvalTypeName).update(lval, rval);
    } else { // newly type name
      isMemUpdated = true;
      CellKind kind = CType.getCellKind(lvalType);
      ArrayType arrType = null;
      switch(kind) {
      case BOOL: {
        arrType = em.arrayType(ptrType, em.booleanType());
        rval = getExpressionEncoding().castToBoolean(rval);
        break;
      }
      case SCALAR: {
        arrType = em.arrayType(ptrType, scalarType);
        break;
      }
      case POINTER: {
        arrType = em.arrayType(ptrType, ptrType);
        if(!ptrType.equals(rval.getType())) {
          assert rval.isConstant();
          rval = getExpressionEncoding().getPointerEncoding().getNullPtr();
        }
        break;
      }
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
      tgtArray = em.variable(lvalTypeName, arrType, false).asArray().update(lval, rval);
    }    
    currentMemElems.put(lvalTypeName, tgtArray);
    Type currentMemType = isMemUpdated? getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems) 
    		: memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  private Expression updateView(RecordExpression memState, TupleExpression viewState, 
      Expression indexExpr) {
    if(!hasView(indexExpr.getNode()))  return viewState;
    xtc.type.Type indexType = CType.getType(indexExpr.getNode());
    String indexTypeName = CTypeNameAnalyzer.getTypeName(indexType);
    
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);
    ExpressionManager em = getExpressionManager();
    CellKind kind = CType.getCellKind(indexType);
    switch(kind) {
    case SCALAR: {
      Expression newView = getViewVar(indexTypeName, scalarType);
      scalarViewState = scalarViewState.asArray().update(indexExpr, newView);
      break;
    }
    case POINTER: {
      Expression newView = getViewVar(indexTypeName, ptrType);
      ptrViewState = ptrViewState.asArray().update(indexExpr, newView);
      break;
    }
    default:
      throw new IllegalArgumentException("Invalid kind for view update " + kind);
    }
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }

  private boolean hasView(Node node) {
    boolean hasView = analyzer.hasView(node);
    return hasView;
  }
  
  private ArrayExpression getViewVar(String typeName, Type elemType) {
    if(viewVars.containsKey(typeName))  return viewVars.get(typeName);
    
    ArrayExpression elemArr = getExpressionManager()
        .arrayVar(typeName, ptrType, elemType, false);
    viewVars.put(typeName, elemArr);
    return elemArr;
  }
}
