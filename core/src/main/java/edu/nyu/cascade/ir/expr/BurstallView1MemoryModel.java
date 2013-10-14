package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Iterator;

import xtc.tree.Node;
import xtc.type.*;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CTypeNameAnalyzer;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.typeanalysis.TypeCastAnalysis;
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

public class BurstallView1MemoryModel extends AbstractMemoryModel {
  protected static final String DEFAULT_VIEW_VARIABLE_NAME = "view";
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
  private final Map<String, ArrayExpression> currentMemElems;
  private final Map<String, ArrayExpression> typeArrVarInView;
  
  private ArrayExpression currentAlloc = null;
  private ArrayExpression currentView = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  private TypeCastAnalysis analyzer = null;
  
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
    
    ptrType = encoding.getPointerEncoding().getType();
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
    xtc.type.Type lvalType = CType.unwrapped(CType.getType(lval.getNode()));
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
      currentMemElems.putAll(getRecordElems(state.getChild(0)));
      prevDerefState = state;
    }
    if(currentAlloc == null)  currentAlloc = state.getChild(1).asArray();
    if(currentView == null)    currentView = state.getChild(2).asArray();
    
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
      CellKind kind = CType.getCellKind(pType);
      ArrayExpression tgtArray = null;
      switch(kind) {
      case SCALAR: {
        ArrayType arrType = em.arrayType(ptrType, scalarType);
        tgtArray = em.variable(typeName, arrType, false).asArray();
        break;
      }
      case POINTER:{
        ArrayType arrType = em.arrayType(ptrType, ptrType);
        tgtArray = em.variable(typeName, arrType, false).asArray();
        break;
      } 
      case BOOL:{
        ArrayType arrType = em.arrayType(ptrType, em.booleanType());
        tgtArray = em.variable(typeName, arrType, false).asArray();
        break;
      }
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
      currentMemElems.put(typeName, tgtArray);
      Type memPrimeType = getRecordTypeFromMap(
      		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
      Expression memPrime = em.record(memPrimeType, currentMemElems.values());
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
    xtc.type.Type lvalType = CType.getType(lval.getNode());
    CellKind kind = CType.getCellKind(lvalType);
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
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1), state.getChild(2));
    
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
    Expression ptrView = initializeViewState(state.getChild(2), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1).asArray();
    currentAlloc = currentAlloc.update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, ptrView);
    currentState = suspend(state, statePrime);
    
    return valid_malloc(state, locVar, size);
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
  public Expression addressOf(Expression content) {
    xtc.type.Type type = CType.unwrapped(CType.getType(content.getNode()));
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
        allocType, true);
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
          List<Expression> oldArgs_view = Lists.newLinkedList();
          List<Expression> newArgs_view = Lists.newLinkedList();
          for(String typeName : typeArrVarInView.keySet()) {
            if(memoryMemMap.containsKey(typeName)) {
              oldArgs_view.add(typeArrVarInView.get(typeName));
              newArgs_view.add(memoryMemMap.get(typeName));
            }
          }
          if(!oldArgs_view.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs_view, newArgs_view);
            oldArgs_view.clear(); newArgs_view.clear();
          }
          
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
          setStateType(expr.getType());
          
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
  
/*  @Override
  public Expression castExpression(Expression state, Expression src, xtc.type.Type targetType) {
    //FIXME: scalar type has same cell size in this model, ignore cast cast
    if(CellKind.POINTER.equals(CType.getCellKind(targetType))) {
      // Initialization
      if(currentMemElems.isEmpty() || state != prevDerefState) {
        currentMemElems.putAll(getRecordElems(state.getChild(0)));
        prevDerefState = state;
      }
      if(currentAlloc == null)  currentAlloc = state.getChild(1);
      if(currentView == null)    currentView = state.getChild(2);
      
      Type currentMemType = getCurrentMemoryType();
      Expression memPrime = currentMemElems.isEmpty() ? state.getChild(0) : 
        getExpressionManager().record(currentMemType, currentMemElems.values());
      Expression viewPrime = updateViewState(currentView, CType.unwrapped(targetType), src);     
      TupleExpression statePrime = getUpdatedState(state,
          memPrime, currentAlloc, viewPrime);
      currentState = suspend(state, statePrime);
    } else {
      IOUtils.err().println("Ignored cast of " + 
          (xtc.type.Type) src.getNode().getProperty(TYPE) + " to " +  targetType);
    }
    return src;
  }*/
  
  @Override
  public Expression substSizeArr(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, allocType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(offType.getSize()), allocType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
  }
  
  @Override
  public void setTypeCastAnalyzer(TypeCastAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShot());
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
          // for assign null to pointer int* ptr = 0;
          assert(rval.isConstant());
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
      case SCALAR:
        arrType = em.arrayType(ptrType, scalarType); break;
      case POINTER: {
        arrType = em.arrayType(ptrType, ptrType);
        if(!ptrType.equals(rval.getType())) {
          assert(rval.isConstant());
          rval = getExpressionEncoding().getPointerEncoding().getNullPtr();
        }
        break;
      }
      default :
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
      xtc.type.Type lvalType = CType.getType(lval.getNode());
      assert(CellKind.POINTER.equals(CType.getCellKind(lvalType)));
      regionType = CType.unwrapped(CType.unwrapped(lvalType).toPointer().getType());
    } else {
      regionType = CType.unwrapped(CType.getType(rval.getNode()));
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
      String elemArrName = CTypeNameAnalyzer.getTypeName(regionType);
      Expression indexExpr = startAddr;
      CellKind kind = CType.getCellKind(regionType);
      switch(kind) {
      case SCALAR: {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
        Expression scalarView = scalarViewState.asArray().index(indexExpr);
        scalarView = scalarView.asArray().update(elemArr, elemArr);
        scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
        break;
      }
      case POINTER: {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
        Expression ptrView = ptrViewState.asArray().index(indexExpr);
        ptrView = ptrView.asArray().update(elemArr, elemArr);
        ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
        break;
      } 
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
    }
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }
  
  /**
   * Update @param viewState if @param lval and @param rval are both pointers,
   * and they point to different type, otherwise, just @return viewState
   */
  private Expression updateViewState(Expression viewState, xtc.type.Type lvalType, Expression rval) {
    xtc.type.Type rvalType = CType.unwrapped(CType.getType(rval.getNode()));
    
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);
    
    if(!(lvalType.isPointer() && rvalType.isPointer())) return viewState;
    
    xtc.type.Type lvalPtrToType = CType.unwrapped(lvalType.toPointer().getType());
    xtc.type.Type rvalPtrToType = CType.unwrapped(rvalType.toPointer().getType());
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
    
    xtc.type.Type indexType = CType.getType(indexExpr.getNode());
    ExpressionManager em = getExpressionManager();
    Expression scalarViewState = viewState.asTuple().index(0);
    Expression ptrViewState = viewState.asTuple().index(1);

    String indexTypeName = CTypeNameAnalyzer.getTypeName(indexType);
    CellKind kind = CType.getCellKind(indexType);
    switch(kind) {
    case SCALAR: {
      Expression scalarView = scalarViewState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, scalarType);
      Expression previousView = scalarView.asArray().index(tgtArray);
      scalarView = scalarView.asArray().update(previousView, tgtArray);
      scalarView = scalarView.asArray().update(tgtArray, tgtArray);
      scalarViewState = scalarViewState.asArray().update(indexExpr, scalarView);
      break;
    }
    case POINTER: {
      Expression ptrView = ptrViewState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, ptrType);
      Expression previousView = ptrView.asArray().index(tgtArray);
      ptrView = ptrView.asArray().update(previousView, tgtArray);
      ptrView = ptrView.asArray().update(tgtArray, tgtArray);
      ptrViewState = ptrViewState.asArray().update(indexExpr, ptrView);
      break;
    }
    default:
      throw new IllegalArgumentException("Invalid kind " + kind);
    }
    
    return em.tuple(viewType, scalarViewState, ptrViewState);
  }
  
  private boolean hasView(Node node) {
    boolean hasView = analyzer.hasView(node);
    return hasView;
  }
  
  /**
   * Get the member types of each field of structure type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to member types.
   */
  private Map<String, Type> getElemTypeOfStructUnionField(xtc.type.Type type) {
    Map<String, Type> elemTypes = Maps.newLinkedHashMap();
    String typeName = CTypeNameAnalyzer.getTypeName(type);
    if(!(type.isStruct() || type.isUnion())) {
      CellKind kind = CType.getCellKind(type);
      switch(kind){
      case SCALAR: 
        elemTypes.put(typeName, scalarType); break;
      case POINTER:
        elemTypes.put(typeName, ptrType); break;
      case BOOL:
        elemTypes.put(typeName, getExpressionManager().booleanType()); break;
      default: 
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
    } else {
      StructOrUnionT structUnionType = type.toStructOrUnion();
      for(VariableT elem : structUnionType.getMembers()) {
        // TODO: nested structure type
        String elemName = new StringBuilder().append(typeName)
            .append('.').append(elem.getName()).toString();
        xtc.type.Type elemType = elem.getType();
        CellKind kind = CType.getCellKind(elemType);
        switch(kind){
          case SCALAR: 
            elemTypes.put(elemName, scalarType); break;
          case BOOL: 
            elemTypes.put(elemName, getExpressionManager().booleanType()); break;
          case ARRAY: 
          case STRUCTORUNION:
          case POINTER: 
            elemTypes.put(elemName, ptrType); break;
          default: 
            throw new IllegalArgumentException("Invalid kind " + kind);
        }          
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
    String typeName = CTypeNameAnalyzer.getTypeName(type);
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
    String typeName = CTypeNameAnalyzer.getTypeName(type);
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
