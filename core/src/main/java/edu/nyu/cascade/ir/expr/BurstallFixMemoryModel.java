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

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
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
public class BurstallFixMemoryModel extends AbstractBurstallMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallFixMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallFixMemoryModel(encoding);
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

  private BurstallFixMemoryModel(ExpressionEncoding encoding) {
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
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    ExpressionManager exprManager = getExpressionManager();
    
    size = exprManager.zeroExtend(size, offType.getSize());
    
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
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    size = getExpressionManager().zeroExtend(size, offType.getSize());
    
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
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    size = getExpressionManager().zeroExtend(size, offType.getSize());
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    
    return getUpdatedState(state, state.getChild(0), alloc);
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
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    ExpressionManager exprManager = getExpressionManager();
    size = exprManager.zeroExtend(size, offType.getSize());
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
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
    if(CellKind.SCALAR.equals(CType.getCellKind(lType)) 
        && CellKind.SCALAR.equals(CType.getCellKind(rType))) {
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
    CellKind kind = CType.getCellKind(pType);
    switch(kind) {
    case BOOL: {
      ArrayType arrType = em.arrayType(ptrType, em.booleanType());
      tgtArray = em.variable(typeName, arrType, false).asArray();
      break;
    }
    case SCALAR: {
      int size = getSizeofType(pType);
      ArrayType arrType = em.arrayType(ptrType, em.bitVectorType(size));
      tgtArray = em.variable(typeName, arrType, false).asArray();
      break;
    }
    case POINTER: {
      ArrayType arrType = em.arrayType(ptrType, ptrType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
      break;
    }
    default:
      throw new IllegalArgumentException("Invalid kind " + kind);
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
    CellKind kind = CType.getCellKind(lvalType);
    switch(kind) {
    case SCALAR: {
      int size = getSizeofType(lvalType);
      Type bvType = getExpressionManager().bitVectorType(size);
      rval = getExpressionEncoding().getIntegerEncoding().unknown(bvType);
      break;
    }
    case BOOL:
      rval = getExpressionEncoding().getBooleanEncoding().unknown(); break;
    case POINTER:
      rval = getExpressionEncoding().unknown(); break;
    default:
      throw new IllegalArgumentException("Invalid kind " + kind);
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
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    ExpressionManager exprManager = getExpressionManager();
    
    size = exprManager.zeroExtend(size, offType.getSize());
    
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
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = CType.unwrapped((xtc.type.Type) content.getNode()
        .getProperty(TYPE));
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
//  Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
  return new ExpressionClosure() {
    @Override
    public Expression eval(final Expression memory) {
//      Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
      if(!isState(expr)) {
        // For non-tuple expression evaluation
        Expression exprPrime = expr;
        
        /* Substitute the memory of expr */
        Expression memVar_mem = memoryVar.getChild(0);
        Expression memory_mem = memory.getChild(0);
        
        Map<String, Expression> memVarMemMap = getMemElems(memVar_mem);
        Map<String, Expression> memoryMemMap = getMemElems(memory_mem);
        
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
    if(!CellKind.SCALAR.equals(CType.getCellKind(type)))  {
      assert src.isConstant() && src.isBitVector();
      return ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr();
    }
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
    Iterable<String> elemNames = mem.getType().getElementNames();
    Iterable<String> fieldNames = pickFieldNames(elemNames);
    assert(Iterables.size(elemNames) == Iterables.size(fieldNames));
    Iterator<String> elemNameItr = elemNames.iterator();
    Iterator<String> fieldNameItr = fieldNames.iterator();
    while(elemNameItr.hasNext() && fieldNameItr.hasNext()) {
      String elemName = elemNameItr.next();
      String fieldName = fieldNameItr.next();
      Expression value = mem.select(elemName);
      resMap.put(fieldName, value);
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
    
    Iterable<String> elemNames = recomposeFieldNames(typeName, currentMemElems.keySet());
    
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
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().asBitVectorType().getSize() <= offType.getSize());
    
    ExpressionManager exprManager = getExpressionManager();
    
    size = exprManager.zeroExtend(size, offType.getSize());
    
    Expression alloc = state.getChild(1);
    
    Expression nullPtr = ((PointerExpressionEncoding) getExpressionEncoding())
        .getPointerEncoding().nullPtr();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in burstall memory model");
    }
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
      ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      builder.add(exprManager.neq(ptr, nullPtr)); // ptr != null
      
      List<Expression> regions = Lists.newArrayList(heapRegions);
      /* Collect all the heap regions except the last heap region, the one just allocated. */
      regions.remove(regions.size()-1);
      
      for(Expression region : regions) {
        Expression assump_local = exprManager.and(
            exprManager.greaterThan(alloc.asArray().index(region), 
                exprManager.bitVectorZero(offType.getSize())),
            exprManager.neq(region, nullPtr.asTuple().getChild(0)));
        Expression assert_local = exprManager.neq(region, ptr.asTuple().index(0));
        builder.add(exprManager.implies(assump_local, assert_local));
      }
      
      BooleanExpression res = exprManager.implies(assump, exprManager.and(builder.build()));
      return res;
    } else {
      return exprManager.tt();
    }
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
  
  private RecordExpression updateMemState(Expression memState, Expression lval, Expression rval) {
    currentMemElems.putAll(getMemElems(memState));
    ExpressionManager em = getExpressionManager();
    boolean isMemUpdated = false;
    ArrayExpression tgtArray = null;
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    String lvalTypeName = getTypeName(lvalType);
    if(currentMemElems.containsKey(lvalTypeName)) { // declared type name
      CellKind kind = CType.getCellKind(lvalType);
      switch(kind) {
      case BOOL: { // cascade_conditions
        rval = getExpressionEncoding().castToBoolean(rval);
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
        break;
      }
      case POINTER: {
        if(!ptrType.equals(rval.getType())) {
          // for assign null to pointer int* ptr = 0;
          assert rval.isConstant();
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
        break;
      } 
      case SCALAR:
        tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval); break;
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }      
    } else { // new type name
      isMemUpdated = true;
      CellKind kind = CType.getCellKind(lvalType);
      ArrayType arrType = null;
      switch(kind) {
      case BOOL: {
        rval = getExpressionEncoding().castToBoolean(rval);
        arrType = em.arrayType(ptrType, em.booleanType());
        break;
      } 
      case SCALAR: {
        int size = getSizeofType(lvalType);
        arrType = em.arrayType(ptrType, em.bitVectorType(size));
        break;
      } 
      case POINTER:{
        arrType = em.arrayType(ptrType, ptrType);
        if(!ptrType.equals(rval.getType())) {
          assert(rval.isConstant());
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
            .getPointerEncoding().nullPtr();
        }
        break;
      }
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
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
