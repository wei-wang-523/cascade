package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Iterator;

import xtc.tree.Node;
import xtc.type.AliasT;
import xtc.type.AnnotatedT;
import xtc.type.ArrayT;
import xtc.type.Reference;
import xtc.type.StructOrUnionT;
import xtc.type.StructT;
import xtc.type.UnionT;
import xtc.type.VariableT;

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
 * These arrays types map pointer type to cell type. Cell type is 
 * union of pointer type and scalar type. The state of memory is 
 * a record with multiple arrays for various types.
 * 
 * @author Wei
 *
 */

public class BurstallVer2MemoryModel extends AbstractMemoryModel {
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_ALLOC_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_SCALAR_ALIAS_VARIABLE_NAME = "scalarAlias";
  protected static final String DEFAULT_PTR_ALIAS_VARIABLE_NAME = "ptrAlias";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_ALIAS_STATE_TYPE = "aliasType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";
  protected static final String TEST_VAR = "TEST_VAR";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallVer2MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallVer2MemoryModel(encoding);
  }

  private final TupleType ptrType; // tuple (ref-type, off-type)
  private final BitVectorType scalarType; // cell type
  private final ArrayType allocType; // Array refType offType
  // Array ptrType Array (Array ptrType scalarType, Array ptrType scalarType)
  private final ArrayType scalarAliasType; 
  // Array ptrType Array (Array ptrType ptrType, Array ptrType ptrType)
  private final ArrayType ptrAliasType;
  private final TupleType aliasType;
  private RecordType memType; // Record type w/ multiple array types
  private TupleType stateType; // tuple(memType, allocType, scalarAliasType, ptrAliasType)
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private final Map<String, ArrayExpression> typeArrVarInAlias;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;

  private BurstallVer2MemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    this.typeArrVarInAlias = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    scalarType = exprManager.bitVectorType(size);
    ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    
    ArrayType scalarArrayType = exprManager.arrayType(ptrType, scalarType);
    ArrayType ptrArrayType = exprManager.arrayType(ptrType, ptrType);
    
    scalarAliasType = exprManager.arrayType(ptrType, 
        exprManager.arrayType(scalarArrayType, scalarArrayType));
    ptrAliasType = exprManager.arrayType(ptrType, 
        exprManager.arrayType(ptrArrayType, ptrArrayType));
    aliasType = exprManager.tupleType(DEFAULT_ALIAS_STATE_TYPE, scalarAliasType, ptrAliasType);
    
    allocType = exprManager.arrayType(
        ptrType.getElementTypes().get(0), ptrType.getElementTypes().get(1));
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), elemNames, elemTypes);
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType, aliasType);
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( scalarType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    RecordExpression memory = updateMemState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);
    Expression aliasState = initializeAliasState(state.getChild(2), ptr, locVar);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc, aliasState);
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( scalarType ));
    
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
    Preconditions.checkArgument(size.getType().equals( scalarType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    Expression ptrAlias = initializeAliasState(state.getChild(2), ptr);
    return getUpdatedState(state, state.getChild(0), alloc, ptrAlias);
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
    TupleExpression alias = state.getChild(2).asTuple();
    
    RecordExpression memPrime = updateMemState(mem, lval, rval);
    Expression aliasPrime = updateAliasRep(mem, alias, lval);
    aliasPrime = updateAliasState(aliasPrime, lval, rval);
    
    TupleExpression statePrime = getUpdatedState(state, memPrime, state.getChild(1), aliasPrime);
    
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
    if(currentAlloc == null)    
      currentAlloc = state.getChild(1);
    
    xtc.type.Type pType = (xtc.type.Type) p.getNode().getProperty(xtc.Constants.TYPE);
    String typeName = getTypeName(pType);
    
    if(currentMemElems.containsKey(typeName)) {
      ArrayExpression tgtArray = currentMemElems.get(typeName).asArray();
      if(!isStructFieldType(pType)) {
        return tgtArray.index(p);
      } else {
        Expression aliasState = state.getChild(2);
        Expression scalarAliasState = aliasState.asTuple().index(0);
        Expression ptrAliasState = aliasState.asTuple().index(1);
        if(scalarType.equals(tgtArray.getType().getElementType())) {
          ArrayExpression aliasArr = scalarAliasState.asArray().index(p).asArray();
          ArrayExpression repArr = aliasArr.index(tgtArray).asArray();
          return repArr.index(p);
        } else {
          ArrayExpression aliasArr = ptrAliasState.asArray().index(p).asArray();
          ArrayExpression repArr = aliasArr.index(tgtArray).asArray();
          return repArr.index(p);
        }
      }
    }
    
    // Add an element to currentMemElem
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    
    if(typeName.equals(TEST_VAR)) {
      ArrayType arrType = em.arrayType(ptrType, em.booleanType());
      tgtArray = em.variable(typeName, arrType, false).asArray();
    } else if(isScalarType(pType)) {
      ArrayType arrType = em.arrayType(ptrType, scalarType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
    } else if(isStructFieldType(pType)) {
      throw new ExpressionFactoryException("undeclared structure field selection expression");
    } else {
      ArrayType arrType = em.arrayType(ptrType, ptrType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
    }
    currentMemElems.put(typeName, tgtArray);
    
    Type currentMemType = getCurrentMemoryType();
    
    Expression memPrime = em.record(currentMemType, currentMemElems.values());
    Expression statePrime = getUpdatedState(state, memPrime, currentAlloc, state.getChild(2));
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
    if(isWithScalarType(lval.getNode())) {
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    } else {
      rval = getExpressionEncoding().unknown();
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
    
    Expression currentMem = updateMemState(state.getChild(0), ptr, locVar);
    Expression ptrAlias = initializeAliasState(state.getChild(2), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc, ptrAlias);
    currentState = suspend(state, statePrime);
    
    return exprManager.tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    xtc.type.Type type = (xtc.type.Type) content.getNode()
        .getProperty(xtc.Constants.TYPE);
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
    Expression aliasVar = exprManager.tuple(aliasType, 
        exprManager.variable(DEFAULT_SCALAR_ALIAS_VARIABLE_NAME, aliasType.asTuple().getElementTypes().get(0), true),
        exprManager.variable(DEFAULT_PTR_ALIAS_VARIABLE_NAME, aliasType.asTuple().getElementTypes().get(1), true));
    return exprManager.tuple(stateType, memVar, allocVar, aliasVar);
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
          Map<String, Expression> memElems = getMemElems(memory.getChild(0));
          List<Expression> oldArgs = Lists.newLinkedList();
          List<Expression> newArgs = Lists.newLinkedList();
          for(String typeName : typeArrVarInAlias.keySet()) {
            if(memElems.containsKey(typeName)) {
              oldArgs.add(typeArrVarInAlias.get(typeName));
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
    final String typeName_1 = memType_1.getName();
    final String typeName_0 = memType_0.getName();
    
    for(String elemName : commonElemNames) {
      String elemName_1 = typeName_1 + '@' + elemName;
      String elemName_0 = typeName_0 + '@' + elemName;
      Expression elem = em.ifThenElse(guard, mem_1.select(elemName_1), mem_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    final String typeName = Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME);
    Iterable<String> elemNames = Iterables.transform(commonElemNames, 
        new Function<String, String>(){
      @Override
      public String apply(String elemName) {
        return elemName + '@' + typeName;
      }
    });
    
    RecordType recordType = em.recordType(Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME), 
        elemNames, elemTypes);
    Expression res = em.record(recordType, elems);
    
    return res;
  }
  
  protected String getTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    StringBuffer sb =  new StringBuffer();
    
    if(type.isPointer()) {
      xtc.type.PointerT pType = (xtc.type.PointerT) type;
      sb.append('$').append("PointerT").append(getTypeName(pType.getType()));
    } else if(type.isArray()) {
      xtc.type.ArrayT aType = (xtc.type.ArrayT) type;
      sb.append('$').append("ArrayT").append(getTypeName(aType.getType()));
    } else if(type.isStruct()) {
      sb.append('$').append(type.getName());
    } else if(type.isUnion()) {
      sb.append('$').append(type.getName());
    } else if(type.isAnnotated()){
      AnnotatedT annoType = type.toAnnotated();
      if(annoType.hasShape()) {
        Reference ref = annoType.getShape();
        if(ref.hasBase() && ref.hasField()) {
          xtc.type.Type baseType = ref.getBase().getType();
          String fieldName = ref.getField();
          sb.append(getTypeName(baseType)).append('#').append(fieldName);
        } else {
          sb.append(getTypeName(ref.getType()));
        }
      } else {
        sb.append(getTypeName(annoType.getType()));
      }
    } else if(type.isAlias()) {
      AliasT aliasType = type.toAlias();
      sb.append(getTypeName(aliasType.getType()));
    } else if(type.isVariable()) {
      VariableT varType = (VariableT) type;
      sb.append(getTypeName(varType.getType()));
    } else if(type.isInteger()){
      sb.append('$').append("IntegerT");
    } else if(type.isFloat()){
      sb.append('$').append("FloatT");
    } else {
      throw new IllegalArgumentException("Cannot parse type " + type.getName());
    }
    return sb.toString();
  }
  
  protected String getTypeName(Node node) {
    Preconditions.checkArgument(node != null);
    String resName = null;
    if(node.getName().equals("PrimaryIdentifier") && node.getString(0).startsWith(TEST_VAR)) {
      resName = TEST_VAR;
    } else {
      xtc.type.Type type = (xtc.type.Type) node.getProperty(xtc.Constants.TYPE);
      resName = getTypeName(type);
    }
    return resName;
  }
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime, @param aliasPrime 
   * and create a new state type if state type is changed from the type of state
   * @return a new state
   */
  public TupleExpression getUpdatedState(Expression state, 
      Expression memoryPrime, Expression allocPrime, Expression aliasPrime) {
    ExpressionManager em = getExpressionManager();
    Type stateTypePrime = null;
    
    Type memType = state.getType().asTuple().getElementTypes().get(0);
    
    if(state != null && memType.equals(memoryPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType(), aliasPrime.getType());
    }
    
    // update aliasPrime
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
      aliasPrime = aliasPrime.subst(oldElems, newElems);
    
    return em.tuple(stateTypePrime, memoryPrime, allocPrime, aliasPrime);
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
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(xtc.Constants.TYPE);
    String lvalTypeName = getTypeName(lvalType); 
    
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    
    boolean isMemUpdated = false;
    if(currentMemElems.containsKey(lvalTypeName)) { // previously declared variable
      // for assign null to pointer int* ptr = 0;
      if(!isScalarType(unwrapped(lvalType)) && rval.isBitVector()) {
        assert(rval.isConstant() 
            && Integer.parseInt(rval.getNode().getString(0)) == 0);
        rval = ((PointerExpressionEncoding) getExpressionEncoding())
            .getPointerEncoding().nullPtr();
      } else if(lvalTypeName.equals(TEST_VAR)) { // for assign true/false to TEST_VAR_X 
        rval = getExpressionEncoding().castToBoolean(rval);
      }
      
      tgtArray =  currentMemElems.get(lvalTypeName).asArray().update(lval, rval);
    } else { // newly type name
      isMemUpdated = true;
      if(lvalTypeName.equals(TEST_VAR)) {
        ArrayType arrType = em.arrayType(ptrType, em.booleanType());
        tgtArray = em.variable(lvalTypeName, arrType, false).asArray()
            .update(lval, getExpressionEncoding().castToBoolean(rval));
      } else if(isScalarType(unwrapped(lvalType))) {
        ArrayType arrType = em.arrayType(ptrType, scalarType);
        tgtArray = em.variable(lvalTypeName, arrType, false).asArray().update(lval, rval);
      } else {
        ArrayType arrType = em.arrayType(ptrType, ptrType);
        if(rval.isBitVector()) {
          assert(rval.isConstant() 
              && Integer.parseInt(rval.getNode().getString(0)) == 0);
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
        tgtArray = em.variable(lvalTypeName, arrType, false).asArray().update(lval, rval);
      }
    }
    
    currentMemElems.put(lvalTypeName, tgtArray);
    Type currentMemType = isMemUpdated? getCurrentMemoryType() : memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  /**
   * Initialize @param aliasState with allocate statement
   * @param lval = malloc(...). The region assign to lval is
   * @param rval; and structure declare statement with @param
   * lval == null
   */
  private Expression initializeAliasState(Expression aliasState, Expression rval) {
    return initializeAliasState(aliasState, null, rval);
  }
  
  private Expression initializeAliasState(Expression aliasState, Expression lval, Expression rval) {
    Expression scalarAliasState = aliasState.asTuple().index(0);
    Expression ptrAliasState = aliasState.asTuple().index(1);
    
    Expression startAddr = rval;
    xtc.type.Type regionType = null;
    if(lval != null) {
      xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(xtc.Constants.TYPE);
      assert(lvalType.isPointer());
      regionType = unwrapped(lvalType.toPointer().getType());
    } else {
      regionType = unwrapped((xtc.type.Type) rval.getNode().getProperty(xtc.Constants.TYPE));
    }
    
    ExpressionManager em = getExpressionManager();
    if(regionType.isStruct()) {
      Map<String, Type> elemTypes = getMemberTypeOfField(regionType);
      Map<String, Expression> elemOffsets = getOffsetOfField(regionType);
      for(Entry<String, Expression> entry : elemOffsets.entrySet()) {
        String elemArrName = entry.getKey();
        Expression elemOffset = entry.getValue();
        Expression indexExpr = getExpressionEncoding().plus(startAddr, elemOffset);
        if(scalarType.equals(elemTypes.get(elemArrName))) { //
          Expression scalarAlias = scalarAliasState.asArray().index(indexExpr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
          scalarAlias = scalarAlias.asArray().update(elemArr, elemArr);
          scalarAliasState = scalarAliasState.asArray().update(indexExpr, scalarAlias);
        } else {
          Expression ptrAlias = ptrAliasState.asArray().index(indexExpr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
          ptrAlias = ptrAlias.asArray().update(elemArr, elemArr);
          ptrAliasState = ptrAliasState.asArray().update(indexExpr, ptrAlias);
        }
      } 
    } else if(regionType.isUnion()) { 
      Map<String, Type> elemTypes = getMemberTypeOfField(regionType);
      Map<String, Integer> elemTypeSizes = getSizeTypeOfField(regionType);
      int minTypeSize = Integer.MAX_VALUE;
      String repTypeName = null;
      for(String elemName : elemTypeSizes.keySet()) {
        int elemTypeSize = elemTypeSizes.get(elemName);
        if(minTypeSize > elemTypeSize) {
          minTypeSize = elemTypeSize; 
          repTypeName = elemName;
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
        ArrayExpression repArr = getTypeArrVar(repTypeName, scalarType);
        for(Entry<String, Type> entry : elemTypes.entrySet()) {
          String elemArrName = entry.getKey();
          Expression scalarAlias = scalarAliasState.asArray().index(startAddr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
          scalarAlias = scalarAlias.asArray().update(elemArr, repArr);
          scalarAliasState = scalarAliasState.asArray().update(startAddr, scalarAlias);
        }
      } else if(isAllPtrType) {
        ArrayExpression repArr = getTypeArrVar(repTypeName, ptrType);
        for(Entry<String, Type> entry : elemTypes.entrySet()) {
          String elemArrName = entry.getKey();
          Expression ptrAlias = ptrAliasState.asArray().index(startAddr);
          ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
          ptrAlias = ptrAlias.asArray().update(elemArr, repArr);
          scalarAliasState = scalarAliasState.asArray().update(startAddr, ptrAlias);
        }
      } else {
        throw new ExpressionFactoryException("Union type with both pointer type and scalar type.");
      }      
    } else { // lval point to a non-structure type
      String elemArrName = getTypeName(regionType);
      Expression indexExpr = startAddr;
      if(isScalarType(regionType)) {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, scalarType);
        Expression scalarAlias = scalarAliasState.asArray().index(indexExpr);
        scalarAlias = scalarAlias.asArray().update(elemArr, elemArr);
        scalarAliasState = scalarAliasState.asArray().update(indexExpr, scalarAlias);
      } else {
        ArrayExpression elemArr = getTypeArrVar(elemArrName, ptrType);
        Expression ptrAlias = ptrAliasState.asArray().index(indexExpr);
        ptrAlias = ptrAlias.asArray().update(elemArr, elemArr);
        ptrAliasState = ptrAliasState.asArray().update(indexExpr, ptrAlias);
      }   
    }
    return em.tuple(aliasType, scalarAliasState, ptrAliasState);
  }
  
  /**
   * Update @param aliasState if @param lval and @param rval are both pointers,
   * and they point to different type, otherwise, just @return aliasState
   */
  private Expression updateAliasState(Expression aliasState, Expression lval, Expression rval) {
    xtc.type.Type lvalType = unwrapped((xtc.type.Type) lval.getNode().getProperty(xtc.Constants.TYPE));
    xtc.type.Type rvalType = unwrapped((xtc.type.Type) rval.getNode().getProperty(xtc.Constants.TYPE));
    
    Expression scalarAliasState = aliasState.asTuple().index(0);
    Expression ptrAliasState = aliasState.asTuple().index(1);
    
    if(!(lvalType.isPointer() && rvalType.isPointer())) return aliasState;
    
    xtc.type.Type lvalPtrToType = unwrapped(lvalType.toPointer().getType());
    xtc.type.Type rvalPtrToType = unwrapped(rvalType.toPointer().getType());
    if(lvalPtrToType.equals(rvalPtrToType)) return aliasState;
    
    ExpressionEncoding encoding = getExpressionEncoding();
    ExpressionManager em = getExpressionManager();
    
    Map<String, Expression> lvalFieldOffset = getOffsetOfField(lvalPtrToType);
    Map<String, Type> lvalMemberTypeOfField = getMemberTypeOfField(lvalPtrToType);
    Map<String, Type> rvalMemberTypeOfField = getMemberTypeOfField(rvalPtrToType);
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
        Expression scalarAlias = scalarAliasState.asArray().index(indexExpr);
        Expression representative = scalarAlias.asArray().index(rMemberTypeArr);
        scalarAlias = scalarAlias.asArray().update(lMemberTypeArr, representative);
        scalarAliasState = scalarAliasState.asArray().update(indexExpr, scalarAlias);
      } else {
        Expression ptrAlias = ptrAliasState.asArray().index(indexExpr);
        Expression representative = ptrAlias.asArray().index(rMemberTypeArr);
        ptrAlias = ptrAlias.asArray().update(lMemberTypeArr, representative);
        ptrAliasState = ptrAliasState.asArray().update(indexExpr, ptrAlias);
      }
    }   
    return em.tuple(aliasType, scalarAliasState, ptrAliasState);
  }
  
  private Expression updateAliasRep(RecordExpression memState, TupleExpression aliasState, 
      Expression indexExpr) {
    xtc.type.Type indexType = (xtc.type.Type) indexExpr.getNode().getProperty(xtc.Constants.TYPE);
    String indexTypeName = getTypeName(indexType);
    
    // The index type name is not $StructType#FieldType, do not analyze alias now.
    if(!isStructFieldType(indexType))  return aliasState;
    
    Expression scalarAliasState = aliasState.asTuple().index(0);
    Expression ptrAliasState = aliasState.asTuple().index(1);
    ExpressionManager em = getExpressionManager();
    
    if(isScalarType(indexType)) {
      Expression scalarAlias = scalarAliasState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, scalarType);
      Expression previousRep = scalarAlias.asArray().index(tgtArray);
      scalarAlias = scalarAlias.asArray().update(previousRep, tgtArray);
      scalarAlias = scalarAlias.asArray().update(tgtArray, tgtArray);
      scalarAliasState = scalarAliasState.asArray().update(indexExpr, scalarAlias);
    } else {
      Expression ptrAlias = ptrAliasState.asArray().index(indexExpr);
      Expression tgtArray = getTypeArrVar(indexTypeName, ptrType);
      Expression previousRep = ptrAlias.asArray().index(tgtArray);
      ptrAlias = ptrAlias.asArray().update(previousRep, tgtArray);
      ptrAlias = ptrAlias.asArray().update(tgtArray, tgtArray);
      ptrAliasState = ptrAliasState.asArray().update(indexExpr, ptrAlias);
    }
    return em.tuple(aliasType, scalarAliasState, ptrAliasState);
  }
  
  private xtc.type.Type unwrapped(xtc.type.Type type) {
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type;
  }
  
  
  private boolean isWithScalarType(Node node) {
    xtc.type.Type type = (xtc.type.Type) node.getProperty(xtc.Constants.TYPE);
    return isScalarType(type);
  }
  
  private boolean isScalarType(xtc.type.Type type) {
    type = unwrapped(type);
    return type.isInteger() || type.isBoolean() || type.isFloat() || type.isNumber();
  }
  
  private boolean isStructFieldType(xtc.type.Type type) {
    String typeName = getTypeName(type);
    boolean isPointer = typeName.contains("PointerT");
    boolean hasField = typeName.indexOf('#') >= 0;
    return !isPointer && hasField;
  }
  
  /**
   * Get the member types of each field of structure type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to member types.
   */
  private Map<String, Type> getMemberTypeOfField(xtc.type.Type type) {
    if(!(type.isStruct() || type.isUnion()))    return null;
    
    Map<String, Type> elemTypes = Maps.newLinkedHashMap();
    StructOrUnionT structUnionType = type.toStructOrUnion();
    String structTypeName = getTypeName(structUnionType);
    for(VariableT elem : structUnionType.getMembers()) {
      // TODO: nested structure type
      String elemName = new StringBuilder().append(structTypeName)
          .append('#').append(elem.getName()).toString();
      xtc.type.Type elemType = elem.getType();
      if(isScalarType(elemType)) {
        elemTypes.put(elemName, scalarType);
      } else {
        elemTypes.put(elemName, ptrType);
      }
    }
    return elemTypes;
  }
  
  /**
   * Get the member offset of each field of structure type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to corresponding offsets.
   */
  private Map<String, Expression> getOffsetOfField(xtc.type.Type type) {    
    if(!type.isStruct()) return null;
    
    Map<String, Expression> elemOffsets = Maps.newLinkedHashMap();
    ExpressionManager em = getExpressionManager();
    
    StructT structType = type.toStruct();
    String structTypeName = getTypeName(structType);
    int offset = 0;
    int size = getOffType().getSize();
    for(VariableT elem : structType.getMembers()) {
      // TODO: nested structure type
      String elemName = new StringBuilder().append(structTypeName)
          .append('#').append(elem.getName()).toString();
      Expression offsetExpr = em.bitVectorConstant(offset, size);
      offset += sizeofXtcType(elem.getType());
      elemOffsets.put(elemName, offsetExpr);
    }
    return elemOffsets;
  }
  
  /**
   * Get the member type size of each field of union type, if
   * @param type is not structure type, @return null; otherwise,
   * @return a map from member names to corresponding offsets.
   */
  private Map<String, Integer> getSizeTypeOfField(xtc.type.Type type) {    
    if(!type.isUnion()) return null;
    
    Map<String, Integer> elemOffsets = Maps.newLinkedHashMap();    
    UnionT unionType = type.toUnion();
    String unionTypeName = getTypeName(unionType);
    for(VariableT elem : unionType.getMembers()) {
      // TODO: nested structure type
      String elemName = new StringBuilder().append(unionTypeName)
          .append('#').append(elem.getName()).toString();
      elemOffsets.put(elemName, sizeofXtcType(elem.getType()));
    }
    return elemOffsets;
  }
  
  private int sizeofXtcType(xtc.type.Type t) {
    int res = 0;
    t = unwrapped(t);   
    if (t.isInteger()) {
      res = 1;
    } else if (t.isPointer()) {
      res = 1;
    } else if (t.isStruct()) {
      for(VariableT elem : t.toStruct().getMembers()) {
        res += sizeofXtcType(elem.getType());
      }
    } else if (t.isUnion()) {
      for(VariableT elem : t.toUnion().getMembers()) {
        res = Math.max(res, sizeofXtcType(elem.getType()));
      }
    } else if(t.isArray()) {
      ArrayT array = t.toArray();
      res = (int) (array.getLength()) * sizeofXtcType(array.getType());
    } else {
      throw new IllegalArgumentException("Unknown type.");
    }
    return res;
  }
  
  private ArrayExpression getTypeArrVar(String typeName, Type elemType) {
    if(typeArrVarInAlias.containsKey(typeName))
      return typeArrVarInAlias.get(typeName);
    
    ArrayExpression elemArr = getExpressionManager()
        .arrayVar(typeName, ptrType, elemType, false);
    typeArrVarInAlias.put(typeName, elemArr);
    return elemArr;
  }
  
  private Type getRefType() {
    return ptrType.getElementTypes().get(0);
  }
  
  private BitVectorType getOffType() {
    return ptrType.getElementTypes().get(1).asBitVectorType();
  }
}
