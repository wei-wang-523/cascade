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

public class BurstallMemoryModel extends AbstractMemoryModel {
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallMemoryModel(encoding);
  }

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final BitVectorType cellType; // cell type
  private final ArrayType allocType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  /** when allocate a region_x in stack of array or structure, we just 
   * let addr_of_array == region_x, or addr_of_struct == region_x, 
   * which models exactly what happened in C. It means we should remove 
   * addr_of_array or addr_of_struct from lvals, otherwise when do 
   * --sound-alloc or --order-alloc, we will call getAssumptions(), which
   * ensures that addr_of_array/addr_of_struct < region_x or addr_of_array
   * /addr_of_strcut != region_x, and it's conflict with the above equality.
   * Here, we keep rvals to record those removed addr_of_struct and addr_of_array,
   * and remove them from lvals in getAssumptions().
   */
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems;
  private Expression currentAlloc = null;
  private ExpressionClosure currentState = null;

  private BurstallMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();
    this.currentMemElems = Maps.newLinkedHashMap();
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.cellType = exprManager.bitVectorType(size);
    
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    this.allocType = exprManager.arrayType(
        ptrType.getElementTypes().get(0), ptrType.getElementTypes().get(1));
    
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
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression memory = updateMemState(state.getChild(0), ptr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    return getUpdatedState(memory, alloc);
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0); 
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion);
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getUpdatedState(state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    /* For stack allocated region, add ptr directly to stackRegions */
    stackRegions.add(stackRegion); 
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    resetCurrentState();
    return getUpdatedState(state.getChild(0), alloc);
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
    resetCurrentState();
    return getUpdatedState(state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression memory = updateMemState(state.getChild(0), lval, rval);  
    resetCurrentState();
    return getUpdatedState(memory, state.getChild(1));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    return renewMemState(state, p);
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Expression rval = null;
    if(isScalaType(lval.getNode()))
      rval = getExpressionEncoding().getIntegerEncoding().unknown();
    else
      rval = getExpressionEncoding().unknown();
    Expression memory = updateMemState(state.getChild(0), lval, rval); 
    
    return getUpdatedState(memory, state.getChild(1));
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
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(currentMem, currentAlloc);
    currentState = suspend(state, statePrime);
    
    return exprManager.tt();
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
    return getUpdatedState(memVar, allocVar);
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
          // For tuple expression evaluation over memoryVar, since substitution doesn't return
          // right children for as tuple expression for state.
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memPrime = expr.getChild(0);
          memPrime = memPrime.subst(memoryVar.getChild(0), memory.getChild(0));
          memPrime = memPrime.subst(memoryVar.getChild(1), memory.getChild(1));
          
          Iterator<String> nameItr = memory.getChild(0).getType().asRecord().getElementNames().iterator();
          Iterator<? extends Expression> elemItr = memory.getChild(0).getChildren().iterator();
          Map<String, Expression> elemMap = Maps.newLinkedHashMap();
          while(nameItr.hasNext() && elemItr.hasNext()) {
            elemMap.put(nameItr.next(), elemItr.next());
          }
          
          if(memPrime.equals(expr.getChild(0))) {
            Iterator<String> namePrimeItr = expr.getChild(0).getType().asRecord().getElementNames().iterator();
            Iterator<? extends Expression> elemPrimeItr = expr.getChild(0).getChildren().iterator();
            while(namePrimeItr.hasNext() && elemPrimeItr.hasNext()) {
              elemMap.put(namePrimeItr.next(), elemPrimeItr.next());
            }
          } else {
            for(String name : memPrime.getType().asRecord().getElementNames()) {
              Expression elem = memPrime.asRecord().select(name);
              elemMap.put(name, elem);
            }
          }
          
          Iterable<Type> elemTypes = Iterables.transform(elemMap.values(), new Function<Expression, Type>(){
            @Override
            public Type apply(Expression elem) {
              return elem.getType();
            }
          });
          
          memType = exprManager.recordType(Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE),
              elemMap.keySet(), elemTypes);
          Expression mem = exprManager.record(memType, elemMap.values());
          
          Expression alloc = expr.getChild(1);
          if(alloc.isVariable()) { // substitution is useful for variable
            assert(alloc.equals(memoryVar.getChild(1)));
            alloc = memory.getChild(1);
          } else {
            alloc = alloc.subst(memoryVar.getChild(0), memory.getChild(0));
            alloc = alloc.subst(memoryVar.getChild(1), memory.getChild(1));
          }
          stateType = exprManager.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
              memType, alloc.getType());
          
          return exprManager.tuple(stateType, mem, alloc);
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
  public void resetCurrentState() {
    currentMemElems.clear();
    currentAlloc = null;
    currentState = null;
  }
  
  private RecordExpression getUpdatedMemory() {
    ExpressionManager em = getExpressionManager();
    
    Iterable<Type> elemTypes = Iterables.transform(currentMemElems.values(), 
        new Function<Expression, Type>(){
      @Override
      public Type apply(Expression expr) {
        return expr.getType();
      }
    });

    memType = em.recordType(Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        currentMemElems.keySet(), elemTypes);
        
    return em.record(memType, currentMemElems.values());
  }
  
  private TupleExpression getUpdatedState(Expression memoryPrime, Expression allocPrime) {
    ExpressionManager em = getExpressionManager();
    if(!stateType.getElementTypes().get(0).equals(memoryPrime.getType())) {
      stateType = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType());
    }
    return em.tuple(stateType, memoryPrime, allocPrime);
  }
  
  private void initCurrentMemElems(Expression memState) {
    Preconditions.checkArgument(memState.isRecord());
    RecordExpression mem = memState.asRecord();
    for(String elemName : mem.getType().getElementNames()) {
      currentMemElems.put(elemName, mem.select(elemName));
    }
  }
  
  private RecordExpression updateMemState(Expression memState, Expression lval, Expression rval) {   
    initCurrentMemElems(memState);
    String typeName = getTypeName(lval.getNode()); 
    // for case: assign null to pointer int* ptr = 0;
    if(typeName.startsWith("$PointerT") && rval.isBitVector()) {
        Preconditions.checkArgument(rval.isConstant() 
            && Integer.parseInt(rval.getNode().getString(0)) == 0);
        rval = ((PointerExpressionEncoding) getExpressionEncoding()).getPointerEncoding().nullPtr();
    }
    ArrayExpression tgtArray = null;
    if(currentMemElems.containsKey(typeName)) { // previously declared variable
      tgtArray =  currentMemElems.get(typeName).asArray().update(lval, rval);
    } else { // newly type name
      ExpressionManager em = getExpressionManager();
      if(isScalaType(lval.getNode())) {
        ArrayType arrType = em.arrayType(ptrType, cellType);
        tgtArray = em.variable(typeName, arrType, false).asArray().update(lval, rval);
      } else {
        ArrayType arrType = em.arrayType(ptrType, ptrType);
        tgtArray = em.variable(typeName, arrType, false).asArray().update(lval, rval);
      }
    }
    currentMemElems.put(typeName, tgtArray);
    
    return getUpdatedMemory();
  }
  
  private Expression renewMemState(Expression state, Expression p) {    
    initCurrentMemElems(state.getChild(0));
    String typeName = getTypeName(p.getNode());
    if(currentMemElems.containsKey(typeName)) {
      return currentMemElems.get(typeName).asArray().index(p);
    }
    
    ExpressionManager em = getExpressionManager();
    ArrayExpression tgtArray = null;
    
    if(isScalaType(p.getNode())) {
      ArrayType arrType = em.arrayType(ptrType, cellType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
    } else {
      ArrayType arrType = em.arrayType(ptrType, ptrType);
      tgtArray = em.variable(typeName, arrType, false).asArray();
    }
    currentMemElems.put(typeName, tgtArray);
    
    if(currentAlloc == null)  currentAlloc = state.getChild(1);
    Expression statePrime = getUpdatedState(getUpdatedMemory(), currentAlloc);
    currentState = suspend(state, statePrime);
    return tgtArray.index(p);
  }
  
  private boolean isScalaType(Node node) {
    xtc.type.Type type = (xtc.type.Type) node.getProperty(xtc.Constants.TYPE);
    
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type.isInteger() || type.isBoolean() || type.isFloat() || type.isNumber();
  }
  
  private Type getRefType() {
    return ptrType.getElementTypes().get(0);
  }
  
  private BitVectorType getOffType() {
    return ptrType.getElementTypes().get(1).asBitVectorType();
  }
  
  private String getTypeName(xtc.type.Type type) {
    if(type == null) 
      throw new ExpressionFactoryException("Invalid type.");
    
    StringBuffer sb =  new StringBuffer();
    type = type.resolve();
    if(type.isPointer()) {
      xtc.type.PointerT pType = (xtc.type.PointerT) type;
      sb.append('$').append(type.getName().substring(9)).append(getTypeName(pType.getType()));
    } else if(type.isArray()) {
      xtc.type.ArrayT aType = (xtc.type.ArrayT) type;
      sb.append('$').append(type.getName().substring(9)).append(getTypeName(aType.getType()));
    } else if(type.isStruct()) {
      sb.append('$').append(type.getName());
    } else if(type.isUnion()) {
      sb.append('$').append(type.getName());
    } else {
      sb.append('$').append(type.getName().substring(9));
    }
    return sb.toString();
  }
  
  private String getTypeName(Node node) {
    String resName = null;
    if(node.getName().equals("DirectComponentSelection")) {
      Node baseNode = node.getNode(0);
      String baseName = getTypeName((xtc.type.Type) baseNode.getProperty
          (xtc.Constants.TYPE));
      String fieldName = node.getString(1);
      resName = baseName + "#" + fieldName;
    } else if(node.getName().equals("IndirectComponentSelection")) {
      Node baseNode = node.getNode(0);
      xtc.type.Type baseType = (xtc.type.Type) baseNode.getProperty(xtc.Constants.TYPE);
      String baseName = getTypeName(((xtc.type.PointerT) baseType).getType());
      String fieldName = node.getString(1);
      resName = baseName + "#" + fieldName;
    } else {
      xtc.type.Type type = (xtc.type.Type) node.getProperty(xtc.Constants.TYPE);
      resName = getTypeName(type);
    }
    return resName;
  }
}
