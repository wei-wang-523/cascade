package edu.nyu.cascade.ir.expr;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import xtc.tree.Node;
import xtc.type.AliasT;
import xtc.type.AnnotatedT;
import xtc.type.Reference;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

/**
 * Burstall memory model, still has a flat memory array, but has 
 * type as a component of index. The type of array maps (type constant, 
 * pointer type) to pointer type. Scalar value is also with pointer 
 * type, but has $Constant as the first element - pretty slow.
 * 
 * @author Wei
 *
 */
public class BurstallVer1MemoryModel extends AbstractMemoryModel {
  protected static final String TYPE_NAME = "typeName";
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_CONSTANT = "$Constant";

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static BurstallVer1MemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    
    /** pointer type is (refType, offType) */
    PointerEncoding ptrEncoding = ((PointerExpressionEncoding) encoding).getPointerEncoding();
    TupleType ptrType = ptrEncoding.getType();
    
    ExpressionManager exprManager = encoding.getExpressionManager();
    UninterpretedType typeNameType = exprManager.uninterpretedType(TYPE_NAME);
    /** array's index type is (typeNameType, ptrType) */
    TupleType indexType = exprManager.tupleType("idxType", typeNameType, ptrType);
    /** array's type is (indexType, ptrType) */
    ArrayType memArrayType = exprManager.arrayType(indexType, ptrType);

    return new BurstallVer1MemoryModel(encoding, memArrayType);
  }
  
  /** Create an expression factory with the given array type to model memory. The size of the 
   * index type of the memory array (i.e., the size of a pointer) must be a multiple of the size
   * of the element type (i.e., the size of a memory word).
   */
  public static BurstallVer1MemoryModel create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    
    return new BurstallVer1MemoryModel(encoding, memArrayType);
  }

  public static BurstallVer1MemoryModel create(ExpressionEncoding encoding,
      ArrayVariableExpression memArray,
      ArrayVariableExpression allocArray) throws ExpressionFactoryException
  {
    return create(encoding, memArray.getType());
  }

  private final TupleType ptrType; // (ref-type, off-type)
  private final TupleType idxType; // (typeName-type, ptrType)
  private final ArrayType memType; // idxType -> ptrType
  private final ArrayType sizeType; // ref-type -> off-type  
  private final UninterpretedType typeNameType; // typeName-type
  
  private final VariableExpression constRefVar;
  private final Set<VariableExpression> lvals; // lvals: variables in stack
  private final Set<Expression> rvals;
  private final List<Expression> stackRegions, heapRegions;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;
  
  /** Restore the variable expression created for type name
   */
  private final Map<String, VariableExpression> typeMap;
  
  /** Restore all the scala type expressions
   */
  private final Set<VariableExpression> scalaTypeVars;

  private BurstallVer1MemoryModel(ExpressionEncoding encoding, ArrayType memType) {
    super(encoding);
  
    this.lvals = Sets.newHashSet();
    this.rvals = Sets.newHashSet();
    this.stackRegions = Lists.newArrayList();
    this.heapRegions = Lists.newArrayList();

    this.memType = memType;
    this.idxType = memType.getIndexType().asTuple();
    this.typeNameType = idxType.getElementTypes().get(0).asUninterpreted();
    this.ptrType = idxType.getElementTypes().get(1).asTuple();
    this.sizeType = getExpressionManager().arrayType(getRefType(), getOffType());
    
    this.typeMap = Maps.newHashMap();
    /** Put constant type variable into type map */
    this.constRefVar = getExpressionManager().variable(DEFAULT_CONSTANT, getRefType(), false);
    
    this.scalaTypeVars = Sets.newHashSet();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression typeNameVar = getTypeVar(ptr.getNode());
    Expression indexPtr = exprManager.tuple(idxType, typeNameVar, ptr);
    Expression memory = state.getChild(0).asArray().update(indexPtr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    return exprManager.tuple(getStateType(), memory, alloc);
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();
    Expression stackRegion = ptr.asTuple().index(0);
    stackRegions.add(stackRegion); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add(stackRegion); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size.asTuple().index(1));   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression stackRegion = ptr.asTuple().index(0);
    stackRegions.add(stackRegion); // For stack allocated region, add ptr directly to stackRegions;
    rvals.add(stackRegion); // Add ptr to rvals (removed variables)
    
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size.asTuple().index(1));   
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }

  /* TODO: This will fail for automatically allocated addresses (e.g., the
   * address of a local variable).
   */
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
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
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
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
    return exprManager.tuple(getStateType(), state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    
    ExpressionManager em = getExpressionManager();
    
    if(rval.getType().equals(getOffType()))
      rval = em.tuple(ptrType, constRefVar, rval);
    
    Expression typeNameVar = getTypeVar(lval.getNode());
    Expression index = em.tuple(idxType, typeNameVar, lval);
    Expression memory = state.getChild(0).asArray().update(index, rval);   
    
    return em.tuple(getStateType(), memory, state.getChild(1));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    Expression memory = state.getChild(0);
    ExpressionManager exprManager = getExpressionManager();
    Expression typeNameVar = getTypeVar(p.getNode());
    Expression indexVar = exprManager.tuple(idxType, typeNameVar, p);
    return memory.asArray().index(indexVar);
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?

    Expression rval = getExpressionEncoding().unknown();
    Expression typeNameVar = getTypeVar(lval.getNode());
    Expression index = getExpressionManager().tuple(idxType, typeNameVar, lval);
    Expression memory = state.getChild(0).asArray().update(index, rval);   
    
    return getExpressionManager().tuple(getStateType(), memory, state.getChild(1));
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
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( ptrType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression refVar = exprManager.variable(REGION_VARIABLE_NAME, getRefType(), true);
    Expression offZero = exprManager.bitVectorZero(getOffType().getSize());
    // locVar: (region_x, 0)
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression typeNameVar = getTypeVar(ptr.getNode());
    Expression indexPtr = exprManager.tuple(idxType, typeNameVar, ptr);
    Expression memory = state.getChild(0).asArray().update(indexPtr, locVar);
    Expression alloc = state.getChild(1).asArray().update(refVar, size.asTuple().index(1));
    Expression statePrime = exprManager.tuple(getStateType(), memory, alloc);
    
    setCurrentState(state, statePrime);
    return exprManager.tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    Preconditions.checkArgument(content.getChild(1).getType().equals(ptrType));
    return content.getChild(1);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      ExpressionManager exprManager = getExpressionManager();
      PointerExpressionEncoding encoding = (PointerExpressionEncoding) getExpressionEncoding();
      
      /* Assume all the scalar type index variables has constant values in memory */
      Expression indexVar = exprManager.variable("indexVar", idxType, true);
      List<BooleanExpression> disjs = Lists.newArrayListWithCapacity(scalaTypeVars.size());
      for(VariableExpression typeVar : scalaTypeVars)
        disjs.add(indexVar.asTuple().index(0).eq(typeVar));
      
      /* Assume for all index variable, if its type is scalar type, then its value tuple should 
       * have constant-ref variable as first argument. */
      BooleanExpression boolExpr = exprManager.forall(indexVar, 
          exprManager.implies(exprManager.or(disjs), 
              state.getChild(0).asArray().index(indexVar).asTuple().index(0).eq(constRefVar)));
      builder.add(boolExpr);
      
      /* Collect all the regions. */
      ImmutableList<Expression> regions = new ImmutableList.Builder<Expression>()
          .addAll(stackRegions).addAll(heapRegions).build();
      
      /* Remove all the variable in structVals from lvals. */      
      lvals.remove(rvals);
      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        /* The sound allocation encoding doesn't assume anything about the ordering
         * of lvals and regions. This may lead a blow-up due to case splits.
         */
        if(regions.size() > 1) {
          builder.add(exprManager.distinct(regions));
        }
        
        if (typeMap.size() > 1) {
          builder.add(exprManager.distinct(typeMap.values()));
        }
        
        if (lvals.size() > 1) {
          builder.add(exprManager.distinct(lvals));
        }
      } else if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
        /* Unsound allocation encoding: just pick an order and assert that
         * the tvals, lvals and regions are allocated in that order. 
         */
        
        /* Assert the distinctness on the tvals */
        if (typeMap.size() > 1) {
          builder.add(exprManager.distinct(typeMap.values()));
        }
       
        /* Assert the ordering on the lvals */
        VariableExpression lval = null;
        Iterator<VariableExpression> lvalIter = lvals.iterator();
        if( lvalIter.hasNext() ) {
          lval = lvalIter.next();
        }
        
        while (lvalIter.hasNext()) {
          VariableExpression lval2 = lvalIter.next();
          builder.add(encoding.lessThan(lval, lval2).asBooleanExpression());
          lval = lval2;
        }
        
        Expression regionVar = null;
        Iterator<Expression> regionIter = regions.iterator();
        if( regionIter.hasNext() ) {
          regionVar = regionIter.next();
        }
        
        while (regionIter.hasNext()) {
          Expression regionVar2 = regionIter.next();
          builder.add(encoding.lessThan(regionVar, regionVar2).asBooleanExpression());
          regionVar = regionVar2;
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
    Expression allocVar = exprManager.variable(DEFAULT_REGION_SIZE_VARIABLE_NAME, 
        sizeType, true);
    return exprManager.tuple(getStateType(), memVar, allocVar);
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return getExpressionManager().tupleType("memState", memType, sizeType);
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
        if(!expr.getType().equals(getStateType())) { 
          // For non-tuple expression evaluation
          Expression exprPrime = expr
              .subst(memoryVar.getChildren(), memory.getChildren());
          return exprPrime.setNode(expr.getNode());
        } else { 
          // For tuple expression evaluation over memoryVar, since substitution doesn't return
          // right children for as tuple expression for state.
          ExpressionManager exprManager = getExpressionManager();
          return exprManager.tuple(getStateType(), RecursionStrategies.unaryRecursionOverList(
              expr.getChildren(),
              new UnaryRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression e) {
              Expression ePrime = e.subst(ImmutableList.of(memoryVar.getChild(0)), 
                  ImmutableList.of(memory.getChild(0)));
              ePrime = ePrime.subst(ImmutableList.of(memoryVar.getChild(1)), 
                  ImmutableList.of(memory.getChild(1)));
              return ePrime;
            }
          }));
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
    };
  }
  
  @Override
  public ExpressionClosure getCurrentState() {
    return currentState;
  }
  
  @Override
  public void clearCurrentState() {
    currentState = null;
  }
  
  protected void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
  
  private Type getRefType() {
    return ptrType.getElementTypes().get(0);
  }
  
  private BitVectorType getOffType() {
    return ptrType.getElementTypes().get(1).asBitVectorType();
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
      AnnotatedT annoType = (AnnotatedT) type;
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
      AliasT aliasType = (AliasT) type;
      sb.append(getTypeName(aliasType.getType()));
    }
    return sb.toString();
  }
  
  private VariableExpression getTypeVar(Node node) {
    String resName  = getTypeName((xtc.type.Type) node.getProperty(xtc.Constants.TYPE));
    if(typeMap.containsKey(resName))    
      return typeMap.get(resName);
    
    VariableExpression res = getExpressionManager().variable(resName, typeNameType, false);
    typeMap.put(resName, res);
    
    if(resName.equals("$IntegerT") || resName.equals("$CharT")) scalaTypeVars.add(res);
    return res;
  }
  
  @Override
  public Expression castConstant(int value) {
    Expression val = getExpressionEncoding().integerConstant(value);
    return getExpressionManager().tuple(ptrType, constRefVar, val);
  }
}
