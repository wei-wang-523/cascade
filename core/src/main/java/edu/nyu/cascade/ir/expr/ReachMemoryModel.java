package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.inject.internal.Maps;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.util.Preferences;

public class ReachMemoryModel extends BitVectorMemoryModel {
  
  protected final Expression nullPtr;

  /** 
   * Map associate a region with bunch of regions may be pointed to
   * private Map<Expression, Set<Expression>> pointTo;
   * side-effect assumption, generated in memory operations 
   * private BooleanExpression sideAssump;
   */
  protected ReachMemoryModel(ExpressionEncoding encoding, ArrayType memType) {
    super(encoding, memType);
    nullPtr = addressType.zero(addressType.getSize());
  }
  
  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param size the desired size of a pointer
   * @param size2 the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static ReachMemoryModel create(
      ExpressionEncoding encoding,
      int size, int size2)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    BitVectorType addressType = exprManager.bitVectorType(size);
    BitVectorType cellType = exprManager.bitVectorType(size2);
    ArrayType memArrayType = exprManager.arrayType(addressType, cellType);

    return new ReachMemoryModel(encoding, memArrayType);
  }
  
  /** Create an expression factory with the given array type to model memory. The size of the 
   * index type of the memory array (i.e., the size of a pointer) must be a multiple of the size
   * of the element type (i.e., the size of a memory word).
   * @param exprManager
   * @param addressSize
   *          the desired size of a pointer
   * @param cellSize
   *          the desired size of a memory word (i.e., the unit of a pointer
   *          "step")
   * 
   * @throws IllegalArgumentException
   *           if <code>addressSize</code> is not a multiple of
   *           <code>cellSize</code>
   */
  public static ReachMemoryModel create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(memArrayType.getIndexType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getElementType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getIndexType().asBitVectorType().getSize()
        % memArrayType.getElementType().asBitVectorType().getSize() == 0);
      return new ReachMemoryModel(encoding, memArrayType);
  }

  public static ReachMemoryModel create(
      ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException
  {
    return create(encoding, memArray.getType());
  }
  
  public BooleanExpression fieldAssign(
      Expression state,
      Expression lval,
      String field,
      Expression rval) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    if(Preferences.isSet(Preferences.OPTION_ENCODE_FIELD_ARRAY)) {
      updateReach(field, lval, rval);
      return getExpressionManager().tt();
    } else
      return assignReach(field, lval, rval);
  }
  
  /**
   * Assume a acyclic singly list with length <code>length</code> connected by field 
   * <code>fieldName</code> is allocated with root <code>ptr</code>. Each element has  
   * type with size <code>size<code>, and the field with offset <code>offset</code> in 
   * the type.
   */
  public BooleanExpression create_list(Expression state,
      Expression ptr, Expression lengthExpr, int size,
      Map<String, Integer> fldOffMap,
      boolean acyclic, boolean singly_list) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    Preconditions.checkArgument(lengthExpr.isConstant());
    
    ExpressionManager exprManager = getExpressionManager();
    
    ArrayExpression memory = state.getChild(0).asArray();
    ArrayExpression regionSize = state.getChild(1).asArray();
    
    int length = exprManager.valueOfIntegerConstant(lengthExpr);
   
    /* Create #length new regions */
    List<Expression> newRegions = Lists.newArrayListWithCapacity(length);
    for(int i = 0; i<length; i++) 
      newRegions.add(exprManager.variable(REGION_VARIABLE_NAME, addressType, true));
    
    /* For dynamic memory allocation, add to the end of regions */
    heapRegions.addAll(newRegions);
    
    Expression auxPtr = acyclic ? nullPtr : ptr;
    newRegions.add(0, auxPtr);
    newRegions.add(auxPtr);
    
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    Expression currloc = ptr;
    memory = memory.update(currloc, newRegions.get(1));
    
    String[] flds = new String[fldOffMap.size()];
    Map<String, Expression> fldLocMap = Maps.newLinkedHashMap();

    for(int i = 1; i<=length; i++) {
      regionSize = regionSize.update(newRegions.get(i), 
          exprManager.bitVectorConstant(size, addressType.getSize()));
      int fld_index = 0;
      for(String fld : fldOffMap.keySet()) {
        int offset = fldOffMap.get(fld);
        currloc = exprManager.plus(addressType.getSize(), newRegions.get(i), 
            (Expression) exprManager.bitVectorConstant(offset, addressType.getSize())); 
        flds[fld_index++] = fld;
        fldLocMap.put(fld, currloc);
      }
      
      if(singly_list) { // singly-linked list
        Preconditions.checkArgument(flds.length == 2);
        memory = memory.update(fldLocMap.get(flds[0]), newRegions.get(i+1));
        if(Preferences.isSet(Preferences.OPTION_ENCODE_FIELD_ARRAY))
          updateReach(flds[0], newRegions.get(i), newRegions.get(i+1));
        else           
          builder.add(assignReach(flds[0], newRegions.get(i), newRegions.get(i+1)));
      } else { // doubly-linked list
        Preconditions.checkArgument(flds.length == 2);
        memory = memory.update(fldLocMap.get(flds[0]), newRegions.get(i+1));
        memory = memory.update(fldLocMap.get(flds[1]), newRegions.get(i-1));
        if(Preferences.isSet(Preferences.OPTION_ENCODE_FIELD_ARRAY)) {
          updateReach(flds[0], newRegions.get(i), newRegions.get(i+1));
          updateReach(flds[1], newRegions.get(i), newRegions.get(i-1));
        } else {
          builder.add(assignReach(flds[0], newRegions.get(i), newRegions.get(i+1)));
          builder.add(assignReach(flds[1], newRegions.get(i), newRegions.get(i-1)));
        }
      }
    }
    
    if(acyclic) {
      if(singly_list)
        builder.add(isRoot(flds[0], newRegions.get(1)));
      else {
        builder.add(isRoot(flds[0], newRegions.get(1)));
        builder.add(isRoot(flds[1], newRegions.get(length)));
      }
    }
    
    Expression statePrime = exprManager.tuple(getStateType(), memory, regionSize);    
    setCurrentState(state, statePrime);
    return exprManager.and(builder.build());
  }
  
  @Override
  public ReachEncoding getExpressionEncoding() {
    ReachEncoding encoding = (ReachEncoding) super.getExpressionEncoding();
    return encoding;
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet<BooleanExpression> res = super.getAssumptions(state);
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    if(Preferences.isSet(Preferences.OPTION_PARTIAL_INST) || Preferences.isSet(Preferences.OPTION_TOTAL_INST))
      instGen(heapRegions);
    builder.addAll(res);
    return builder.build();
  }
  
  protected BooleanExpression assignReach(String field, Expression arg1, Expression arg2) {
    ReachEncoding encoding = (ReachEncoding) super.getExpressionEncoding();
    return encoding.assignReach(field, arg1, arg2);
  }
  
  protected void instGen(Iterable<Expression> gterms) {
    ReachEncoding encoding = getExpressionEncoding();
    encoding.instGen(gterms);
  }
  
  public BooleanExpression isRoot(String field, Expression rootExpr) {
    ReachEncoding encoding = getExpressionEncoding();
    return encoding.isRoot(field, rootExpr);
  }
  
  protected void updateReach(String field, Expression arg1, Expression arg2) {
    ReachEncoding encoding = getExpressionEncoding();
    encoding.updateReach(field, arg1, arg2);
  }
  
  public BooleanExpression reach(String field, Expression arg1, Expression arg2, Expression arg3) {
    ReachEncoding encoding = getExpressionEncoding();
    return encoding.reach(field, arg1, arg2, arg3);
  }
}
