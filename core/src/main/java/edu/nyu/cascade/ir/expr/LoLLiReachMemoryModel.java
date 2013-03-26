package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

public class LoLLiReachMemoryModel extends ReachMemoryModel {
  
  private static final String FUN_F = "f";  
  private static final String FUN_RF_AVOID = "rf_avoid";
  
  /** 
   * Map associate a region with bunch of regions may be pointed to
   * private Map<Expression, Set<Expression>> pointTo;
   * side-effect assumption, generated in memory operations 
   * private BooleanExpression sideAssump;
   */
  protected LoLLiReachMemoryModel(ExpressionEncoding encoding, ArrayType memType,
      ArrayType reachArrayType) {
    super(encoding, memType, reachArrayType);
  }
  
  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param addressSize the desired size of a pointer
   * @param cellSize the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static LoLLiReachMemoryModel create(
      ExpressionEncoding encoding,
      int addressSize, int cellSize)
      throws ExpressionFactoryException {
    
    ExpressionManager exprManager = encoding.getExpressionManager();
    
    BitVectorType addressType = exprManager.bitVectorType(addressSize);
    BitVectorType cellType = exprManager.bitVectorType(cellSize);
    ArrayType memArrayType = exprManager.arrayType(addressType, cellType);
    ArrayType reachArrayType = exprManager.arrayType(addressType, addressType);
    
    return new LoLLiReachMemoryModel(encoding, memArrayType, reachArrayType);
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
  public static LoLLiReachMemoryModel create(
      ExpressionEncoding encoding, 
      ArrayType memArrayType)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(memArrayType.getIndexType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getElementType().isBitVectorType());
    Preconditions.checkArgument(memArrayType.getIndexType().asBitVectorType().getSize()
        % memArrayType.getElementType().asBitVectorType().getSize() == 0);
    
    ExpressionManager exprManager = encoding.getExpressionManager();
    
    BitVectorType addressType = memArrayType.getIndexType().asBitVectorType();
    ArrayType reachArrayType = exprManager.arrayType(addressType, addressType);
    
    return new LoLLiReachMemoryModel(encoding, memArrayType, reachArrayType);
  }

  public static LoLLiReachMemoryModel create(
      ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException {
    return create(encoding, memArray.getType());
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    /* FIXME: What if element size and integer size don't agree? */
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();

    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, addressType, true);
    
    /* For dynamic memory allocation, add to the end of regions */
    heapRegions.add(locVar); 
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression regionSize = state.getChild(1).asArray().update(locVar, size); 
    Expression reachArray = state.getChild(2).asArray().update(locVar, locVar);
        
    return exprManager.tuple(getStateType(),
        memory, 
        regionSize,
        reachArray);
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();

    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, addressType, true);
    
    /* For dynamic memory allocation, add to the end of regions */
    heapRegions.add(locVar); 
    
    Expression memory = state.getChild(0).asArray().update(ptr, locVar);
    Expression regionSize = state.getChild(1).asArray().update(locVar, size); 
    Expression reachArray = state.getChild(2).asArray().update(locVar, locVar);
        
    setCurrentState(state, exprManager.tuple(getStateType(), memory, regionSize, reachArray));
    return exprManager.tt();
  }

  @Override
  public Expression reach(Expression state, String fieldName, 
      Expression lvalExpr, Expression rvalExpr) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lvalExpr.getType().equals(addressType));
    Preconditions.checkArgument(rvalExpr.getType().equals(addressType));

    Expression result = applyEltRf_avoid(lvalExpr, rvalExpr, rvalExpr);
    return result;
  }

  @Override
  public BooleanExpression getReachAssumptions(Expression state) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    final ExpressionManager exprManager = getExpressionManager();
    final ArrayExpression reachArray = state.getChild(2).asArray();
    
    if(Preferences.isSet(Preferences.OPTION_PARTIAL_INST) 
        || Preferences.isSet(Preferences.OPTION_TOTAL_INST)) {
      instGen(heapRegions);
    }
    
    /* Apply unaryRecursionOverList instead of go through a list
     * same job as above
     */
    return exprManager.and(RecursionStrategies.unaryRecursionOverList(
        heapRegions,
        new UnaryRecursionStrategy<Expression, Expression>() {
      @Override
      public BooleanExpression apply(Expression locVar_a) {
        Expression locVar_b = getEltExpr(reachArray.index(locVar_a)); 
        Expression f_locVar_a = applyEltF(locVar_a);
        return f_locVar_a.eq(locVar_b);
      }
    }));
  }
  
  @Override
  public BooleanExpression isRoot(Expression state, String fieldName, Expression rootExpr) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(rootExpr.getType().equals(addressType));
    ExpressionManager exprManager = getExpressionManager();
    Expression nil = getNil();
    Type eltType = getEltType();
    Expression x_var = exprManager.variable("x", eltType, true);
    rootExpr = getEltExpr(rootExpr);
    BooleanExpression res = exprManager.implies(rootExpr.neq(nil), 
        exprManager.forall(x_var, rootExpr.neq(applyF(x_var))));
    return res;
  }
  
  private Expression applyF(Expression arg) {
    ReachEncoding encoding = getExpressionEncoding();
    return encoding.functionCall(FUN_F, arg);
  }
  
  private Expression applyEltF(Expression arg) {
    return applyF(getEltExpr(arg));
  }
  
  private Expression applyRf_avoid(Expression arg1, Expression arg2, Expression arg3) {
    ReachEncoding encoding = getExpressionEncoding();
    return encoding.functionCall(FUN_RF_AVOID, arg1, arg2, arg3);
  }
  
  private Expression applyEltRf_avoid(Expression arg1, Expression arg2, Expression arg3) {
    return applyRf_avoid(getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
}
