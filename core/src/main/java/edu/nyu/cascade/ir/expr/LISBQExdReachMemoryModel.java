package edu.nyu.cascade.ir.expr;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
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

public class LISBQExdReachMemoryModel extends ReachMemoryModel {
  
  private static final String FUN_R = "r";
  
  private final Expression nullPtr;

  /** 
   * Map associate a region with bunch of regions may be pointed to
   * private Map<Expression, Set<Expression>> pointTo;
   * side-effect assumption, generated in memory operations 
   * private BooleanExpression sideAssump;
   */
  private LISBQExdReachMemoryModel(ExpressionEncoding encoding, ArrayType memType,
      ArrayType reachArrayType) {
    super(encoding, memType, reachArrayType);
    nullPtr = addressType.zero(addressType.getSize());
  }
  
  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param addressSize the desired size of a pointer
   * @param cellSize the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static LISBQExdReachMemoryModel create(
      ExpressionEncoding encoding,
      int addressSize, int cellSize)
      throws ExpressionFactoryException {
    
    ExpressionManager exprManager = encoding.getExpressionManager();
    
    BitVectorType addressType = exprManager.bitVectorType(addressSize);
    BitVectorType cellType = exprManager.bitVectorType(cellSize);
    ArrayType memArrayType = exprManager.arrayType(addressType, cellType);
    ArrayType reachArrayType = exprManager.arrayType(addressType, addressType);
    
    return new LISBQExdReachMemoryModel(encoding, memArrayType, reachArrayType);
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
  public static LISBQExdReachMemoryModel create(
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
    
    return new LISBQExdReachMemoryModel(encoding, memArrayType, reachArrayType);
  }

  public static LISBQExdReachMemoryModel create(
      ExpressionEncoding encoding,
      ArrayVariableExpression memArray) throws ExpressionFactoryException {
    return create(encoding, memArray.getType());
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();

    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, addressType, true);
    
    // For dynamic memory allocation, add to the end of regions
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
  public Expression reach(Expression state, String fieldName, 
      Expression lvalExpr, Expression rvalExpr) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lvalExpr.getType().equals(addressType));
    Preconditions.checkArgument(rvalExpr.getType().equals(addressType));
    
    ExpressionEncoding encoding = getExpressionEncoding();
    ArrayExpression reachArray = state.getChild(2).asArray();
    
    Expression result = encoding.functionCall(FUN_R, reachArray, lvalExpr, rvalExpr, rvalExpr);
    return result;
  }

  @Override
  public BooleanExpression getReachAssumptions(Expression state) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    ExpressionManager exprManager = getExpressionManager();
    List<BooleanExpression> result = Lists.newArrayList();    
    ArrayExpression reachArray = state.getChild(2).asArray();    
    result.add(reachArray.index(nullPtr).eq(nullPtr));
//    
//    /* For each pair (locVar_a, locVar_b) in reachArray
//     */
//    for(VariableExpression locVar_a : regions) {
//      Expression locVar_b = reachArray.index(locVar_a); 
//      Expression f_locVar_a = encoding.functionCall(FUN_R, locVar_a);
//      result.add(f_locVar_a.eq(locVar_b));
//    }
    
    return exprManager.and(result);
  }
  
  @Override
  public BooleanExpression isRoot(Expression state, String fieldName, Expression rootExpr) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(rootExpr.getType().equals(addressType));
    JoinReachEncoding encoding = (JoinReachEncoding) getExpressionEncoding();
    ExpressionManager exprManager = getExpressionManager();
    Expression nil = encoding.getNil();
    Type eltType = encoding.getEltType();
    Expression x_var = exprManager.variable("x", eltType, true);
    BooleanExpression res = exprManager.implies(rootExpr.neq(nil), 
        exprManager.forall(x_var, rootExpr.neq(encoding.applyF(x_var))));
    return res;
  }
}
