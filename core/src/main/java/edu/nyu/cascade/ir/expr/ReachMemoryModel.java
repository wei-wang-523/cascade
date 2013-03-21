package edu.nyu.cascade.ir.expr;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

public abstract class ReachMemoryModel extends BitVectorMemoryModel {

  protected static final String DEFAULT_REACH_ARRAY_VARIABLE_NAME = "ra";
  
  protected final ArrayType reachArrayType;
  
  protected final Expression nullPtr;

  /** 
   * Map associate a region with bunch of regions may be pointed to
   * private Map<Expression, Set<Expression>> pointTo;
   * side-effect assumption, generated in memory operations 
   * private BooleanExpression sideAssump;
   */
  protected ReachMemoryModel(ExpressionEncoding encoding, ArrayType memType,
      ArrayType reachArrayType) {
    super(encoding, memType);
    this.reachArrayType = reachArrayType;
    this.nullPtr = addressType.zero(addressType.getSize());
  }
  
  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression regionSizeVar = exprManager.variable(DEFAULT_REGION_SIZE_VARIABLE_NAME, 
        memType, true);
    Expression fieldAssignVar = exprManager.variable(DEFAULT_REACH_ARRAY_VARIABLE_NAME, 
        reachArrayType, true);
    
    return exprManager.tuple(getStateType(), memVar, regionSizeVar, fieldAssignVar);
  }
  
  @Override
  public TupleType getStateType() {
    return getExpressionManager().tupleType("stateType", memType, memType, reachArrayType);
  }

  @Override
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, addressType, true);  
    
    // For array, add to the start of regions;
    stackRegions.add(locVar); 
    // Add ptr to rvals (removed variables)
    rvals.add((VariableExpression) ptr);
    
    Expression regionSize = state.getChild(1).asArray().update(locVar, size);
    
    return exprManager.tuple(getStateType(), 
        state.getChild(0), 
        regionSize,
        state.getChild(2));
  }
  
  @Override
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(size.getType().equals( addressType ));
    
    ExpressionManager exprManager = getExpressionManager();
    
    VariableExpression locVar = exprManager.variable(REGION_VARIABLE_NAME, addressType, true);  
    
    // For array, add to the start of regions;
    stackRegions.add(locVar); 
    // Add ptr to rvals (removed variables)
    rvals.add((VariableExpression) ptr);
    
    Expression regionSize = state.getChild(1).asArray().update(locVar, size);
    
    return exprManager.tuple(getStateType(), 
        state.getChild(0), 
        regionSize,
        state.getChild(2));
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {   
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    Expression regionSize = state.getChild(1);
    
    try {
      BitVectorExpression regionZero = getExpressionEncoding().getIntegerEncoding()
          .zero().asBitVector();
//      for( VariableExpression locVar : regions )
//          regionSize = exprManager.ifThenElse(ptr.eq(locVar), 
//              regionSize.asArray().update(locVar, regionZero), regionSize);
      regionSize = regionSize.asArray().update(ptr, regionZero);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }   
    return exprManager.tuple(getStateType(), 
        state.getChild(0), 
        regionSize, 
        state.getChild(2));
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    Expression memory = state.getChild(0); 
    memory = memory.asArray().update(lval, rval);   
    
    return getExpressionManager().tuple(getStateType(), 
        memory, 
        state.getChild(1),
        state.getChild(2));
  }
  
  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(getStateType().equals(memory.getType()) );
        if(!expr.isTuple()) { 
          // For non-tuple expression evaluation
          Expression exprPrime = expr   // For memory
              .subst(ImmutableList.of(memoryVar.getChild(0)), ImmutableList.of(memory.getChild(0)));
          exprPrime = exprPrime        // For region size
              .subst(ImmutableList.of(memoryVar.getChild(1)), ImmutableList.of(memory.getChild(1)));
          exprPrime = exprPrime        // For region size
              .subst(ImmutableList.of(memoryVar.getChild(1)), ImmutableList.of(memory.getChild(2)));
          return exprPrime.setNode(expr.getNode());
        } else { 
          // For tuple expression evaluation over memoryVar, since substitution doesn't return
          // right children for as tuple expression for state.
          ExpressionManager exprManager = getExpressionManager();
          return exprManager.tuple(getStateType(), (Iterable<? extends Expression>) 
              RecursionStrategies.unaryRecursionOverList(expr.getChildren(),
              new UnaryRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression e) {
              Expression ePrime = e.subst(ImmutableList.of(memoryVar.getChild(0)), 
                  ImmutableList.of(memory.getChild(0)));
              ePrime = ePrime.subst(ImmutableList.of(memoryVar.getChild(1)), 
                  ImmutableList.of(memory.getChild(1)));
              ePrime = ePrime.subst(ImmutableList.of(memoryVar.getChild(2)), 
                  ImmutableList.of(memory.getChild(2)));
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
  
  public TupleExpression fieldAssign(
      Expression state,
      Expression lval,
      String field,
      Expression rval) {
    Preconditions.checkArgument( state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( addressType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();
    Expression reachArray = state.getChild(2).asArray().update(lval, rval);
    
    return exprManager.tuple(getStateType(), 
        state.getChild(0), 
        state.getChild(1),
        reachArray);
  }
  
  /**
   * Assume a acyclic singly list with length <code>length</code> connected by field 
   * <code>fieldName</code> is allocated with root <code>ptr</code>. Each element has  
   * type with size <code>size<code>, and the field with offset <code>offset</code> in 
   * the type.
   */
  public BooleanExpression create_acyclic_list(Expression state, 
      String fieldName, Expression ptr,
      Expression lengthExpr, int size, int offset) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    Preconditions.checkArgument(lengthExpr.isConstant());
    
    ExpressionManager exprManager = getExpressionManager();
    
    ArrayExpression memory = state.getChild(0).asArray();
    ArrayExpression regionSize = state.getChild(1).asArray();
    ArrayExpression reachArray = state.getChild(2).asArray();
    
    int length = exprManager.valueOfIntegerConstant(lengthExpr);
   
    /* Create #length new regions */
    List<Expression> newRegions = Lists.newArrayListWithCapacity(length);
    for(int i = 0; i<length; i++) 
      newRegions.add(exprManager.variable(REGION_VARIABLE_NAME, 
          addressType, true));
    
    /* For dynamic memory allocation, add to the end of regions */
    heapRegions.addAll(newRegions);
    
    Expression currloc = ptr;
    for(int i = 0; i<length; i++) {
      memory = memory.update(currloc, newRegions.get(i));
      regionSize = regionSize.update(newRegions.get(i), 
          exprManager.bitVectorConstant(size, addressType.getSize()));
      currloc = exprManager.plus(addressType.getSize(), newRegions.get(i), 
          (Expression) exprManager.bitVectorConstant(offset, addressType.getSize()));
      if(i == length-1) {
        reachArray = reachArray.update(newRegions.get(i), nullPtr);
        memory = memory.update(currloc, nullPtr);        
      } else {
        reachArray = reachArray.update(newRegions.get(i), newRegions.get(i+1));
      }
    }
    
    Expression statePrime = exprManager.tuple(getStateType(), memory, regionSize, reachArray);    
    setCurrentState(state, statePrime);
    
    return exprManager.tt();
  }
  
  /**
   * Assume a cyclic singly list with length <code>length</code> connected by field 
   * <code>fieldName</code> is allocated with root <code>ptr</code>. Each element has  
   * type with size <code>size<code>, and the field with offset <code>offset</code> in 
   * the type.
   */
  public BooleanExpression create_cyclic_list(Expression state, 
      String fieldName, Expression ptr,
      Expression lengthExpr, int size, int offset) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(ptr.getType().equals( addressType ));
    Preconditions.checkArgument(lengthExpr.isConstant());
    
    ExpressionManager exprManager = getExpressionManager();
    
    ArrayExpression memory = state.getChild(0).asArray();
    ArrayExpression regionSize = state.getChild(1).asArray();
    ArrayExpression reachArray = state.getChild(2).asArray();
    
    int length = exprManager.valueOfIntegerConstant(lengthExpr);
   
    /* Create #length new regions */
    List<Expression> newRegions = Lists.newArrayListWithCapacity(length);
    for(int i = 0; i<length; i++) 
      newRegions.add(exprManager.variable(REGION_VARIABLE_NAME, 
          addressType, true));
    
    /* For dynamic memory allocation, add to the end of regions */
    heapRegions.addAll(newRegions);
    
    Expression currloc = ptr;
    for(int i = 0; i<length; i++) {
      memory = memory.update(currloc, newRegions.get(i));
      regionSize = regionSize.update(newRegions.get(i), 
          exprManager.bitVectorConstant(size, addressType.getSize()));
      currloc = exprManager.plus(addressType.getSize(), newRegions.get(i), 
          (Expression) exprManager.bitVectorConstant(offset, addressType.getSize()));
      if(i == length-1) {
        reachArray = reachArray.update(newRegions.get(i), ptr);
        memory = memory.update(currloc, ptr);
      } else {
        reachArray = reachArray.update(newRegions.get(i), newRegions.get(i+1));
      }
    }
    
    Expression statePrime = exprManager.tuple(getStateType(), memory, regionSize, reachArray);    
    setCurrentState(state, statePrime);
    
    return exprManager.tt();
  }
  
  /**
   * Get all the related reachability assumptions f(a) = b from memory model
   * <code>state</code>
   */
  abstract public BooleanExpression getReachAssumptions(Expression state);
  
  /**
   * Predicate that <code>lvalExpr</code> can reach <code>rvalExpr</code>
   * via <code>fieldName</code> path.
   */
  abstract public Expression reach(Expression state, String fieldName, 
      Expression lvalExpr, Expression rvalExpr);

  abstract public BooleanExpression isRoot(Expression memory, String fieldname,
      Expression ptrExpr);
}
