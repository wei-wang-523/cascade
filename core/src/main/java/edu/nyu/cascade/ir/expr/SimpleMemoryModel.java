package edu.nyu.cascade.ir.expr;

import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

public class SimpleMemoryModel extends AbstractMemoryModel {
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String ADDRESS_TYPE = "addr";
  
  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   * @param size the desired size of a memory word (i.e., the unit of a pointer "step")
   * @param exprManager
   * @throws IllegalArgumentException if <code>addressSize</code> is not a multiple of <code>cellSize</code>
   */
  public static SimpleMemoryModel create(
      ExpressionEncoding encoding,
      int size)
      throws ExpressionFactoryException {
    ExpressionManager exprManager = encoding.getExpressionManager();
    BitVectorType cellType = exprManager.bitVectorType(size);

    return new SimpleMemoryModel(encoding, cellType);
  }

  protected final Type addressType;
  protected final BitVectorType cellType;
  protected final ArrayType memType;
  
  /** when allocate a region_x in stack of array or structure, we just 
   * let addr_of_array == region_x, or addr_of_struct == region_x, 
   * which models exactly what happened in C. It means we should remove 
   * addr_of_array or addr_of_struct from arrays, otherwise when do 
   * --sound-alloc or --order-alloc, we will call getAssumptions(), which
   * ensures that addr_of_array/addr_of_struct < region_x or addr_of_array
   * /addr_of_strcut != region_x, and it's conflict with the above equality.
   * Here, we keep rvals to record those removed addr_of_struct and addr_of_array,
   * and remove them from arrays in getAssumptions().
   */
  protected final Set<Expression> lvals;
  
  /** The current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  private ExpressionClosure currentState;

  protected SimpleMemoryModel(ExpressionEncoding encoding, BitVectorType cellType) {
    super(encoding);
    
    IntegerEncoding<?> integerEncoding = encoding.getIntegerEncoding();
    Preconditions.checkArgument(integerEncoding.getType().equals(cellType));
    
    addressType = getExpressionManager().uninterpretedType(ADDRESS_TYPE);
    this.cellType = cellType;
    memType = getExpressionManager().arrayType(addressType, cellType);
    lvals = Sets.newHashSet();
  }
  
  @Override
  public Expression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    Preconditions.checkArgument(lval.getType().equals( cellType ));
    // FIXME: What if element size and integer size don't agree?
    Preconditions.checkArgument(rval.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();    
    String lvalName = lval.asVariable().getName();
    Expression lvalIdx = exprManager.variable(lvalName, addressType, false);
    Expression statePrime = state.asArray().update(lvalIdx, rval);
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(state.getType().equals( getStateType() ));
    ExpressionManager exprManager = getExpressionManager();
    String lvalName = p.asVariable().getName();
    Expression lvalIdx = exprManager.variable(lvalName, addressType, false);
    return state.asArray().index(lvalIdx);
  }
  
  @Override
  public void addLval(VariableExpression p) {
    ExpressionManager exprManager = getExpressionManager();  
    String lvalName = p.getName();
    Expression lvalIdx = exprManager.variable(lvalName, addressType, false);
    lvals.add(lvalIdx);
  }
  
  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    return memVar;
  }
  
  @Override
  public ArrayType getMemoryType() {
    return memType;
  }
  
  @Override
  public Type getStateType() {
    return getMemoryType();
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
          Expression exprPrime = expr.subst(memoryVar, memory);
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
  public void resetCurrentState() {
    currentState = null;
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      ExpressionManager exprManager = getExpressionManager();
      
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        /* The sound allocation encoding doesn't assume anything about the ordering
         * of lvals. This may lead a blow-up due to case splits.
         */
        if (lvals.size() > 1) {
          builder.add(exprManager.distinct(lvals));
        }
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
  }
  
  protected void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression alloc(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareStruct(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression declareArray(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression free(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression havoc(Expression state, Expression lval) {
    // TODO Auto-generated method stub
    return null;
  }
}
