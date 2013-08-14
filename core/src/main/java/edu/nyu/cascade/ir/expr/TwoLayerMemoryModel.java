package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;
import xtc.type.AnnotatedT;
import xtc.type.Reference;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public class TwoLayerMemoryModel extends AbstractMemoryModel {
  protected static final String DEFAULT_STATE_TYPE = "twoLayerStateType";
  protected static final String DEFAULT_BURSTALL_STATE_NAME = "burstallState";
  protected static final String DEFAULT_MONO_STATE_NAME = "monoState";
  
  protected final BurstallMemoryModel burstallMem;
  protected final MonolithicMemoryModel monoMem;

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static TwoLayerMemoryModel create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new TwoLayerMemoryModel(encoding);
  }
  
  private ExpressionClosure currentState = null;
  private TupleType stateType;

  private TwoLayerMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
    this.burstallMem = BurstallMemoryModel.create(encoding);
    this.monoMem = MonolithicMemoryModel.create(encoding);
    this.stateType = getExpressionManager().tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), burstallMem.getStateType(), monoMem.getStateType());
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);

    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
//    if(toCollapse(ptr)) {
      monoStatePrime = monoMem.alloc(monoStatePrime, ptr, size);
//    } else {
//      burstallStatePrime = burstallMem.alloc(burstallStatePrime, ptr, size);
//    }
    
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);

    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
    if(toCollapse(ptr)) {
      monoStatePrime = monoMem.declareArray(monoState, ptr, size);
    } else {
      burstallStatePrime = burstallMem.declareArray(burstallState, ptr, size);
    }
      
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);

    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
    if(toCollapse(ptr)) {
      monoStatePrime = monoMem.declareStruct(monoState, ptr, size);
    } else {
      burstallStatePrime = burstallMem.declareStruct(burstallState, ptr, size);
    }
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }

  /* TODO: This will fail for automatically allocated addresses (e.g., the
   * address of a local variable).
   */
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);
    
    BooleanExpression burstallStateAssump= burstallMem.valid(burstallState, ptr);
    BooleanExpression monoStateAssump = monoMem.valid(monoState, ptr);
    
    return getExpressionManager().and(burstallStateAssump, monoStateAssump);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);

    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
//    if(toCollapse(ptr)) {
//      burstallStatePrime = burstallMem.free(burstallState, ptr);
//    } else {
      monoStatePrime = monoMem.free(monoState, ptr);
//    }
    
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }

  @Override
  public TupleExpression assign(Expression state, Expression lval, Expression rval) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);

    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
    if(toCollapse(lval, rval)) {
      monoStatePrime = monoMem.assign(monoState, lval, rval);
    } else {
      burstallStatePrime = burstallMem.assign(burstallState, lval, rval);
    }
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);
    Expression res = null;
    if(toCollapse(p)) {
      res = monoMem.deref(monoState, p);
    } else {
      res = burstallMem.deref(burstallState, p);
    }
    
    ExpressionClosure burstallCurrentState = burstallMem.getCurrentState();
    ExpressionClosure monoCurrentState = monoMem.getCurrentState();
    
    if(!(burstallCurrentState == null && monoCurrentState == null)) {
      Expression burstallStatePrime = burstallState;
      Expression monoStatePrime = monoState;
      
      if(burstallCurrentState != null) {
        /* Don't change burstall state type at this point */
        TupleType burstallStateType = burstallMem.getStateType();
        burstallStatePrime = burstallCurrentState.eval(burstallState);
        burstallMem.clearCurrentState();
        burstallMem.setStateType(burstallStateType);
      }
      
      if(monoCurrentState != null) {
        monoStatePrime = monoCurrentState.eval(monoState);
        monoMem.clearCurrentState();
      }
      
      Expression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
//      stateType = statePrime.getType().asTuple();
      currentState = suspend(state, statePrime);
    }
    
    return res;
  }
  
  @Override
  public TupleExpression havoc(Expression state, Expression lval) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);
    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
    if(toCollapse(lval)) {
      burstallStatePrime = burstallMem.havoc(burstallState, lval);
    } else {
      monoStatePrime = monoMem.havoc(monoState, lval);
    }
    
    TupleExpression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    stateType = statePrime.getType();    
    return statePrime;
  }
  
  @Override
  public Expression createLval(String name) {
//    monoMem.createLval(name);
    return burstallMem.createLval(name);
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);
    
    Expression burstallStatePrime = burstallState;
    Expression monoStatePrime = monoState;
    
//    if(toCollapse(ptr)) {
      monoMem.allocated(monoState, ptr, size);
      ExpressionClosure monoCurrentState = monoMem.getCurrentState();
      monoStatePrime = monoCurrentState.eval(burstallState);
      monoMem.clearCurrentState();
//    } else {
//      burstallMem.allocated(burstallState, ptr, size);
//      ExpressionClosure burstallCurrentState = burstallMem.getCurrentState();
//      burstallStatePrime = burstallCurrentState.eval(burstallState);
//      burstallMem.clearCurrentState();
//    }
    
    Expression statePrime = getUpdatedState(state, burstallStatePrime, monoStatePrime);
    currentState = suspend(state, statePrime);
    
    return getExpressionManager().tt();
  }
  
  @Override
  public Expression addressOf(Expression content) {
    if(toCollapse(content)) {
      return monoMem.addressOf(content);
    } else {
      return burstallMem.addressOf(content);
    }
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    Expression burstallState = state.getChild(0);
    Expression monoState = state.getChild(1);
    builder.addAll(burstallMem.getAssumptions(burstallState));
    builder.addAll(monoMem.getAssumptions(monoState));
    return builder.build();
  }

  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression burstallVar = burstallMem.freshState();
    Expression monoVar = monoMem.freshState();
    return exprManager.tuple(stateType, burstallVar, monoVar);
  }
  
  @Override
  public RecordType getMemoryType() {
    throw new UnsupportedOperationException("Two layer memory model doesn't support getMemoryType()");
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  public void setStateType(TupleType stateType) {
    this.stateType = stateType;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        if(!isState(expr)) {
          // For non-tuple expression evaluation
          Expression burstallMemVar = memoryVar.getChild(0);
          Expression monoMemVar = memoryVar.getChild(1);
          Expression burstallMem = memory.getChild(0);
          Expression monoMem = memory.getChild(1);
          Expression exprPrime = expr
              .subst(burstallMemVar.getChildren(), burstallMem.getChildren());
          exprPrime = exprPrime
              .subst(monoMemVar.getChildren(), monoMem.getChildren());
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_burstall = memory.getChild(0);
          Expression memory_mono = memory.getChild(1);
          
          Expression expr_burstall = expr.getChild(0);
          Expression expr_mono = expr.getChild(1);
          
          Expression memoryVar_burstall = memoryVar.getChild(0);
          Expression memoryVar_mono = memoryVar.getChild(1);
          
          ExpressionClosure currentState_burstall = burstallMem.suspend(memoryVar_burstall, expr_burstall);
          ExpressionClosure currentState_mono = monoMem.suspend(memoryVar_mono, expr_mono);
          
          Expression memPrime_bustall = currentState_burstall.eval(memory_burstall);
          Expression memPrime_mono = currentState_mono.eval(memory_mono);
          
          stateType = expr.getType().asTuple();
          
          return exprManager.tuple(expr.getType(), memPrime_bustall, memPrime_mono);
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
    currentState = null;
    monoMem.clearCurrentState();
    burstallMem.clearCurrentState();
  }
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  public TupleExpression getUpdatedState(Expression state, Expression burstallState, Expression monoState) {
    ExpressionManager em = getExpressionManager();
    Type stateTypePrime = null;
    
    if(state != null 
        && state.getType().asTuple().getElementTypes().get(0).equals(burstallState.getType())
        && state.getType().asTuple().getElementTypes().get(1).equals(monoState.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          burstallState.getType(), monoState.getType());
    }
    
    return em.tuple(stateTypePrime, burstallState, monoState);
  }
  
  /**
   * Decide to collapse this assign statement or not:
   *  - union access
   *  - cast
   *  - memCopy
   *  - pointer arithmetic
   * 
   * Or inconsistent view with current region
   *    - array with scalar type: pointer arithmetic or memCopy won't create inconsistent with
   *    - array with aggregate type: TODO
   *    - structure: view with valid field names, might inconsistent with pointer arithmetic, memCopy
   *    - union: view with current valid field names, inconsistent with any other names, 
   *    pointer arithmetic or memCopy
   * 
   * FIXME: how to associate each expression with the right region? Also the problem in Mono memory
   */
  private boolean toCollapse(Expression lval, Expression rval) {
    xtc.type.Type lType = (xtc.type.Type) lval.getNode().getProperty(xtc.Constants.TYPE);
    xtc.type.Type rType = (xtc.type.Type) rval.getNode().getProperty(xtc.Constants.TYPE);
    String lvalTypeName = burstallMem.getTypeName(lType);
    String rvalTypeName = burstallMem.getTypeName(rType);
    if(lvalTypeName.equals(rvalTypeName)) {
      return toCollapse(lval) || toCollapse(rval);
    } else {
      return true;
    }
  }
  
  private boolean toCollapse(Expression p) {
    Node srcNode = p.getNode();
    xtc.type.Type type = (xtc.type.Type) srcNode.getProperty(xtc.Constants.TYPE);
    
    while(type.isAnnotated()) {
      AnnotatedT annotatedType = (AnnotatedT) type;
      if(!annotatedType.hasShape())
        type = annotatedType.getType();
      else {
        Reference ref = annotatedType.getShape();
        if(!ref.hasBase())
          type = ref.getType();
        else
          type = ref.getBase().getType();
      }
    }
    
    return type.isUnion();
  }
}
