package edu.nyu.cascade.fds;

import java.util.List;
import java.util.Map;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.inject.Inject;

import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;

public class TemporalExpressionEncodingImpl extends
    AbstractExpressionEncoding implements
    TemporalExpressionEncoding {
  public static class Factory implements TemporalExpressionEncoding.Factory {
    private final StateExpression.Factory exprFactory;
    
    @Inject
    Factory(StateExpression.Factory exprFactory) {
      this.exprFactory = exprFactory;
    }
    
    @Override
    public TemporalExpressionEncoding create(
        ExpressionEncoding baseEncoding) {
      return new TemporalExpressionEncodingImpl(baseEncoding,exprFactory);
    }
  }
  
  private final StateExpression.Factory stateExprFactory;
  private final StateProperty.Factory statePropFactory;
  private final Map<String, StateProperty> atPreds;
  private final Map<String, Function<StateExpression, StateExpression>> paramAtPreds;
  
  public TemporalExpressionEncodingImpl(
      ExpressionEncoding baseEncoding,
      final StateExpression.Factory stateExprFactory) {
    this(
        TemporalIntegerEncoding.create(baseEncoding.getIntegerEncoding(), stateExprFactory), 
        new TemporalBooleanEncoding((BooleanEncoding<? extends Expression>) baseEncoding.getBooleanEncoding(), 
            StateProperties.createFactory(stateExprFactory)), 
        TemporalArrayEncoding.create(baseEncoding.getArrayEncoding(), stateExprFactory), 
        stateExprFactory);
  }

  public TemporalExpressionEncodingImpl(
      IntegerEncoding<? extends StateExpression> integerEncoding,
      BooleanEncoding<? extends StateProperty> booleanEncoding,
      ArrayEncoding<? extends StateExpression> arrayEncoding,
      StateExpression.Factory stateExprFactory) {
    super(integerEncoding,booleanEncoding,arrayEncoding);
  
    this.stateExprFactory = stateExprFactory;
    this.statePropFactory = StateProperties.createFactory(stateExprFactory);
    this.atPreds = Maps.newHashMap();
    this.paramAtPreds = Maps.newHashMap();
    }
  
  @Override
  public void addAtPredicate(String label,
      Function<StateExpression, StateExpression> atPred) {
    Preconditions.checkArgument(!paramAtPreds.containsKey(label));
    paramAtPreds.put(label, atPred);
  }
  
  @Override
  public void addAtPredicate(String label, StateExpression atPred) {
    Preconditions.checkArgument(!atPreds.containsKey(label));
    atPreds.put(label, atPred.asStateProperty());
  }

  @Override
  public StateProperty and(Expression... conjuncts) {
    return statePropFactory.valueOf( super.and(conjuncts) );
  }

  /**
   * Returns a boolean expression representing the conjunction of the two
   * boolean arguments.
   */
  @Override
  public StateProperty and(Expression lhs, Expression rhs) {
    return statePropFactory.valueOf( super.and(lhs,rhs) );
  }

  @Override
  public StateProperty and(Iterable<? extends Expression> conjuncts) {
    return statePropFactory.valueOf( super.and(conjuncts) );
  }
  
  @Override
  public StateProperty atPredicate(StateExpression index,
      String firstLabel,
      String... otherLabels) {
    Function<StateExpression, StateExpression> expr = paramAtPreds.get(firstLabel);
    if (expr == null) {
      return null;
//      throw new ExpressionFactoryException("No at-predicate for '" + firstLabel + "'");
    }
    
    StateProperty firstPred = expr.apply(index).asStateProperty();
    assert( firstPred.isBoolean() );
    List<StateProperty> otherPreds = Lists.newArrayListWithCapacity(otherLabels.length);
    for( String label : otherLabels ) {
      expr = paramAtPreds.get(label);
      if (expr == null) {
        throw new ExpressionFactoryException("No at-predicate for '" + label + "'");
      }
      otherPreds.add( expr.apply(index).asStateProperty() );
    }
    return firstPred.or(otherPreds);
  }

  @Override
  public StateProperty atPredicate(String firstLabel, String... otherLabels) {
    StateProperty firstPred = atPreds.get(firstLabel);

    if( otherLabels.length==0 ) {
      return firstPred;
    }
    
    List<StateProperty> otherPreds = Lists.newArrayListWithCapacity(otherLabels.length);
    for( String label : otherLabels ) {
      StateProperty pred = atPreds.get(label);
      if( pred == null ) {
        throw new ExpressionFactoryException("No at-predicate for label: " + label);
      }
      otherPreds.add( pred );
    }
    return firstPred.or(otherPreds);
  }

  @Override
  public StateExpression bindingForSourceVar(String qName) {
    return stateExprFactory.valueOf( super.bindingForSourceVar(qName) );
  }

  @Override
  public StateProperty castToBoolean(Expression expr) {
    return stateExprFactory.valueOf( super.castToBoolean(expr) ).asStateProperty();
  }

  
  @Override
  public StateProperty eq(Expression a, Expression b) {
    return statePropFactory.valueOf(super.eq(a, b));
  }

  @Override
  public StateExpression functionCall(String name,
      Iterable<? extends Expression> args)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerStateExpression integerConstant(int i) {
    return stateExprFactory.valueOf(super.integerConstant(i)).asIntegerExpression();
  }

  @Override
  public StateProperty preserved(Iterable<? extends StateVariable> xs) {
    List<StateProperty> eqs = Lists.newArrayList();
    for (StateVariable x : xs) {
      eqs.add(x.preserved());
    }
    return stateExprFactory.valueOf(and(eqs)).asStateProperty();
  }
  
  @Override
  public StateVariable symbolicConstant(String name, IRType type, boolean fresh) {
    return stateExprFactory.valueOf(super.symbolicConstant(name,type,fresh)).asVariable();
  }

  @Override
  public StateVariable variable(String name, IRType type, boolean fresh) {
    return stateExprFactory.valueOf(super.variable(name,type,fresh)).asVariable();
  }
}
