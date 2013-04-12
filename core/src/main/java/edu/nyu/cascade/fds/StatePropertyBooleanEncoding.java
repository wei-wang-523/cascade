package edu.nyu.cascade.fds;

import java.util.List;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.AbstractTypeEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;

public class StatePropertyBooleanEncoding 
extends AbstractTypeEncoding<StateProperty>
implements
    BooleanEncoding<StateProperty> {
  
  private final StateProperty.Factory propFactory;
  
  @Inject
  public StatePropertyBooleanEncoding(@Assisted ExpressionManager exprManager, 
      @Assisted StateProperty.Factory propFactory) {
     super(exprManager,exprManager.booleanType());
     this.propFactory = propFactory;
  }

  @Override
  public StateProperty and(Iterable<? extends StateProperty> conjuncts) {
    List<BooleanExpression> conjExprs = Lists.newArrayList();
    for (StateProperty p : conjuncts) {
      conjExprs.add(p.asBooleanExpression());
    }
    return wrap(getExpressionManager().and(conjExprs));
  }
  
  @Override
  public StateProperty and(StateProperty lhs, StateProperty rhs) {
    return lhs.and(rhs);
  }

  @Override
  public StateProperty ff() {
    return propFactory.valueOf(getExpressionManager().ff());
  }
  
  @Override
  public StateProperty iff(StateProperty lhs, StateProperty rhs) {
    return lhs.iff(rhs);
  }

  @Override
  public StateProperty implies(StateProperty lhs, StateProperty rhs) {
    return lhs.implies(rhs);
  }

  @Override
  public StateProperty not(StateProperty arg) {
    return arg.not();
  }

  @Override
  public StateProperty ofBooleanExpression(BooleanExpression b) {
    return propFactory.valueOf(b);
  }

  @Override
  public StateProperty or(Iterable<? extends StateProperty> disjuncts) {
    List<BooleanExpression> disjExprs = Lists.newArrayList();
    for (StateProperty p : disjuncts) {
      disjExprs.add(p.asBooleanExpression());
    }
    return wrap(getExpressionManager().or(disjExprs));
  }

  @Override
  public StateProperty or(StateProperty lhs, StateProperty rhs) {
    return lhs.or(rhs);
  }

  @Override
  public StateProperty tt() {
    return propFactory.valueOf(getExpressionManager().tt());
  }

  private StateProperty wrap(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    return propFactory.valueOf(expr);
  }

  @Override
  public StateProperty xor(StateProperty lhs, StateProperty rhs) {
    return lhs.xor(rhs);
  }

  @Override
  public BooleanExpression toBoolean(StateProperty b) {
    return b.asBooleanExpression();
  }

  @Override
  public StateProperty forall(Iterable<? extends VariableExpression> vars,
      StateProperty expr) {
    return expr.forall(vars);
  }

  @Override
  public StateProperty ofExpression(Expression x) {
    Preconditions.checkArgument(x.isBoolean());
    return propFactory.valueOf(x.asBooleanExpression());
  }
}
