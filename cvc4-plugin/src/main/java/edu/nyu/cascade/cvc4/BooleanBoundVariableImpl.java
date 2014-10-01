package edu.nyu.cascade.cvc4;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public final class BooleanBoundVariableImpl extends VariableExpressionImpl implements BooleanExpression {
	
  BooleanBoundVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.booleanType(), fresh);
  }

  @Override
  public BooleanTypeImpl getType() {
    return (BooleanTypeImpl) super.getType();
  }
  
  @Override
  public void addTrigger(Expression p) {
    addTrigger(p);
  }

  @Override
  public void addMultiTrigger(Iterable<? extends Expression> multiTrigger) {
    addMultiTrigger(multiTrigger);
  }

  @Override
  public BooleanExpression and(Expression e) {
    return this.and(e);
  }

  @Override
  public BooleanExpression and(Iterable<? extends Expression> e) {
    return this.and(e);
  }

  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars) {
    return this.exists(vars);
  }

  @Override
  public BooleanExpression exists(Expression firstVar, Expression... otherVars) {
    return this.exists(firstVar, otherVars);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars) {
    return this.forall(vars);
  }

  @Override
  public BooleanExpression forall(Expression firstVar, Expression... otherVars) {
    return this.forall(firstVar, otherVars);
  }

  @Override
  public ImmutableList<ImmutableList<? extends Expression>> getTriggers() {
    return getTriggers();
  }

  @Override
  public BooleanExpression iff(Expression e) {
   return this.iff(e);
  }

  @Override
  public Expression ifThenElse(Expression thenPart, Expression elsePart) {
    return this.ifThenElse(thenPart, elsePart);
  }

  @Override
  public BooleanExpression implies(Expression e) {
    return this.implies(e);
  }

  @Override
  public BooleanExpression not() {
    return this.not();
  }

  @Override
  public BooleanExpression or(Expression e) {
    return BooleanExpressionImpl.mkOr(getExpressionManager(), this, e);
  }

  @Override
  public void setTriggers(Iterable<? extends Expression> triggers) {
    this.setTriggers(triggers);
  }

  @Override
  public void setMultiTriggers(
      Iterable<? extends Iterable<? extends Expression>> multiTriggers) {
    this.setMultiTriggers(multiTriggers);
  }

  @Override
  public BooleanExpression xor(Expression e) {
    return BooleanExpressionImpl.mkXor(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpression or(Iterable<? extends Expression> disjuncts) {
    ImmutableList<Expression> args = new ImmutableList.Builder<Expression>()
        .add(this).addAll(disjuncts).build();
    return BooleanExpressionImpl.mkOr(getExpressionManager(), args);
  }

  @Override
  public void setBoundVars(Iterable<? extends Expression> vars) {
    this.setBoundVars(vars);
  }

  @Override
  public ImmutableList<? extends Expression> getBoundVars() {
    return this.getBoundVars();
  }

  @Override
  public void setBody(BooleanExpression expr) {
    this.setBody(expr);
  }

  @Override
  public BooleanExpression getBody() {
    return this.getBody();
  }
}
