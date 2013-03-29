package edu.nyu.cascade.prover;

import java.util.Map;

import com.google.inject.internal.Maps;

public class Axiom {
  private final String name;
  private Map<Expression, VariableExpression> boundVarMap;
  private BooleanExpression rule;
  
  public Axiom(String name, BooleanExpression rule) {
    this.name = name;
    this.rule = rule;
    this.boundVarMap = Maps.newHashMap();
  }
  
  public static Axiom create(String name, BooleanExpression rule) {
    return new Axiom(name, rule);
  }
  
  public static Axiom create(String name) {
    return new Axiom(name, null);
  }
  
  public String getName() {
    return name;
  }
  
  public BooleanExpression getRule() {
    return rule;
  }
  
  public void setRule(BooleanExpression rule) {
    this.rule = rule;
  }
  
  public VariableExpression getVar(Expression key) {
    return boundVarMap.get(key);
  }
  
  public void putBoundVar(Expression bound, VariableExpression var) {
    boundVarMap.put(bound, var);
  }
  
  public Iterable<? extends Expression> getBounds() {
    return boundVarMap.keySet();
  }
}
