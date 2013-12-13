package edu.nyu.cascade.cvc4;

import java.util.Arrays;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.BooleanType;

public final class BooleanTypeImpl extends TypeImpl implements BooleanType {
  @Override
  public BooleanExpressionImpl importExpression(
      Expression expression) {
    switch( expression.getKind() ) {
    case EQUAL:
      assert( expression.getArity() == 2 );
      return BooleanExpressionImpl.mkEq(getExpressionManager(),
          (Expression) expression.getChild(0), (Expression) expression
              .getChild(1));
    
    default:
      return super.importExpression(expression).asBooleanExpression();
    }
  }


  BooleanTypeImpl(ExpressionManagerImpl expressionManager) {
    super(expressionManager);
      setCVC4Type(expressionManager
          .getTheoremProver()
          .getCvc4ExprManager()
          .booleanType());
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.BOOLEAN;
  }

  @Override
  public BooleanVariableImpl variable(String name, boolean fresh) {
    return new BooleanVariableImpl(getExpressionManager(), name, fresh);
  }
  
  @Override
  public BooleanBoundVariableImpl boundVariable(String name, boolean fresh) {
    return new BooleanBoundVariableImpl(getExpressionManager(), name, fresh);
  }

  @Override
  public String getName() {
    return "BOOLEAN";
  }

  @Override
  public BooleanExpressionImpl and(Expression a, Expression b) {
    return BooleanExpressionImpl.mkAnd(getExpressionManager(),a, b);
  }

  @Override
  public BooleanExpressionImpl and(Expression first, Expression... rest) {
    return BooleanExpressionImpl.mkAnd(getExpressionManager(),Lists.asList(first, rest));
  }

  @Override
  public BooleanExpressionImpl and(Iterable<? extends Expression> subExpressions) {
    // TODO: Check for proper typing
    ImmutableList<? extends Expression> subList = ImmutableList
        .copyOf(subExpressions);
    if (!subList.isEmpty()) {
      // Create the and expression
      return BooleanExpressionImpl.mkAnd(getExpressionManager(),subList);
    }
    return tt();
  }

  @Override
  public BooleanExpressionImpl iff(Expression a, Expression b) {
    // TODO: Check for proper typing
    return BooleanExpressionImpl.mkIff(getExpressionManager(),a, b);
  }

  @Override
  public BooleanExpressionImpl implies(Expression a, Expression b) {
    // Create the and expression
    return BooleanExpressionImpl.mkImplies(getExpressionManager(),a, b);
  }

  @Override
  public BooleanExpressionImpl not(Expression a) {
    return BooleanExpressionImpl.mkNot(getExpressionManager(),a);
  }

  @Override
  public BooleanExpressionImpl or(Expression a, Expression b) {
    return BooleanExpressionImpl.mkOr(getExpressionManager(),a, b);
  }
  
  @Override
  public BooleanExpressionImpl or(Iterable<? extends Expression> subExpressions) {
  	if (subExpressions.iterator().hasNext()) {
  		return BooleanExpressionImpl.mkOr(getExpressionManager(),subExpressions);
  	}
  	return ff();
  }

  @Override
  public BooleanExpressionImpl or(Expression... subExpressions) {
    return or(Arrays.asList(subExpressions));
  }

  @Override
  public BooleanExpressionImpl xor(Expression a, Expression b) {
    return BooleanExpressionImpl.mkXor(getExpressionManager(),a,b);
  }

  @Override
  public BooleanExpressionImpl ff() {
    return BooleanExpressionImpl.mkFalse(getExpressionManager());
  }

  @Override
  public BooleanExpressionImpl tt() {
    return BooleanExpressionImpl.mkTrue(getExpressionManager());
  }

  @Override
  public BooleanExpressionImpl exists(Iterable<? extends Expression> vars,
      Expression body) {
  	return BooleanExpressionImpl.mkExists(getExpressionManager(),vars, body);
  }

  @Override
  public BooleanExpressionImpl forall(Iterable<? extends Expression> vars,
      Expression body) {
    return BooleanExpressionImpl.mkForall(getExpressionManager(),vars, body);
  }
  
  @Override
  public BooleanExpressionImpl forall(Iterable<? extends Expression> vars,
      Expression body,
      Iterable<? extends Expression> triggers) {
    return BooleanExpressionImpl.mkForall(getExpressionManager(),vars, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rewriteRule(Iterable<? extends VariableExpression> vars, 
      Expression guard, Expression rule) {
    return BooleanExpressionImpl.mkRewriteRule(getExpressionManager(), vars, guard, rule);
  }
  
  @Override
  public BooleanExpressionImpl rrRewrite(Expression head, Expression body, 
  		Iterable<? extends Expression> triggers) {
    return BooleanExpressionImpl.mkRRRewrite(getExpressionManager(), head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrRewrite(Expression head, Expression body) {
    return BooleanExpressionImpl.mkRRRewrite(getExpressionManager(), head, body);
  }
  
  @Override
  public BooleanExpressionImpl rrReduction(Expression head, Expression body, 
  		Iterable<? extends Expression> triggers) {
    return BooleanExpressionImpl.mkRRReduction(getExpressionManager(), head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrReduction(Expression head, Expression body) {
    return BooleanExpressionImpl.mkRRReduction(getExpressionManager(), head, body);
  }
  
  @Override
  public BooleanExpressionImpl rrDeduction(Expression head, Expression body, 
  		Iterable<? extends Expression> triggers) {
    return BooleanExpressionImpl.mkRRDeduction(getExpressionManager(), head, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl rrDeduction(Expression head, Expression body) {
    return BooleanExpressionImpl.mkRRDeduction(getExpressionManager(), head, body);
  }

  @Override
  public void addTrigger(Expression e, Expression p) {
    BooleanExpressionImpl e2 = BooleanExpressionImpl.valueOf(getExpressionManager(),e);
    e2.addTrigger(p);
  }

  @Override
  public void setTriggers(Expression e, Iterable<? extends Expression> triggers) {
    BooleanExpressionImpl e2 = BooleanExpressionImpl.valueOf(getExpressionManager(),e);
    e2.setTriggers(triggers);
  }

  @Override
  public ImmutableList<ImmutableList<? extends Expression>> getTriggers(Expression e) {
    BooleanExpressionImpl e2 = BooleanExpressionImpl.valueOf(getExpressionManager(),e);
    return e2.getTriggers();
  }

  @Override
  public  Expression ifThenElse(Expression cond, Expression thenPart, 
  		Expression elsePart) {
    return ExpressionImpl.mkIte(getExpressionManager(),cond, thenPart, elsePart);
  }

  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers) {
    return BooleanExpressionImpl.mkExists(getExpressionManager(), vars, body, triggers);
  }


  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
  	return exists(vars, body, triggers);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    return forall(vars, body, triggers);
  }
  
  @Override
  public BooleanExpressionImpl distinct(Iterable<? extends Expression> children) {
  	Preconditions.checkArgument(Iterables.size(children) > 1);
  	return BooleanExpressionImpl.mkDistinct(getExpressionManager(), children);
  }
  
  @Override
  public  BooleanExpressionImpl distinct(
      Expression first, Expression second, Expression... rest) {
    return BooleanExpressionImpl.mkDistinct(getExpressionManager(), first,second,rest);
  }
  
  @Override
  public  BooleanExpressionImpl eq(Expression left, Expression right)  {
    return BooleanExpressionImpl.mkEq(getExpressionManager(), left, right);
  }
}
