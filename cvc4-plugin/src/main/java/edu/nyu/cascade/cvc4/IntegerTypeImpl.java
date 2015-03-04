package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.IntegerType;

class IntegerTypeImpl extends TypeImpl implements IntegerType {
  
	IntegerTypeImpl(ExpressionManagerImpl expressionManager) {
    super(expressionManager);
    setCVC4Type(expressionManager
        .getTheoremProver()
        .getCvc4ExprManager()
        .integerType());
  }

  protected IntegerTypeImpl(ExpressionManagerImpl expressionManager,
      BinaryConstructionStrategy strategy, Expression expr1,
      Expression expr2) {
    super(expressionManager, strategy, expr1, expr2);
  }

  protected IntegerTypeImpl(ExpressionManagerImpl em, UnaryConstructionStrategy strategy,
      Expression expr) {
    super(em, strategy, expr);
  }

  @Override
  public IntegerExpressionImpl add(
      Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),a, b);
  }
  
  @Override
  public IntegerExpressionImpl add(
      Expression first,
      Expression... rest) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),Lists.asList(first, rest));
  }

  @Override
  public IntegerExpressionImpl add(
      Iterable<? extends Expression> addends) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),addends);
  }

  @Override
  public IntegerExpressionImpl divide(Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkDivide(getExpressionManager(), a, b);
  }

  @Override
  public IntegerExpressionImpl mod(Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkModulous(getExpressionManager(), a, b);
  }

  @Override
  public BooleanExpressionImpl geq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkGeq(getExpressionManager(),a, b);  
    }
  
  @Override
  public BooleanExpressionImpl sgeq(Expression a,
      Expression b) {
    throw new UnsupportedOperationException();
  }
  
  @Override
  public DomainType getDomainType() {
    return DomainType.INTEGER;
  }

  @Override
  public String getName() {
    return "INT";
  }

  @Override
  public BooleanExpressionImpl gt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkGt(getExpressionManager(),a, b);  
  }
  
  @Override
  public BooleanExpression sgt(Expression a, 
      Expression b) {
    return gt(a, b);
  }

  @Override
  public BooleanExpressionImpl leq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkLeq(getExpressionManager(),a, b);
  }
  
  @Override
  public BooleanExpression sleq(Expression a, 
      Expression b) {
    return leq(a, b);
  }

  @Override
  public BooleanExpressionImpl lt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkLt(getExpressionManager(),a, b);
  }

  @Override
  public BooleanExpression slt(Expression a, Expression b) {
    return lt(a, b);
  }
  
  @Override
  public IntegerExpressionImpl mult(
      Expression left,
      Expression right) {
    return IntegerExpressionImpl.mkMult(getExpressionManager(),left,right);
  }

  @Override
  public IntegerExpressionImpl mult(
      Iterable<? extends Expression> terms) {
    return IntegerExpressionImpl.mkMult(getExpressionManager(),terms);
  }

  @Override
  public IntegerExpressionImpl negate(Expression a) {
    return IntegerExpressionImpl.mkUminus(getExpressionManager(),a);
  }

  @Override
  public IntegerExpressionImpl one() {
    return IntegerExpressionImpl.mkConstant(getExpressionManager(),1);
  }

  @Override
  public IntegerExpressionImpl pow(Expression base,
      Expression exp) {
    return IntegerExpressionImpl.mkPow(getExpressionManager(),base,exp);
  }

  @Override
  public IntegerExpressionImpl subtract(
      Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkMinus(getExpressionManager(),a, b);
  }

  @Override
  public IntegerVariableImpl variable(String name, boolean fresh) {
    return new IntegerVariableImpl(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public IntegerBoundVariableImpl boundVar(String name, boolean fresh) {
    return IntegerBoundVariableImpl.create(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public IntegerBoundVariableImpl boundExpression(String name, int index, boolean fresh) {
    return boundVar(name, fresh);
  }

  @Override
  public IntegerExpressionImpl zero() {
    return IntegerExpressionImpl.mkConstant(getExpressionManager(),0);
  }
  
	@Override
	IntegerExpressionImpl createExpression(Expr res, Expression e, Kind kind,
			Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isInteger());
		return IntegerExpressionImpl.create(getExpressionManager(), 
				kind, res, e.getType().asInteger(), children);
	}
}
