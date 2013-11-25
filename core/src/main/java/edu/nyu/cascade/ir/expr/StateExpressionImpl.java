package edu.nyu.cascade.ir.expr;

import java.util.List;

import xtc.tree.GNode;
import xtc.util.SymbolTable.Scope;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.RationalVariableExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public class StateExpressionImpl implements StateExpression {
  public static class Factory implements StateExpression.Factory {
    public StateExpressionImpl valueOf( Expression expr ) {
      return StateExpressionImpl.valueOf( expr );
    }
  }
  
  public static StateExpressionImpl valueOf(Expression expression) {
    if (expression instanceof StateExpressionImpl) {
      return (StateExpressionImpl) expression;
    } else {
      return new StateExpressionImpl(expression);
    }
  }

  private final Expression expression;

  private Scope scope;

  @Inject
  protected StateExpressionImpl(@Assisted Expression expression) {
    this.expression = expression;
  }

  @Override
  public ArrayExpression asArray() {
    return expression.asArray();
  }

  @Override
  public BitVectorExpression asBitVector() {
    return expression.asBitVector();
  }

  @Override
  public BooleanExpression asBooleanExpression() {
    return expression.asBooleanExpression();
  }

  @Override
  public IntegerExpression asIntegerExpression() {
    return expression.asIntegerExpression();
  }

  
  public IntegerVariableExpression asIntegerVariable() {
    return expression.asIntegerVariable();
  }
  public RationalExpression asRationalExpression() {
    return expression.asRationalExpression();
  }

  public RationalVariableExpression asRationalVariable() {
    return expression.asRationalVariable();
  }

  @Override
  public FunctionExpression asFunctionExpression() {
    return expression.asFunctionExpression();
  }

  @Override
  public VariableExpression asVariable() {
    return expression.asVariable();
  }

  @Override
  public BooleanExpression eq(Expression e) {
    return expression.eq(e);
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof StateExpressionImpl)
      return expression.equals(((StateExpressionImpl) o).expression);
    else
      return false;
  }

  @Override
  public int getArity() {
    return expression.getArity();
  }

  @Override
  public Expression getChild(int i) {
    return expression.getChild(i);
  }

  @Override
  public List<? extends Expression> getChildren() {
    return expression.getChildren();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return expression.getExpressionManager();
  }

  @Override
  public edu.nyu.cascade.prover.Expression.Kind getKind() {
    return expression.getKind();
  }

  @Override
  public Type getType() {
    return expression.getType();
  }
  
  @Override
  public FunctionType getFuncDecl() {
    return expression.getFuncDecl();
  }
  
  @Override
  public int hashCode() {
    return expression.hashCode();
  }

  public boolean isArray() {
    return expression.isArray();
  }

/*  public <I extends Type<I>> boolean isArray(I indexType) {
    return expression.isArray(indexType);
  }

  public <I extends Type<I>, E extends Type<E>> boolean isArray(I indexType,
      E elementType) {
    return expression.isArray(indexType, elementType);
  }
*/
  public boolean isBitVector() {
    return expression.isBitVector();
  }

  @Override
  public boolean isBoolean() {
    return expression.isBoolean();
  }

  @Override
  public boolean isConstant() {
    return expression.isConstant();
  }

  public boolean isInteger() {
    return expression.isInteger();
  }

  public boolean isFunction() {
    return expression.isFunction();
  }

  @Override
  public boolean isVariable() {
    return expression.isVariable();
  }

  @Override
  public FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars) {
    return expression.lambda(vars);
  }

  @Override
  public FunctionExpression lambda(
      VariableExpression var) {
    return expression.lambda(var);
  }

  @Override
  public BooleanExpression neq(Expression e) {
    return expression.neq(e);
  }

  @Override
  public Expression subst(Expression oldExpr, Expression newExpr) {
    return expression.subst(oldExpr,newExpr);
  }
  
  @Override
  public Expression subst(Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs) {
    return expression.subst(oldExprs, newExprs);
  }

  @Override
  public Expression toExpression() {
    return expression;
  }

  @Override
  public String toString() {
    return expression.toString();
  }
  
  @Override
  public InductiveExpression asInductive() {
    return expression.asInductive();
  }

  @Override
  public TupleExpression asTuple() {
    return expression.asTuple();
  }

  @Override
  public boolean isRational() {
    return expression.isRational();
  }

  public boolean isTuple() {
    return expression.isTuple();
  }

  public boolean isInductive() {
    return expression.isInductive();
  }

  @Override
  public GNode getNode() {
    return expression.getNode();
  }

  @Override
  public Expression setNode(GNode node) {
    return expression.setNode(node);
  }

  @Override
  public RecordExpression asRecord() {
    return expression.asRecord();
  }

  @Override
  public UninterpretedExpression asUninterpreted() {
    return expression.asUninterpreted();
  }

  @Override
  public boolean isRecord() {
    return expression.isRecord();
  }

  @Override
  public boolean isUninterpreted() {
    return expression.isUninterpreted();
  }

	@Override
	public void setScope(Scope _scope) {
		scope = _scope;
	}

	@Override
	public Scope getScope() {
		return scope;
	}
}
