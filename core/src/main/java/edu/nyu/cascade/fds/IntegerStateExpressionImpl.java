package edu.nyu.cascade.fds;

import java.util.List;

import xtc.tree.GNode;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.RationalVariableExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ComparableType;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.IntegerType;

public class IntegerStateExpressionImpl implements IntegerStateExpression {
  private final StateExpression expr;
  
  public IntegerStateExpressionImpl(Expression expr) {
    this( StateExpressionImpl.valueOf(expr) );
    Preconditions.checkArgument(expr.isInteger());
  }
  
  public IntegerStateExpressionImpl(StateExpression expr) {
    this.expr = expr;
  }

  @Override
  public ArrayExpression asArray() {
    return expr.asArray();
  }

/*  @Override
  public <I extends Type<I>> ArrayExpression asArray(I indexType) {
    return expr.asArray(indexType);
  }

  @Override
  public <I extends Type<I>, E extends Type<E>> ArrayExpression asArray(
      I indexType, E elementType) {
    return expr.asArray(indexType, elementType);
  }
*/  
  @Override
  public BitVectorExpression asBitVector() {
    return expr.asBitVector();
  }

  @Override
  public StateProperty asBooleanExpression() {
    return expr.asBooleanExpression();
  }

  @Override
  public IntegerStateExpression asIntegerExpression() {
    return this;
  }

  @Override
  public IntegerVariableExpression asIntegerVariable() {
    return expr.asIntegerVariable();
  }

  @Override
  public RationalExpression asRationalExpression() {
    return expr.asRationalExpression();
  }

  @Override
  public RationalVariableExpression asRationalVariable() {
    return expr.asRationalVariable();
  }

  @Override
  public StateProperty asStateProperty() {
    return expr.asStateProperty();
  }

  @Override
  public FunctionExpression asFunctionExpression() {
    return expr.asFunctionExpression();
  }

  @Override
  public StateVariable asVariable() {
    return expr.asVariable();
  }

  @Override
  public RationalExpression castToRational() {
    return expr.toExpression().asIntegerExpression().castToRational();
  }

  @Override
  public StateProperty eq(Expression e) {
    return expr.eq(e);
  }

  @Override
  public int getArity() {
    return expr.getArity();
  }

  @Override
  public Expression getChild(int i) {
    return expr.getChild(i);
  }

  @Override
  public List<? extends Expression> getChildren() {
    return expr.getChildren();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return expr.getExpressionManager();
  }

  @Override
  public Kind getKind() {
    return expr.getKind();
  }

  @Override
  public IntegerType getType() {
    return getExpressionManager().integerType();
  }
  
  @Override
  public FunctionType getFuncDecl() {
    return expr.getFuncDecl();
  }

  @Override
  public StateProperty greaterThan(Expression e) {
    Preconditions.checkArgument(getType() instanceof ComparableType);
    return StatePropertyImpl.valueOf(expr.toExpression().asIntegerExpression()
        .greaterThan(e));
  }

  @Override
  public StateProperty greaterThanOrEqual(Expression e) {
    Preconditions.checkArgument(e.isInteger());
    return StatePropertyImpl.valueOf(expr.toExpression().asIntegerExpression().greaterThanOrEqual(e));
  }

  @Override
  public boolean isArray() {
    return expr.isArray();
  }

/*  @Override
  public <I extends Type<I>> boolean isArray(I indexType) {
    return expr.isArray(indexType);
  }

  @Override
  public <I extends Type<I>, E extends Type<E>> boolean isArray(I indexType,
      E elementType) {
    return expr.isArray(indexType, elementType);
  }*/

  @Override
  public boolean isBitVector() {
    return expr.isBitVector();
  }

  @Override
  public boolean isBoolean() {
    return expr.isBoolean();
  }

  @Override
   public boolean isConstant() {
    return expr.isConstant();
  }

  @Override
  public boolean isInteger() {
    return expr.isInteger();
  }

  @Override
  public boolean isFunction() {
    return expr.isFunction();
  }

  @Override
  public boolean isVariable() {
    return expr.isVariable();
  }

  @Override
  public FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars) {
    return expr.lambda(vars);
  }

  @Override
  public FunctionExpression lambda(
      VariableExpression var) {
    return expr.lambda(var);
  }

  @Override
  public StateProperty lessThan(Expression e) {
    Preconditions.checkArgument(e.isInteger());
    return StatePropertyImpl.valueOf(expr.toExpression().asIntegerExpression().lessThan(e));
  }

  @Override
  public StateProperty lessThanOrEqual(Expression e) {
    Preconditions.checkArgument(e.isInteger());
    return StatePropertyImpl.valueOf(expr.toExpression().asIntegerExpression().lessThanOrEqual(e));
  }

  @Override
  public IntegerStateExpression minus(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().minus(e));
  }

  @Override
  public IntegerStateExpression negate() {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().negate());
  }

  @Override
  public StateProperty neq(Expression e) {
    return expr.neq(e);
  }

  @Override
  public IntegerStateExpression plus(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().plus(e));
  }

  @Override
  public IntegerStateExpression pow(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().pow(e));
  }

  @Override
  public IntegerStateExpression prime() {
    return new IntegerStateExpressionImpl(expr.prime());
  }

  @Override
  public IntegerStateExpression subst(Expression oldExpr,
      Expression newExpr) {
    return new IntegerStateExpressionImpl(expr.subst(oldExpr, newExpr));
  }

  @Override
  public IntegerStateExpression subst(
      Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs) {
    return new IntegerStateExpressionImpl(expr.subst(oldExprs, newExprs));
  }

  @Override
  public IntegerStateExpression times(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().times(e));
  }

  @Override
  public IntegerStateExpression divides(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().divides(e));
  }

  @Override
  public IntegerStateExpression mods(Expression e) {
    return new IntegerStateExpressionImpl(expr.toExpression().asIntegerExpression().mods(e));
  }
  
  @Override
  public Expression toExpression() {
    return expr.toExpression();
  }

  @Override
  public IntegerStateExpression unprime() {
    return new IntegerStateExpressionImpl(expr.unprime());
  }

  public InductiveExpression asInductive() {
    return expr.asInductive();
  }

  public TupleExpression asTuple() {
    return expr.asTuple();
  }

  public boolean isRational() {
    return expr.isRational();
  }

  public boolean isTuple() {
    return expr.isTuple();
  }

  public boolean isInductive() {
    return expr.isInductive();
  }

  @Override
  public String toString() {
    return expr.toString();
  }

  @Override
  public GNode getNode() {
    return expr.getNode();
  }

  @Override
  public Expression setNode(GNode node) {
    return expr.setNode(node);
  }

  @Override
  public RecordExpression asRecord() {
    return expr.asRecord();
  }

  @Override
  public UninterpretedExpression asUninterpreted() {
    return expr.asUninterpreted();
  }

  @Override
  public boolean isRecord() {
    return expr.isRecord();
  }

  @Override
  public boolean isUninterpreted() {
    return expr.isUninterpreted();
  }
}
