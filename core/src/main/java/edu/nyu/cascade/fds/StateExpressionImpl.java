package edu.nyu.cascade.fds;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import xtc.tree.GNode;

import com.google.common.base.Preconditions;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.RationalVariableExpression;
import edu.nyu.cascade.prover.TupleExpression;
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

  private StateExpressionImpl primedVersion, unprimedVersion;

  @Inject
  protected StateExpressionImpl(@Assisted Expression expression) {
    this.expression = expression;
  }

  @Override
  public ArrayExpression asArray() {
    return expression.asArray();
  }

/*  @Override
  public ArrayExpression asArray(Type indexType) {
    return expression.asArray(indexType);
  }

  public ArrayExpression asArray(
      Type indexType, Type elementType) {
    return expression.asArray(indexType, elementType);
  }*/

  public BitVectorExpression asBitVector() {
    return expression.asBitVector();
  }

  public StateProperty asBooleanExpression() {
    return StatePropertyImpl.valueOf( expression.asBooleanExpression() );
  }

  public IntegerStateExpression asIntegerExpression() {
    return new IntegerStateExpressionImpl(expression.asIntegerExpression());
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
  public StateProperty asStateProperty() {
    Preconditions.checkState(isBoolean());
    return StatePropertyImpl.valueOf(asBooleanExpression());
  }

  @Override
  public FunctionExpression asFunctionExpression() {
    return expression.asFunctionExpression();
  }

  @Override
  public StateVariable asVariable() {
    return StateVariableImpl.valueOf( expression.asVariable() );
  }

  @Override
  public StatePropertyImpl eq(Expression e) {
    /*
     * [chris 10/23/2009] TODO: e.toExpression() is theoretically unnecessary
     * here, since an StateExpression is an Expression, but it routes around
     * conversion problems we have at the ExpressionManager level (since
     * cleanly converting from StateExpression to Expression is not possible in the
     * general case, due to the lack of operator information). See also: neq.
     * 
     * NOTE: no more e.toExpression() bc we take Expression's not StateExpression's,
     * but we may still have problems with automatic conversions?
     */
    return StatePropertyImpl.valueOf(expression.eq(e));
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof StateExpressionImpl)
      return expression.equals(((StateExpressionImpl) o).expression);
    else
      return false;
  }
/*
  @SuppressWarnings("unchecked")
  @Override
  public StatePropertyImpl geq(StateExpression e) {
    Preconditions.checkArgument(getType() instanceof ComparableType<?>);
    return StatePropertyImpl.create(getExpressionManager().geq(
        (Expression) expression, (Expression) e));
  }*/

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

/*  @SuppressWarnings("unchecked")
  @Override
  public StatePropertyImpl gt(StateExpression e) {
    Preconditions.checkArgument(getType() instanceof ComparableType<?>);
    return StatePropertyImpl.create(getExpressionManager().gt(
        (Expression) expression, (Expression) e));
  }
*/
  @Override
  public int hashCode() {
    return expression.hashCode();
  }

/*  @Override
  public StatePropertyImpl iff(StateExpression e) {
    return StatePropertyImpl.create(getExpressionManager().iff(expression.asBooleanExpression(), e.toExpression().asBooleanExpression()));
  }*/


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

/*  @SuppressWarnings("unchecked")
  @Override
  public StatePropertyImpl leq(StateExpression e) {
    Preconditions.checkArgument(getType() instanceof ComparableType<?>);
    return StatePropertyImpl.create(getExpressionManager().leq(
        (Expression) expression, (Expression) e));
  }
*/
/*  @SuppressWarnings("unchecked")
  @Override
  public StatePropertyImpl lt(StateExpression e) {
    Preconditions.checkArgument(getType() instanceof ComparableType<?>);
    return StatePropertyImpl.create(getExpressionManager().lt(
        (Expression) expression, (Expression) e));
  }*/

  @Override
  public StateProperty neq(Expression e) {
    /*
     * NOTE: see eq() for the reasoning behind e.toExpression()
     * 
     * NOTE (2): previous note is no longer applicable, but the same bug might
     * still be a danger.
     */
    return StatePropertyImpl.valueOf(expression.neq(e));
  }

  @Override
  public StateExpressionImpl prime() {
//    IOUtils.debug().indent().pln(">> PRIMING EXPR: " + this);
    if (primedVersion == null) {
//      IOUtils.debug().indentMore();
      ArrayList<Expression> oldExprs = new ArrayList<Expression>();
      ArrayList<Expression> newExprs = new ArrayList<Expression>();

      LinkedList<Expression> worklist = new LinkedList<Expression>();
      worklist.addAll(expression.getChildren());

      while (!worklist.isEmpty()) {
        Expression e = worklist.remove();
        if (e.isVariable()) {
          // assert( e.getType() instanceof ComparableType );
          StateVariable sv = StateVariableImpl.lookup((VariableExpression) e
              .getExpressionManager().asVariable(e));
          oldExprs.add(sv);
          newExprs.add(sv.prime());
        }
        worklist.addAll(e.getChildren());
      }

      primedVersion = valueOf(expression.subst(oldExprs, newExprs));
      primedVersion.unprimedVersion = this;
//      IOUtils.debug().indentLess();
//      IOUtils.debug().indent().pln("<< got " + primedVersion);
    } else {
//      IOUtils.debug().indent().pln("<< already had primed " + this).indent()
//          .pln("   got: " + primedVersion);
    }
    
    return primedVersion;
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
  public StateExpression unprime() {
    Preconditions.checkArgument(unprimedVersion != null);
    return unprimedVersion;
  }

  public InductiveExpression asInductive() {
    return expression.asInductive();
  }

  public TupleExpression asTuple() {
    return expression.asTuple();
  }

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
}
