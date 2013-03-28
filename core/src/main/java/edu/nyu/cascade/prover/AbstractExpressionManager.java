package edu.nyu.cascade.prover;

import java.util.LinkedHashSet;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.inject.internal.Sets;

import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractExpressionManager implements ExpressionManager {
  
  private final LinkedHashSet<VariableExpression> variableSet = Sets.newLinkedHashSet();
  
  @Override
  public BooleanExpression and(Expression first,
      Expression... rest) {
    return and(Lists.asList(first, rest));
  }

  @Override
  public Expression applyExpr(FunctionType func, Expression first,
      Expression... rest) {
    return applyExpr(func, Lists.asList(first, rest));
  }

  @Override
  public BitVectorExpression bitVectorOne(int size) {
    Preconditions.checkArgument(size > 0);
    return bitVectorConstant(1, size);
  }

  @Override
  public BitVectorExpression bitVectorZero(int size) {
    Preconditions.checkArgument(size > 0);
    return bitVectorConstant(0, size);
  }

  @Override
  public BitVectorExpression concat(Expression left,
      Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isBitVectorType());
    return type.asBitVectorType().concat(left, right);
  }

  @Override
  public BooleanExpression exists(Expression var,
      Expression body) {
    return exists(ImmutableList.of(var), body);
  }
  
  @Override
  public BooleanExpression exists(Expression var,
      Expression body, Iterable<? extends Expression> patterns) {
    return exists(ImmutableList.of(var), body, patterns);
  }
  
  @Override
  public BooleanExpression exists(Expression var,
      Expression body, Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return exists(ImmutableList.of(var), body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression body) {
    return exists(ImmutableList.of(var1, var2), body);
  }
  
  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression body,
      Iterable<? extends Expression> patterns) {
    return exists(ImmutableList.of(var1, var2), body, patterns);
  }
  
  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression body,
      Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return exists(ImmutableList.of(var1, var2), body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression var3,
      Expression body) {
    return exists(ImmutableList.of(var1, var2, var3), body);
  }
  
  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression var3,
      Expression body, Iterable<? extends Expression> patterns) {
    return exists(ImmutableList.of(var1, var2, var3), body, patterns);
  }
  
  @Override
  public BooleanExpression exists(Expression var1,
      Expression var2, Expression var3,
      Expression body, Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return exists(ImmutableList.of(var1, var2, var3), body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression forall(Expression var,
      Expression body) {
    return forall(ImmutableList.of(var), body);
  }
  
  @Override
  public BooleanExpression forall(Expression var,
      Expression body, Iterable<? extends Expression> patterns) {
    return forall(ImmutableList.of(var), body, patterns);
  }
  
  @Override
  public BooleanExpression forall(Expression var, Expression body, 
      Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return forall(ImmutableList.of(var), body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression forall(Expression var1, Expression var2, Expression body) {
    return forall(ImmutableList.of(var1, var2), body);
  }
  
  @Override
  public BooleanExpression forall(Expression var1, Expression var2, Expression body,
      Iterable<? extends Expression> patterns) {
    return forall(ImmutableList.of(var1, var2), body, patterns);
  }
  
  @Override
  public BooleanExpression forall(Expression var1,
      Expression var2, Expression body,
      Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return forall(ImmutableList.of(var1, var2), body, patterns, noPatterns);
  }

  @Override
  public BooleanExpression forall(Expression var1, Expression var2, Expression var3,
      Expression body) {
    return forall(ImmutableList.of(var1, var2, var3), body);
  }
  
  @Override
  public BooleanExpression forall(Expression var1, Expression var2, Expression var3,
      Expression body, Iterable<? extends Expression> patterns) {
    return forall(ImmutableList.of(var1, var2, var3), body, patterns);
  }
  
  @Override
  public BooleanExpression forall(Expression var1, Expression var2, Expression var3,
      Expression body, Iterable<? extends Expression> patterns,
      Iterable<? extends Expression> noPatterns) {
    return forall(ImmutableList.of(var1, var2, var3), body, patterns, noPatterns);
  }

  @Override
  public FunctionType functionType(String fname, Type argType1,
      Type argType2, Type... rest) {
    List<Type> argTypes = Lists.newArrayList(argType1);
    Type range = argType2;
    
    if( rest.length > 0 ) {
      argTypes.add(argType2);
      for( int i = 0; i < rest.length - 1; i++ ) {
        argTypes.add(rest[i]);
      }
      range = rest[rest.length-1];
    } 
    return functionType(fname, argTypes, range);
  }
  
  @Override
  public FunctionType functionType(String fname, Type argType, Type range) {
    List<Type> argTypes = Lists.newArrayList(argType);
    return functionType(fname, argTypes, range);
  }

  @Override
  public BooleanExpression greaterThanOrEqual(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().geq(left, right);
  }
  
  @Override
  public BooleanExpression signedGreaterThanOrEqual(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().sgeq(left, right);
  }

  @Override
  public BooleanExpression greaterThan(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().gt(left, right);
  }
  
  @Override
  public BooleanExpression signedGreaterThan(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().sgt(left, right);
  }

  @Override
  public FunctionExpression lambda(
      VariableExpression var1, VariableExpression var2,
      Expression expr) {
    return lambda(ImmutableList.of(var1, var2), expr);
  }

  @Override
  public BooleanExpression lessThanOrEqual(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().leq(left, right);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().sleq(left, right);
  }

  @Override
  public BooleanExpression lessThan(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().lt(left, right);
  }
  
  @Override
  public BooleanExpression signedLessThan(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isComparableType());
    return type.asComparableType().slt(left, right);
  }

  @Override
  public Expression minus(Expression left,
      Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isAddableType());
    return type.asAddableType().subtract(left, right);
  }

  @Override
  public Expression mult(
      Expression left, Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isMultiplicativeType());    
    return type.asMultiplicativeType().mult(left, right);
  }

  @Override
  public Expression mult(
      List<? extends Expression> children) {
    if (children.isEmpty()) {
      throw new IllegalArgumentException("No addends in plus");
    } else {
      Expression child = children.get(0);
      Type type = child.getType();
      Preconditions.checkArgument(type.isMultiplicativeType());    
      return type.asMultiplicativeType().mult(children);
    }
  }

  @Override
  public Expression negate(Expression a) {
    Type type = a.getType();
    Preconditions.checkArgument(type.isAddableType());  
    return type.asAddableType().negate(a);
  }

  @Override
  public IntegerExpression negativeOne() {
    return constant(-1);
  }

  @Override
  public BooleanExpression neq(Expression arg0,
      Expression arg1) {
    return not(eq(arg0, arg1));
  }

  @Override
  public IntegerExpression one() {
    return constant(1);
  }

  @Override
  public Expression plus(Expression left,
      Expression right) {
    Type type = left.getType();
    Preconditions.checkArgument(type.isAddableType());
    return type.asAddableType().add(left, right);
  }

  @Override
  public Expression plus(Expression first,
      Expression... rest) {
    return plus(Lists.asList(first, rest));
  }

  @Override
  public Expression plus(
      Iterable<? extends Expression> children) {
    if (Iterables.isEmpty(children)) {
      throw new IllegalArgumentException("No addends in plus");
    } else {
      Expression child = Iterables.get(children, 0);
      Type type = child.getType();
      Preconditions.checkArgument(type.isAddableType());
      return type.asAddableType().add(children);
    }
  }

  @Override
  public VariableExpression variable(String name,
      Type type, boolean fresh) {
    VariableExpression res = type.variable(name, fresh);
    variableSet.add(res);
    return res;
  }

  @Override
  public IntegerExpression zero() {
    return constant(0);
  }
  
  @Override
  public LinkedHashSet<VariableExpression> getVariables() {
    return variableSet;
  }
}
