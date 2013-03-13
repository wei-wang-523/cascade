package edu.nyu.cascade.util;

import com.google.common.collect.ImmutableList;

import xtc.tree.Node;
import xtc.tree.Visitor;

public final class RecursionStrategies {
  public static interface BinaryRecursionStrategy<T, R> {
    public R apply(T child1, T child2);
  }

  public interface BinaryInfixRecursionStrategy<T,R> {
    public R apply(T op1, String operator, T op2);
  }

  public static interface UnaryRecursionStrategy<T, R> {
    public R apply(T child);
  }
  
  @SuppressWarnings("unchecked")
  public static <T,R> R binaryNode(Node node,
      Visitor visitor,
      BinaryRecursionStrategy<T, R> strategy)
  {
    Node lhsNode = node.getNode(0);
    Node rhsNode = node.getNode(1);

    T lhs = (T) visitor.dispatch(lhsNode);
    T rhs = (T) visitor.dispatch(rhsNode);

    return strategy.apply(lhs, rhs);
  }
  
  @SuppressWarnings("unchecked")
  public static <T,R> R binaryOp(Node node,
      Visitor visitor,
      BinaryInfixRecursionStrategy<T, R> strategy)
  {
    Node lhsNode = node.getNode(0);
    String op = node.getString(1);
    Node rhsNode = node.getNode(2);

    T lhs = (T) visitor.dispatch(lhsNode);
    T rhs = (T) visitor.dispatch(rhsNode);

    return strategy.apply(lhs, op, rhs);
  }
  
  @SuppressWarnings("unchecked")
  public static <T,R> R unaryNode(Node node,
      Visitor visitor,
      UnaryRecursionStrategy<T, R> strategy)
  {
    Node argNode = node.getNode(0);

    T arg = (T) visitor.dispatch(argNode);

    return strategy.apply(arg);
  }
  
  public static <T, R> Iterable<R> unaryRecursionOverList(Iterable<? extends T> list,
      UnaryRecursionStrategy<T, R> unaryRecursionStrategy)
  { ImmutableList.Builder<R> builder = ImmutableList.builder();
    for(T elem : list)
      builder.add((R) unaryRecursionStrategy.apply(elem));
    return builder.build();
  }
}
