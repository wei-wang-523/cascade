package edu.nyu.cascade.prover;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

public abstract class QueryResult<R> {
  private final ImmutableList<BooleanExpression> assumptions;
  private final Expression query;
  private final R result;
  private final String unknown_reason;

  protected QueryResult(R result, Expression query) {
    this(result, query, ImmutableList.<BooleanExpression>of());
  }

  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions) {
    this(result, query, assumptions, null);
  }
  
  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions,
      String unknownReason) {
    Preconditions.checkNotNull(result);
    Preconditions.checkNotNull(query);
    Preconditions.checkNotNull(assumptions);
    this.result = result;
    this.query = query;
    this.assumptions = ImmutableList.copyOf(assumptions);
    this.unknown_reason = unknownReason;
  }

  public ImmutableList<BooleanExpression> getAssumptions() {
    return assumptions;
  }

  public Expression getFormula() {
    return query;
  }

  public R getType() {
    return result;
  }

  public String getUnknown_reason() {
    return unknown_reason;
  }
  
  @Override
  public String toString() {
    return getType().toString();
  }

}
