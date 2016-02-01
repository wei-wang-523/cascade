package edu.nyu.cascade.prover;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

abstract class QueryResult<R> {
  private final ImmutableList<BooleanExpression> assumptions;
  private final Expression query;
  private final R result;
  private final ImmutableList<BooleanExpression> certificate;
  private final String unknown_reason;

  protected QueryResult(R result, Expression query) {
    this(result, query, ImmutableList.<BooleanExpression>of());
  }

  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions) {
    this(result, query, assumptions, ImmutableList.<BooleanExpression>of());
  }

  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions,
      Iterable<? extends Expression> certificate) {
    this(result, query, assumptions, certificate, null);
  }
  
  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions,
      String reason) {
    this(result, query, assumptions, ImmutableList.<BooleanExpression>of(), reason);
  }
  
  protected QueryResult(R result, Expression query,
      Iterable<? extends BooleanExpression> assumptions,
      Iterable<? extends Expression> certificate,
      String unknownReason) {
    Preconditions.checkNotNull(result);
    Preconditions.checkNotNull(query);
    Preconditions.checkNotNull(assumptions);
    Preconditions.checkNotNull(certificate);
    Preconditions.checkArgument(Iterables.all(certificate, new Predicate<Expression>() {
			@Override
      public boolean apply(Expression input) {
	      return input.isBoolean();
      }
    }));
    this.result = result;
    this.query = query;
    this.assumptions = ImmutableList.copyOf(assumptions);
    this.certificate = ImmutableList.copyOf(Iterables.transform(certificate, 
    		new Function<Expression, BooleanExpression>(){
					@Override
          public BooleanExpression apply(Expression input) {
	          return input.asBooleanExpression();
          }
    }));
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

  /**
   * When <code>isValid()</code> returns <code>false</code>, gives an
   * inconsistent set of assertions that are implied by the assumptions and the
   * formula. E.g., for the formula <code>x > 0 ∧ x = 1 ∧ x < 0</code>,
   * <code>getCounterExample()</code> might return the set
   * <code>{ x > 0, x < 0 }</code>.
   */
  protected ImmutableList<BooleanExpression> getCertificate() {
    return certificate;
  }
  
  @Override
  public String toString() {
    return getType().toString();
  }

}
