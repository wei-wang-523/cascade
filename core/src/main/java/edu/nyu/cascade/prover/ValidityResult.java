package edu.nyu.cascade.prover;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

public class ValidityResult<T> extends QueryResult<ValidityResult.Type> {
  public static enum Type {
    VALID, INVALID, UNKNOWN;
  }

  public static <T> ValidityResult<T> valid(Expression phi) {
    return new ValidityResult<T>(Type.VALID, phi);
  }

  public static <T> ValidityResult<T> valueOf(Type result,
      Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      Iterable<? extends BooleanExpression> counterExample) {
    Preconditions.checkArgument(!Type.VALID.equals(result));
    return new ValidityResult<T>(result, phi, assumptions, counterExample);
  }
  
  public static <T> ValidityResult<T> valueOf(Type result,
      Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      String reason) {
    Preconditions.checkArgument(!Type.VALID.equals(result));
    return new ValidityResult<T>(result, phi, assumptions, reason);
  }

  private ValidityResult(Type result, Expression phi) {
    super(result, phi);
  }

  private ValidityResult(Type result, Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      Iterable<? extends BooleanExpression> counterExample) {
    super(result, phi, assumptions, counterExample);
  }
  
  private ValidityResult(Type result, Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      String reason) {
    super(result, phi, assumptions, reason);
  }

  public boolean isValid() {
    return Type.VALID.equals(getType());
  }

  public boolean isInvalid() {
    return Type.INVALID.equals(getType());
  }
  
  public boolean isUnknown() {
    return Type.UNKNOWN.equals(getType());
  }

  /**
   * When <code>isValid()</code> returns <code>false</code>, gives an
   * inconsistent set of assertions that are implied by the assumptions and the
   * formula. E.g., for the formula <code>x > 0 ∧ x = 1 ∧ x < 0</code>,
   * <code>getCounterExample()</code> might return the set
   * <code>{ x > 0, x < 0 }</code>.
   */
  public ImmutableList<BooleanExpression> getCounterExample() {
    return getCertificate();
  }
}
