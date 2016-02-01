package edu.nyu.cascade.prover;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

public class SatResult<T> extends QueryResult<SatResult.Type> {
  public static enum Type {
    SAT, UNSAT, UNKNOWN;
  };

  public static <T> SatResult<T> unsat(Expression phi) {
    return new SatResult<T>(Type.UNSAT, phi);
  }

  public static <T> SatResult<T> unsat(Expression phi,
      Iterable<? extends BooleanExpression> assumptions) {
    return new SatResult<T>(Type.UNSAT, phi, assumptions);
  }

  public static <T> SatResult<T> valueOf(Type result,
      Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      Iterable<? extends Expression> counterExample) {
    Preconditions.checkArgument(!Type.UNSAT.equals(result));
    return new SatResult<T>(result, phi, assumptions,
        ImmutableList.copyOf(counterExample));
  }
  
  public static <T> SatResult<T> valueOf(Type result,
      Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      String reason) {
    Preconditions.checkArgument(!Type.UNSAT.equals(result));
    return new SatResult<T>(result, phi, assumptions,
        reason);
  }

  private SatResult(Type result, Expression phi) {
    super(result, phi);
  }

  private SatResult(Type result, Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      ImmutableList<? extends Expression> counterExample) {
    super(result, phi, assumptions, counterExample);
  }

  private SatResult(Type result, Expression phi,
      Iterable<? extends BooleanExpression> assumptions) {
    super(result, phi, assumptions);
  }
  
  private SatResult(Type result, Expression phi,
      Iterable<? extends BooleanExpression> assumptions,
      String reason) {
    super(result, phi, assumptions, reason);
  }

  public boolean isSatisfiable() {
    return Type.SAT.equals(getType());
  }

  public boolean isUnsatisfiable() {
    return Type.UNSAT.equals(getType());
  }

  /**
   * When <code>getResultType()</code> returns <code>SATISFIABLE</code>, gives a
   * consistent set of sub-formulas which are sufficient to satisfy the last
   * formula under the given assumptions. E.g., for
   * <code>x > 0 ∨ x = 1 ∨ x < 0</code>, it might return the set
   * <code>{ x > 0 }</code>.
   */
  public ImmutableList<BooleanExpression> getSatisfyingAssertions() {
    return getCertificate();
  }
}
