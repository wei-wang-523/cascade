package edu.nyu.cascade.prover;

import com.google.common.base.Preconditions;

public class SatResult<T> extends QueryResult<SatResult.Type> {
  public static enum Type {
    SAT, UNSAT, UNKNOWN;
  };
  
  public static <T> SatResult<T> unsat(Expression phi) {
    return new SatResult<T>(Type.UNSAT, phi);
  }

  public static <T> SatResult<T> valueOf(Type result,
      Expression phi,
      Iterable<? extends BooleanExpression> assumptions) {
    Preconditions.checkArgument(!Type.UNSAT.equals(result));
    return new SatResult<T>(result, phi, assumptions);
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
  
  public boolean isUnknown() {
  	return Type.UNKNOWN.equals(getType());
  }
}
