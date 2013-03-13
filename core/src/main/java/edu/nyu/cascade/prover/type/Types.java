package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type.DomainType;

public final class Types {
  public static boolean exprHasType(Expression e, Type t) {
    return t.equals(e.getType());
  }

  public static boolean exprHasDomainType(Expression e, DomainType t) {
    return hasDomainType(e.getType(), t);
  }

  public static boolean hasDomainType(Type it, DomainType dt) {
    return dt.equals(it.getDomainType());
  }
}
