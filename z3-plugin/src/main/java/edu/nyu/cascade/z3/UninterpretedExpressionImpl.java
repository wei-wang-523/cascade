package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.UNINTERPRETED;

import com.google.common.base.Preconditions;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.UninterpretedSort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.prover.type.Type;

public final class UninterpretedExpressionImpl extends ExpressionImpl implements
  UninterpretedExpression {

  static UninterpretedExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      String name) {
    return new UninterpretedExpressionImpl(exprManager, type, name);
  }

  private UninterpretedExpressionImpl(final ExpressionManagerImpl exprManager, 
      final Type type, final String name) {
    super (exprManager, UNINTERPRETED,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            UninterpretedSort sort = (UninterpretedSort) exprManager.toZ3Type(type);
            return ctx.MkConst(name, sort);
          }
        });
    setType(type);
  }

  private UninterpretedExpressionImpl(ExpressionImpl un) {
    super(un);
  }
  
  private UninterpretedExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, UninterpretedType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  protected static UninterpretedExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isUninterpreted());
    return new UninterpretedExpressionImpl(em, kind, expr, type.asUninterpreted(), children);
  }
  
  @Override
  public UninterpretedTypeImpl getType() {
    return (UninterpretedTypeImpl) super.getType();
  }

  static UninterpretedExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      ExpressionImpl expr) {
    Preconditions.checkArgument(expr.isUninterpreted());
    if( expr instanceof UninterpretedExpressionImpl ) {
      return (UninterpretedExpressionImpl) expr;
    } else {
      return new UninterpretedExpressionImpl((ExpressionImpl) expr);
    }
  }
}
