package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.UNINTERPRETED;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.UninterpretedConstant;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.prover.type.Type;

public final class UninterpretedExpressionImpl extends ExpressionImpl implements
    UninterpretedExpression {

  static UninterpretedExpressionImpl create(ExpressionManagerImpl exprManager, Type type, int id) {
    Preconditions.checkArgument(type.isUninterpreted());
    return new UninterpretedExpressionImpl(exprManager, type, id);
  }

  private UninterpretedExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right, Type t) {
    super(exprManager, kind, strategy, left, right);
    setType(TupleTypeImpl.valueOf(exprManager,t));
  }

  private UninterpretedExpressionImpl(final ExpressionManagerImpl exprManager, final Type type, final int id) {
    super(exprManager, UNINTERPRETED, new NullaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em)
          throws Exception {
        edu.nyu.acsys.CVC4.Type cvc4_type = exprManager.toCvc4Type(type);
        Integer cvc4_id = new Integer(id);
        UninterpretedConstant uc = new UninterpretedConstant(cvc4_type, cvc4_id);
        return em.mkConst(uc);
      }
    });
    setType(type);
  }

  private UninterpretedExpressionImpl(ExpressionImpl tuple) {
    super(tuple);
  }
  
  private UninterpretedExpressionImpl(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, UninterpretedType type, Iterable<? extends ExpressionImpl> children) {
    super(exprManager, kind, expr, type);
  }
  
  protected static UninterpretedExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, UninterpretedType type, Iterable<? extends ExpressionImpl> children) {
  	return new UninterpretedExpressionImpl(exprManager, kind, expr, type, children);
  }

  @Override
  public UninterpretedTypeImpl getType() {
    return (UninterpretedTypeImpl) super.getType();
  }
  
  static UninterpretedExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      ExpressionImpl expr) {
    Preconditions.checkArgument(expr.isTuple());
    if (exprManager.equals(expr.getExpressionManager())) {
      if( expr instanceof UninterpretedExpressionImpl ) {
        return (UninterpretedExpressionImpl) expr;
      } else {
        return new UninterpretedExpressionImpl((ExpressionImpl) expr);
      }
    }

    switch (expr.getKind()) {
    default:
      throw new UnsupportedOperationException();
    }
  }
}
