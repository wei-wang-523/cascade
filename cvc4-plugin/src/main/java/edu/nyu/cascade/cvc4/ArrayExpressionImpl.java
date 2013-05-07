package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_UPDATE;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_INDEX;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_STORE_ALL;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.ArrayStoreAll;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public final class ArrayExpressionImpl
    extends ExpressionImpl implements ArrayExpression {
  
  static ArrayExpressionImpl mkUpdate(
      ExpressionManagerImpl exprManager, Expression array,
      Expression index, Expression value) {
    Preconditions.checkArgument(array.isArray());
    Preconditions.checkArgument(array.asArray().getIndexType().equals( index.getType() ));
    Preconditions.checkArgument(array.asArray().getElementType().equals( value.getType() ));
    return new ArrayExpressionImpl(exprManager, ARRAY_UPDATE,
        new TernaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg1, Expr arg2, Expr arg3) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.STORE, arg1, arg2, arg3);
          }
        }, array, index, value);
  }
  
  static ExpressionImpl mkArrayIndex(
      ExpressionManagerImpl exprManager, Expression array,
      Expression index) {
    Preconditions.checkArgument(array.isArray());
    ExpressionImpl result = new ExpressionImpl(exprManager, ARRAY_INDEX,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.SELECT, left, right);
          }
        }, array, index);
    result.setType(array.asArray().getElementType());
    return result;
  }
  
  static ArrayExpressionImpl mkStoreAll(
      ExpressionManagerImpl exprManager, Expression expr,
      Type arrayType) {
    Preconditions.checkArgument(expr.getType().equals(arrayType.asArrayType().getElementType()));
    return new ArrayExpressionImpl(exprManager, ARRAY_STORE_ALL,
        new ArrayStoreAllConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, edu.nyu.acsys.CVC4.Type type, Expr expr) {
            edu.nyu.acsys.CVC4.ArrayType arrayType = new edu.nyu.acsys.CVC4.ArrayType(type);
            ArrayStoreAll arrayStoreAll = new ArrayStoreAll(arrayType, expr);
            return em.mkConst(arrayStoreAll);
          }
        }, arrayType, expr);
  }

  private final Type indexType;
  private final Type elementType;
  private final ArrayType type;

  private ArrayExpressionImpl(ExpressionImpl expr) {
    super(expr);
    this.type = (ArrayType) expr.getType();
    this.indexType = type.getIndexType();
    this.elementType = type.getElementType();
  }
  
  private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      TernaryConstructionStrategy strategy,
      Expression array, Expression index,
      Expression element) {
    super(exprManager, kind, strategy, array, index, element);
    type = array.asArray().getType();
    indexType = type.getIndexType();
    elementType = type.getElementType();
  }

  private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      ArrayStoreAllConstructionStrategy strategy,
      Type arrayType, Expression expr) {
    super(exprManager, kind, strategy, arrayType, expr);
    indexType = arrayType.asArrayType().getIndexType();
    elementType = arrayType.asArrayType().getElementType();
    type = exprManager.arrayType(indexType,elementType);
  }

  @Override
  public ArrayType getType() {
    return type;
  }

  @Override
  public Type getIndexType() {
    return indexType;
  }

  @Override
  public Type getElementType() {
    return elementType;
  }

  @Override
  public ExpressionImpl index(Expression i) {
    return mkArrayIndex(getExpressionManager(), this, i);
  }

  @Override
  public ArrayExpressionImpl update(Expression i, Expression val) {
    return mkUpdate(getExpressionManager(), this, i, val);
  }

  static ArrayExpressionImpl valueOf(ExpressionImpl e) {
    Preconditions.checkArgument(e.isArray());
    if( e instanceof ArrayExpressionImpl ) {
      return (ArrayExpressionImpl) e;
    } else {
      return new ArrayExpressionImpl(e);
    }
  }
}
