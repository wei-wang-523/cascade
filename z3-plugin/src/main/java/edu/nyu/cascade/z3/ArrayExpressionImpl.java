package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_STORE_ALL;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_UPDATE;

import com.google.common.base.Preconditions;

import com.microsoft.z3.Expr;
import com.microsoft.z3.ArrayExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Sort;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
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
      public Expr apply(Context ctx, Expr arg1, Expr arg2, Expr arg3) {
        try {
          return ctx.MkStore((ArrayExpr) arg1, arg2, arg3);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, array, index, value);
  }
  
  static ArrayExpressionImpl mkStoreAll(
      ExpressionManagerImpl exprManager, Expression expr,
      Type arrayType) {
    Preconditions.checkArgument(expr.getType().equals(arrayType.asArrayType().getElementType()));
    return new ArrayExpressionImpl(exprManager, ARRAY_STORE_ALL,
        new ArrayStoreAllConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Sort type, Expr expr) {
            try {
              return ctx.MkConstArray(type, expr);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
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
