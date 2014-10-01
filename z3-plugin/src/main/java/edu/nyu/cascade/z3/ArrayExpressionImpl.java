package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_INDEX;
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

final class ArrayExpressionImpl
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
          return ctx.mkStore((ArrayExpr) arg1, arg2, arg3);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, array, index, value);
  }
  
  static ExpressionImpl mkArrayIndex(
      ExpressionManagerImpl exprManager, Expression array,
      Expression index) {
    Preconditions.checkArgument(array.isArray());
    ExpressionImpl result;
    result = new ExpressionImpl(exprManager, ARRAY_INDEX,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) {
              try {
                return ctx.mkSelect((ArrayExpr)left, right);
              } catch (Z3Exception e) {
                throw new TheoremProverException(e);
              }
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
          public Expr apply(Context ctx, Sort type, Expr expr) {
            try {
              return ctx.mkConstArray(type, expr);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
        }, arrayType, expr);
  }

  private final Type indexType;
  private final Type elementType;

  private ArrayExpressionImpl(ExpressionImpl expr) {
    super(expr);
    indexType = super.getType().asArrayType().getIndexType();
    elementType = super.getType().asArrayType().getElementType();
  }
  
  private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      TernaryConstructionStrategy strategy,
      Expression array, Expression index,
      Expression element) {
    super(exprManager, kind, strategy, array, index, element);
    indexType = index.getType();
    elementType = element.getType();
  }
  
  private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      ArrayStoreAllConstructionStrategy strategy,
      Type arrayType, Expression expr) {
    super(exprManager, kind, strategy, arrayType.asArrayType().getIndexType(), expr);
    indexType = arrayType.asArrayType().getIndexType();
    elementType = arrayType.asArrayType().getElementType();
  }
  
  private ArrayExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, ArrayType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
    indexType = type.getIndexType();
    elementType = type.getElementType();
  }
  
  static ArrayExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isArrayType());
    return new ArrayExpressionImpl(em, kind, expr, type.asArrayType(), children);
  }

  @Override
  public ArrayType getType() {
    return getExpressionManager().arrayType(indexType, elementType);
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
