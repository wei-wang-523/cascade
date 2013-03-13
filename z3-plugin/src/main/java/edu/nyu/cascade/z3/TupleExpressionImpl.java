package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.TUPLE;
import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_UPDATE;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.TupleSort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Type;

public final class TupleExpressionImpl extends ExpressionImpl implements
    TupleExpression {
  static TupleExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Expression first, Expression... rest) {
    return new TupleExpressionImpl(exprManager, type, Lists.asList(first, rest));
  }

  static TupleExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(!Iterables.isEmpty(elements));
    return new TupleExpressionImpl(exprManager, type, elements);
  }

  static TupleExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
      Expression tuple, final int index, Expression val) {
    Preconditions.checkArgument(tuple.isTuple());
    Preconditions.checkArgument(0 <= index
        && index < tuple.asTuple().size());
    Preconditions.checkArgument(val.getType().equals(
        tuple.asTuple().getType().getElementTypes().get(index)));

    try {
      return new TupleExpressionImpl(exprManager, TUPLE_UPDATE,
          new BinaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr tuple, Expr val) {
          // FIXME: tuple update is not supported by z3 yet
          throw new UnsupportedOperationException("Unsupported z3 operation");
          /*return em.tupleUpdateExpr(tuple, index, val);*/
        }
      }, tuple, val, tuple.getType());
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  private TupleExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right, Type t) throws Z3Exception {
    super(exprManager, kind, strategy, left, right);
    setType(TupleTypeImpl.valueOf(exprManager,t));
  }

  private TupleExpressionImpl(final ExpressionManagerImpl exprManager, final Type type,
      Iterable<? extends Expression> elements) {
    super (exprManager, TUPLE,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) {
            try {
              return ((TupleSort) exprManager.toZ3Type(type)).MkDecl().Apply(args);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }            
          }
        }, elements);
    setType(type);
  }

  private TupleExpressionImpl(ExpressionImpl tuple) {
    super(tuple);
  }
  
  @Override
  public TupleTypeImpl getType() {
    return (TupleTypeImpl) super.getType();
  }

  @Override
  public Expression index(int i) {
    TupleSort tupleSort = (TupleSort) getExpressionManager().toZ3Type(getType());
    Expr expr = null;
    try {
      expr = tupleSort.FieldDecls()[i].Apply(getZ3Expression());
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }    
    return getExpressionManager().toExpression(expr);
  }

  @Override
  public int size() {
    return getType().size();
  }

  @Override
  public TupleExpressionImpl update(int index, Expression val) {
    return mkUpdate(getExpressionManager(), this, index, val);
  }

  static TupleExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      ExpressionImpl expr) {
    Preconditions.checkArgument(expr.isTuple());
    if( expr instanceof TupleExpressionImpl ) {
      return (TupleExpressionImpl) expr;
    } else {
      return new TupleExpressionImpl((ExpressionImpl) expr);
    }
  }
}
