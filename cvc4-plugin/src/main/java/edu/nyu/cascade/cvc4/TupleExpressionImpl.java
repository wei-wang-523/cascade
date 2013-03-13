package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.TUPLE;
import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_UPDATE;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Type;

public final class TupleExpressionImpl extends ExpressionImpl implements
    TupleExpression {
  static TupleExpressionImpl create(ExpressionManagerImpl exprManager,
      Expression first, Expression... rest) {
    return new TupleExpressionImpl(exprManager, Lists.asList(first, rest));
  }

  static TupleExpressionImpl create(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(!Iterables.isEmpty(elements));
    return new TupleExpressionImpl(exprManager, elements);
  }

  static TupleExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
      Expression tuple, final int index, Expression val) {
    Preconditions.checkArgument(tuple.isTuple());
    Preconditions.checkArgument(0 <= index
        && index < tuple.asTuple().size());
    Preconditions.checkArgument(val.getType().equals(
        tuple.asTuple().getType().getElementTypes().get(index)));

    return new TupleExpressionImpl(exprManager, TUPLE_UPDATE,
        new BinaryConstructionStrategy() {

          @Override
          public Expr apply(ExprManager em, Expr tuple, Expr val) {
            // FIXME: tuple update is not supported by CVC4 yet
            throw new UnsupportedOperationException("Unsupported cvc4 operation");
            /*return em.tupleUpdateExpr(tuple, index, val);*/
          }
        }, tuple, val, tuple.getType());
  }

  private TupleExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right, Type t) {
    super(exprManager, kind, strategy, left, right);
    setType(TupleTypeImpl.valueOf(exprManager,t));
  }

  private TupleExpressionImpl(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> elements) {
    super(exprManager, TUPLE, new NaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, List<Expr> args)
          throws Exception {
        vectorExpr argsExpr = new vectorExpr();
        for(Expr arg : args)    argsExpr.add(arg);
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.TUPLE, argsExpr);
      }
    }, elements);

    List<Type> types = Lists.newArrayList();
    // IType[] types = new IType[Iterables.size(elements)];
    for (Expression t : elements) {
      types.add(t.getType());
    }
    /*
     * types[0] = first.getType(); for( int i=0 ; i < rest.length ; i++ ) {
     * types[i+1] = rest[i].getType(); }
     */
    setType(TupleTypeImpl.create(exprManager, types));
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
    return ExpressionImpl.mkTupleIndex(getExpressionManager(), this, i);
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
