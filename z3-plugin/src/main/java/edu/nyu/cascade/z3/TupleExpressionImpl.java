package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_INDEX;
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
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

final class TupleExpressionImpl extends ExpressionImpl implements
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

  static TupleExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
	    Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
		Preconditions.checkArgument(type.isTuple());
	  return new TupleExpressionImpl(em, kind, expr, type.asTuple(), children);
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
      }, tuple, val);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  static ExpressionImpl mkTupleIndex(
      ExpressionManagerImpl exprManager, Expression tuple,
      final int index) {
    Preconditions.checkArgument(tuple.isTuple());
    final TupleSort tupleSort = (TupleSort) exprManager.toZ3Type(tuple.getType());
    ExpressionImpl result = new ExpressionImpl(exprManager, TUPLE_INDEX,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr expr) {
              try {
                return tupleSort.getFieldDecls()[index].apply(expr);
              } catch (Z3Exception e) {
                throw new TheoremProverException(e);
              }
          }
        }, tuple);
    result.setType((Type) 
        tuple.asTuple().getType().getElementTypes().toArray()[index]);
    return result;
  }

  private TupleExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression tuple,
      Expression value) throws Z3Exception {
    super(exprManager, kind, strategy, tuple, value);
    setType(TupleTypeImpl.valueOf(exprManager, tuple.getType()));
  }

  private TupleExpressionImpl(final ExpressionManagerImpl exprManager, final Type type,
      Iterable<? extends Expression> elements) {
    super (exprManager, TUPLE,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) {
            try {
              return ((TupleSort) exprManager.toZ3Type(type)).mkDecl().apply(args);
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
  
  private TupleExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, TupleType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  @Override
  public TupleTypeImpl getType() {
    return (TupleTypeImpl) super.getType();
  }

  @Override
  public ExpressionImpl index(int i) {
    return mkTupleIndex(getExpressionManager(), this, i);
  }

  @Override
  public int size() {
    return getType().size();
  }

  @Override
  public TupleExpressionImpl update(int index, Expression val) {
    return mkUpdate(getExpressionManager(), this, index, val);
  }
}
