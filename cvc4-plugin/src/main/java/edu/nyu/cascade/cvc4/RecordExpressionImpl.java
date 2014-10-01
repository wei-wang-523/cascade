package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.RECORD;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD_SELECT;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD_UPDATE;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;

final class RecordExpressionImpl extends ExpressionImpl implements
    RecordExpression {
  static RecordExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Expression first, Expression... rest) {
    return new RecordExpressionImpl(exprManager, type, Lists.asList(first, rest));
  }

  static RecordExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Iterable<? extends Expression> elements) {
    return new RecordExpressionImpl(exprManager, type, elements);
  } 

  static RecordExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
	    Expr expr, RecordType type, Iterable<? extends ExpressionImpl> children) {
		return new RecordExpressionImpl(exprManager, kind, expr, type, children);
	}

	static RecordExpressionImpl valueOf(ExpressionManagerImpl exprManager,
	    ExpressionImpl expr) {
	  Preconditions.checkArgument(expr.isRecord());
	  if( expr instanceof RecordExpressionImpl ) {
	    return (RecordExpressionImpl) expr;
	  } else {
	    return new RecordExpressionImpl((ExpressionImpl) expr);
	  }
	}

	static ExpressionImpl mkRecordIndex(ExpressionManagerImpl exprManager,
      Expression record, final String field) {
    ExpressionImpl result = new ExpressionImpl(exprManager, RECORD_SELECT,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr record) {
            Expr index = em.mkConst(new edu.nyu.acsys.CVC4.RecordSelect(field));
            return em.mkExpr(index, record);
          }
        }, record);
    int index = record.getType().asRecord().getElementNames().indexOf(field);
    result.setType(record.getType().asRecord().getElementTypes().get(index));
    return result;
  }

  static RecordExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
      Expression record, final String field, Expression val) {
    Preconditions.checkArgument(record.isRecord());

    return new RecordExpressionImpl(exprManager, RECORD_UPDATE,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr record, Expr val) {
            Expr index = em.mkConst(new edu.nyu.acsys.CVC4.RecordUpdate(field));
            return em.mkExpr(index, record, val);
          }
        }, record, val);
  }

  private RecordExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right) {
    super(exprManager, kind, strategy, left, right);
    setType(RecordTypeImpl.valueOf(exprManager, left.getType()));
  }

  private RecordExpressionImpl(ExpressionManagerImpl exprManager,
      final Type type, Iterable<? extends Expression> elements) {
    super(exprManager, RECORD, new NaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, List<Expr> args)
          throws Exception {
        vectorExpr argsExpr = new vectorExpr();
        argsExpr.add(em.mkConst(new edu.nyu.acsys.CVC4.RecordType(((TypeImpl)type).getCVC4Type()).getRecord()));
        for(Expr arg : args)    argsExpr.add(arg);
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RECORD, argsExpr);
      }
    }, elements);

    List<Type> types = Lists.newArrayList();
    for (Expression t : elements) {
      types.add(t.getType());
    }
    setType(type);
  }

  private RecordExpressionImpl(ExpressionImpl record) {
    super(record);
  }
  
  private RecordExpressionImpl(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, RecordType type, Iterable<? extends ExpressionImpl> children) {
    super(exprManager, kind, expr, type);
  }
  
  @Override
  public RecordTypeImpl getType() {
    return (RecordTypeImpl) super.getType();
  }
  
  @Override
  public RecordExpressionImpl update(String field, Expression val) {
    return mkUpdate(getExpressionManager(), this, field, val);
  }

  @Override
  public Expression select(String field) {
    return mkRecordIndex(getExpressionManager(), this, field);
  }
}
