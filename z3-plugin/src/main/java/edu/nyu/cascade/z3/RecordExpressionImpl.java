package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.RECORD_SELECT;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD_UPDATE;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.microsoft.z3.Context;
import com.microsoft.z3.DatatypeSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

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

  static RecordExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
	    Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
		Preconditions.checkArgument(type.isRecord());
	  return new RecordExpressionImpl(em, kind, expr, type.asRecord(), children);
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

	static RecordExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
      Expression record, String name, Expression val) {
    Preconditions.checkArgument(record.isRecord());
    final int index = record.getType().asRecord().getElementNames().indexOf(name);
    return new RecordExpressionImpl(exprManager, RECORD_UPDATE,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr record, Expr val) throws Z3Exception {
        Expr[] args = record.getArgs();
        args[index] = val;
        return ctx.mkApp(((DatatypeSort) record.getSort()).getConstructors()[0], args); 
      }
    }, record, val);
  }
  
  static ExpressionImpl mkRecordSelect(
      ExpressionManagerImpl exprManager, Expression record, String name) {
    Preconditions.checkArgument(record.isRecord());
    ExpressionImpl result;
    final int index = record.getType().asRecord().getElementNames().indexOf(name);
    result = new ExpressionImpl(exprManager, RECORD_SELECT,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr expr) throws Z3Exception {
            DatatypeSort recordSort = (DatatypeSort) expr.getSort();                
            return recordSort.getAccessors()[0][index].apply(expr);
          }
        }, record);
    
    Type argType = (Type) record.asRecord().getType().getElementTypes().toArray()[index];
    result.setType(argType);
    return result;
  }

  private RecordExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression record,
      Expression value) {
    super(exprManager, kind, strategy, record, value);
    setType(RecordTypeImpl.valueOf(exprManager, record.getType()));
  }

  private RecordExpressionImpl(final ExpressionManagerImpl exprManager, final Type type,
      Iterable<? extends Expression> elements) {
    super (exprManager, RECORD,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
          	return ((DatatypeSort) exprManager.toZ3Type(type)).getConstructors()[0].apply(args);           
          }
        }, elements);
    setType(type);
  }

  private RecordExpressionImpl(ExpressionImpl record) {
    super(record);
  }
  
  private RecordExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, RecordType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  @Override
  public RecordTypeImpl getType() {
    return (RecordTypeImpl) super.getType();
  }

  @Override
  public Expression select(String name) {
    return mkRecordSelect(getExpressionManager(), this, name);
  }

  @Override
  public RecordExpression update(String name, Expression val) {
    return mkUpdate(getExpressionManager(), this, name, val);
  }
}
