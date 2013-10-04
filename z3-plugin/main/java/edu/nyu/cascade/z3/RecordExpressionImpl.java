package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.RECORD_SELECT;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD;
import static edu.nyu.cascade.prover.Expression.Kind.RECORD_UPDATE;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.Context;
import com.microsoft.z3.DatatypeSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.type.Type;

public final class RecordExpressionImpl extends ExpressionImpl implements
    RecordExpression {
  static final String SELECT_PREFIX = "sel@";
  
  static RecordExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Expression first, Expression... rest) {
    return new RecordExpressionImpl(exprManager, type, Lists.asList(first, rest));
  }

  static RecordExpressionImpl create(ExpressionManagerImpl exprManager, Type type,
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(!Iterables.isEmpty(elements));
    return new RecordExpressionImpl(exprManager, type, elements);
  }

  static RecordExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
      Expression record, String name, Expression val) {
    Preconditions.checkArgument(record.isRecord());
    final int index = record.getType().asRecord().getElementNames().indexOf(name);
    try {
      return new RecordExpressionImpl(exprManager, RECORD_UPDATE,
          new BinaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr record, Expr val) throws Z3Exception {
          Expr[] args = record.Args();
          args[index] = val;
          return ctx.MkApp(((DatatypeSort) record.Sort()).Constructors()[0], args); 
        }
      }, record, val);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  static ExpressionImpl mkRecordSelect(
      ExpressionManagerImpl exprManager, Expression record, String name) {
    Preconditions.checkArgument(record.isRecord());
    ExpressionImpl result;
    final int index = record.getType().asRecord().getElementNames().indexOf(name);
    result = new ExpressionImpl(exprManager, RECORD_SELECT,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr expr) {
              try {
                DatatypeSort recordSort = (DatatypeSort) expr.Sort();                
                return recordSort.Accessors()[0][index].Apply(expr);
              } catch (Z3Exception e) {
                throw new TheoremProverException(e);
              }
          }
        }, record);
    
    Type argType = (Type) record.asRecord().getType().getElementTypes().toArray()[index];
    result.setType(argType);
    
    FunctionDeclarator func = FunctionDeclarator.create(
        exprManager, SELECT_PREFIX + name, Lists.newArrayList(record.getType()), argType);
    result.setFuncDecl(func);
    return result;
  }

  private RecordExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression record,
      Expression value) throws Z3Exception {
    super(exprManager, kind, strategy, record, value);
    setType(RecordTypeImpl.valueOf(exprManager, record.getType()));
  }

  private RecordExpressionImpl(final ExpressionManagerImpl exprManager, final Type type,
      Iterable<? extends Expression> elements) {
    super (exprManager, RECORD,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) {
            try {
              return ((DatatypeSort) exprManager.toZ3Type(type)).Constructors()[0].Apply(args);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }            
          }
        }, elements);
    setType(type);
  }

  private RecordExpressionImpl(ExpressionImpl record) {
    super(record);
  }
  
  @Override
  public RecordTypeImpl getType() {
    return (RecordTypeImpl) super.getType();
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

  @Override
  public Expression select(String name) {
    return mkRecordSelect(getExpressionManager(), this, name);
  }

  @Override
  public RecordExpression update(String name, Expression val) {
    return mkUpdate(getExpressionManager(), this, name, val);
  }
}
