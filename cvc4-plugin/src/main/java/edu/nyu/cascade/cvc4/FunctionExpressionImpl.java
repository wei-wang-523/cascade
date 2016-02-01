package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.LAMBDA;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

final class FunctionExpressionImpl extends ExpressionImpl implements FunctionExpression {

  static FunctionExpressionImpl create(ExpressionManagerImpl exprManager, 
  		Iterable<BoundExpression> vars, Expression body) {
		return new FunctionExpressionImpl(exprManager, vars, body);
	}
  
  static FunctionExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
	    Expr expr, FunctionType type, Iterable<? extends ExpressionImpl> children) {
		return new FunctionExpressionImpl(exprManager, kind, expr, type, children);
	}

	static FunctionExpressionImpl valueOf(
      ExpressionManagerImpl exprManager, Expression f) {
    if (exprManager.equals(f.getExpressionManager())) {
      if (f instanceof FunctionExpressionImpl) {
        return (FunctionExpressionImpl) f;
      } else if (f instanceof ExpressionImpl) {
        return new FunctionExpressionImpl((ExpressionImpl) f);
      }
    }

    switch (f.getKind()) {
    default:
      throw new UnsupportedOperationException();
    }
  }
  
  private final Expr op;

  private FunctionExpressionImpl(
      ExpressionImpl f) {
    super(f);
    this.op = getCvc4Expression();
  }
  
  private FunctionExpressionImpl(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, FunctionType type, Iterable<? extends ExpressionImpl> children) {
    super(exprManager, kind, expr, type, children);
    this.op = getCvc4Expression().getOperator();
  }
  
  private FunctionExpressionImpl(ExpressionManagerImpl exprManager,
      Iterable<? extends BoundExpression> vars, Expression body) {
    super(exprManager, LAMBDA, new BinderConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, List<Expr> vars, Expr body) {
        vectorExpr varList = new vectorExpr();
        for(Expr var : vars)    varList.add(var);
        Expr boundVarList = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
        Expr op = em.mkExpr(edu.nyu.acsys.CVC4.Kind.LAMBDA, boundVarList, body);       
        return op;
      }
    }, vars, body);
    this.op = getCvc4Expression().getOperator();
    
    List<Type> argTypes = Lists.newArrayListWithCapacity(Iterables.size(vars));
    for( Expression t : vars ) {
      argTypes.add( t.getType() );
    }
    setType( FunctionTypeImpl.create(exprManager, argTypes, body.getType()) );
  }
  
  @Override
  public Expression apply(Expression arg1, Expression... otherArgs) {
    Preconditions.checkArgument(getType().getArgTypes().size() == otherArgs.length + 1);
    return apply(Lists.asList(arg1, otherArgs));
  }

  @Override
  public Expression apply(Iterable<? extends Expression> args) {
    Preconditions.checkArgument(Iterables.size(args) == getType().getArgTypes().size());
    return ExpressionImpl.mkFunApply(getExpressionManager(), this, args);
  }

  @Override
  public ImmutableList<? extends Type> getArgTypes() {
    return getType().getArgTypes();
  }

  public Expr getCvc4Op() {
    return op;
  }
  
  @Override
  public String getName() {
  	return op.toString();
  }

  @Override
  public Type getRange() {
    return getType().getRangeType();
  }

  @Override
  public FunctionType getType() {
    return super.getType().asFunction();
  }
}
