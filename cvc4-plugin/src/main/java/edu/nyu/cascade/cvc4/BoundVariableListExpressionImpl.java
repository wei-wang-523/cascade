package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.Expression;

public class BoundVariableListExpressionImpl extends ExpressionImpl {
  
  static BoundVariableListExpressionImpl create(ExpressionManagerImpl exprManager,
      Expression first, Expression... rest) {
    return new BoundVariableListExpressionImpl(exprManager, Lists.asList(first, rest));
  }

  static BoundVariableListExpressionImpl create(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> elements) {
    Preconditions.checkArgument(!Iterables.isEmpty(elements));
    return new BoundVariableListExpressionImpl(exprManager, elements);
  }

  private BoundVariableListExpressionImpl(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> elements) {
    super(exprManager, Kind.VARIABLE_LIST, new NaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, List<Expr> args)
          throws Exception {
        vectorExpr argsExpr = new vectorExpr();
        for(Expr arg : args) {
          Preconditions.checkArgument(arg.getKind() 
              == edu.nyu.acsys.CVC4.Kind.BOUND_VARIABLE);
          argsExpr.add(arg);
        }
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, argsExpr);
      }
    }, elements);
    setType(BoundVarTypeImpl.create(exprManager));
  }

  private BoundVariableListExpressionImpl(ExpressionImpl boundVarList) {
    super(boundVarList);
  }

  static BoundVariableListExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      ExpressionImpl expr) {
    if( expr instanceof BoundVariableListExpressionImpl ) {
      return (BoundVariableListExpressionImpl) expr;
    } else {
      return new BoundVariableListExpressionImpl((ExpressionImpl) expr);
    }
  }

  public Expression index(int i) {
    return this.getChild(i);
  }

  public int size() {
    return this.getArity();
  }
}
