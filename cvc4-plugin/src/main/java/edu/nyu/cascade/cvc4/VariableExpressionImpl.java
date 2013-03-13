package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.SKOLEM;
import static edu.nyu.cascade.prover.Expression.Kind.VARIABLE;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class VariableExpressionImpl extends ExpressionImpl implements
    VariableExpression {
  static VariableExpressionImpl valueOf(
      ExpressionManagerImpl exprManager, Expression e) {
    if (e instanceof VariableExpressionImpl) {
      return (VariableExpressionImpl) e;
    } else if (e instanceof VariableExpression) {
      VariableExpression e2 = (VariableExpression) e;
      return new VariableExpressionImpl(exprManager, e2.getName(), e2.getType(),
          false);
    } else if (e instanceof ExpressionImpl && e.isVariable()) {
      ExpressionImpl ei = (ExpressionImpl) e; 
      assert( exprManager.equals(ei.getExpressionManager()) );
      /*FIXME: equivalent way to get String name = cvcExpr.getName();*/
      Expr cvcExpr = ei.getCvc4Expression();
      String name = cvcExpr.getChild(0).getConstString();
      return new VariableExpressionImpl(exprManager, name, ei.getType(), 
          false);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  static  ExpressionImpl valueOfSkolem(
      ExpressionManagerImpl exprManager, final Expr sk, Type type) {
    Preconditions.checkArgument(sk.getKind().equals(edu.nyu.acsys.CVC4.Kind.SKOLEM));
    Preconditions.checkArgument(exprManager.toType(sk.getType()).equals(type));
    
    VariableExpressionImpl result = new VariableExpressionImpl(exprManager,
        SKOLEM, sk, sk.toString(), type);
    result.setConstant(true);
    return result;
  }
  
  static  ExpressionImpl valueOfVariable(
      ExpressionManagerImpl exprManager, final Expr expr, Type type) {
    Preconditions.checkArgument(expr.getKind().equals(edu.nyu.acsys.CVC4.Kind.VARIABLE) 
        /*|| expr.isSymbol()*/);
    Preconditions.checkArgument(exprManager.toType(expr.getType()).equals( type ));

    VariableExpressionImpl result = new VariableExpressionImpl(exprManager,
        VARIABLE, expr, expr.toString(), type);
    result.setIsVariable(true);
    return result;
  }
  
  protected VariableExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      Expr expr, String name, Type type) {
    super(exprManager, kind, expr, type);
    setName(name);
  }
  
  protected VariableExpressionImpl(ExpressionManagerImpl exprManager, String name, Type type, boolean fresh) {
    super(exprManager, new VariableConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, String name, edu.nyu.acsys.CVC4.Type type) {
        /* TODO: see if var is already defined. There's a bug in lookupVar
         * bc it's second parameter is a output parameter. Need to change
         * the API so that it only takes the name.
         */
//        if( IOUtils.debugEnabled() && em.lookupVar(name) == null ) {
          
        if(type.isDatatype()) {
          DatatypeType dtt = new DatatypeType(type);
          String dtName = dtt.getDatatype().getName();
          TheoremProverImpl.tpFileCommand(name + " : " + dtName);
          TheoremProverImpl.debugCommand(name + " : " + dtName);
        } else {
          TheoremProverImpl.tpFileCommand(name + " : " + type.toString());
          TheoremProverImpl.debugCommand(name + " : " + type.toString());
        }
        return em.mkVar(name, type);
      }
    }, name, type, fresh);
  }

  /** Constructor with strategy, for subclasses that need to modify the
   * interaction with CVC4 (c.f., FunctionVariable).
   */
  protected VariableExpressionImpl(ExpressionManagerImpl exprManager,
      VariableConstructionStrategy strategy, String name,
      Type type, boolean fresh) {
    super(exprManager,strategy,name,type,fresh);
  }

  @Override
  public String getName() {
    return super.getName();
  }

}
