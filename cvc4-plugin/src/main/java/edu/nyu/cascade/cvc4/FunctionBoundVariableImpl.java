package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionVariableExpression;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public final class FunctionBoundVariableImpl
  extends BoundVariableExpressionImpl
  implements FunctionVariableExpression {

/*  static  FunctionVariableImpl create(
      ExpressionManagerImpl exprManager, String name, Type argType1, Type argType2,  Type range, boolean fresh) {
    FunctionTypeImpl type = exprManager.functionType(argType1, argType2, range);
    return new FunctionVariableImpl(exprManager, name, type,fresh);
  }
*/  
  static  FunctionBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, Iterable<? extends Type> argTypes, Type range, boolean fresh) {
    FunctionTypeImpl type = exprManager.functionType(argTypes, range);
    return new FunctionBoundVariableImpl(exprManager, name, type,fresh);
  }

  static  FunctionBoundVariableImpl create(
      ExpressionManagerImpl exprManager, 
      String name, FunctionType type, boolean fresh) {
    return new FunctionBoundVariableImpl(exprManager, name, type, fresh);
  }
  
  private FunctionBoundVariableImpl(ExpressionManagerImpl exprManager, Kind kind,
      Expr expr, String name, FunctionType type) {
    super(exprManager, kind, expr, name, type);
  }
  
  private FunctionBoundVariableImpl(ExpressionManagerImpl exprManager, String name, final FunctionType ftype,boolean fresh) {
    super(exprManager, new VariableConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, String name, edu.nyu.acsys.CVC4.Type type)
          throws Exception {
        TheoremProverImpl.debugCommand("%s: %s;", name, type.toString());
        TheoremProverImpl.tpFileCommand("%s: %s;", name, type.toString());
/*        TheoremProver.debugCall("validityChecker.createOp(\"%s\",%s)", name,
            ftype);
*/
        /*Expr op = em.createOp(name, type);*/
        Expr op = em.mkBoundVar(name, type);
        IOUtils.debug().pln(op.toString());
        return op;
      }
    }, name, ftype, fresh);
  }

  @Override
  public FunctionTypeImpl getType() {
    return (FunctionTypeImpl) super.getType();
  }

  @Override
  public ExpressionImpl apply(Expression arg1, Expression... rest) {
    Preconditions.checkArgument(getType().getArity() == rest.length + 1);
    return getType().apply(this, arg1, rest);
  }

  @Override
  public ExpressionImpl apply(Iterable<? extends Expression> args) {
    Preconditions.checkArgument(getType().getArity() == Iterables.size(args));
    return getType().apply(this, args);
  }

  @Override
  public ImmutableList<? extends Type> getArgTypes() {
    return getType().getArgTypes();
  }

  @Override
  public Type getRange() {
    return getType().getRangeType();
  }
}
