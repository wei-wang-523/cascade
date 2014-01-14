package edu.nyu.cascade.cvc4;

import static com.google.common.base.Preconditions.checkArgument;
import static edu.nyu.cascade.prover.Expression.Kind.DATATYPE_TEST;
import edu.nyu.acsys.CVC4.Datatype;
import edu.nyu.acsys.CVC4.DatatypeConstructor;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Constructor;

/* FIXME: The constructor should be a child of this expression! */

public class TestExpressionImpl extends BooleanExpressionImpl {
  static TestExpressionImpl create(ExpressionManagerImpl exprManager,
      Constructor constructor, Expression val) {
    checkArgument(val.isInductive());
    checkArgument(val.asInductive().getType().getConstructors().contains(constructor));
    return new TestExpressionImpl(exprManager, constructor, val);
  }

  private final Constructor constructor;

  private TestExpressionImpl(final ExpressionManagerImpl exprManager,
      final Constructor constructor, Expression val) {
    super(exprManager, DATATYPE_TEST, new UnaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr arg) throws Exception {  
        Type type = exprManager.toCvc4Type(constructor.getType());
        DatatypeType dtt = new DatatypeType(type);
        Datatype dt = dtt.getDatatype();
        long constructorIndex = Datatype.indexOf(dt.getConstructor(constructor.getName()));
        DatatypeConstructor dtc = dt.get(constructorIndex);
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.APPLY_TESTER,
            dtc.getTester(), arg);
        /*return em.datatypeTestExpr(constructor.getName(), arg);*/
      }
    }, val);

    this.constructor = constructor;
  }

  public Constructor getConstructor() {
    return constructor;
  }
}
