package edu.nyu.cascade.cvc4;

import static com.google.common.base.Preconditions.checkArgument;
import static edu.nyu.cascade.prover.Expression.Kind.DATATYPE_SELECT;
import edu.nyu.acsys.CVC4.Datatype;
import edu.nyu.acsys.CVC4.DatatypeConstructor;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Selector;

/* FIXME: The selector should be a child of this expression! */

public class SelectExpressionImpl extends ExpressionImpl {
  static SelectExpressionImpl create(
      ExpressionManagerImpl exprManager, Selector selector,
      Expression val) {
    checkArgument(val.isInductive());
    checkArgument(val.asInductive().getType().getConstructors().contains(
        selector.getConstructor()));
    return new SelectExpressionImpl(exprManager, selector, val);
  }

  private SelectExpressionImpl(final ExpressionManagerImpl exprManager,
      final Selector selector, Expression val) {
    super(exprManager, DATATYPE_SELECT, new UnaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr arg) throws Exception {
        Type type = exprManager.toCvc4Type(selector.getConstructor().getType());
        DatatypeType dtt = new DatatypeType(type);
        Datatype dt = dtt.getDatatype();
        long constructorIndex = Datatype.indexOf(dt.getConstructor(selector.getConstructor().getName()));
        DatatypeConstructor dtc = dt.getConstructor(constructorIndex);
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.APPLY_SELECTOR, 
            dtc.getSelector(selector.getName()), arg);
    	/* return em.datatypeSelExpr(selector.getName(), arg); */
      }
    }, val);
    setType( selector.getType() );
  }
}
