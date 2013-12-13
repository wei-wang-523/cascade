package edu.nyu.cascade.cvc4;

import static com.google.common.base.Preconditions.checkArgument;
import static edu.nyu.cascade.prover.Expression.Kind.DATATYPE_CONSTRUCT;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

import edu.nyu.acsys.CVC4.Datatype;
import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.cascade.cvc4.InductiveTypeImpl.ConstructorImpl;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;

public class InductiveExpressionImpl extends ExpressionImpl implements
    InductiveExpression {
  /*
   * static InductiveExpression create(ExpressionManager exprManager, final
   * IConstructor constructor) { checkArgument(constructor.getSelectors().size()
   * == 0); return new InductiveExpression(exprManager,constructor); }
   */
  static InductiveExpressionImpl create(Constructor constructor,
      Expression... args) {
    checkArgument(constructor.getSelectors().size() == args.length);
    return new InductiveExpressionImpl(ConstructorImpl.valueOf(constructor),
        ImmutableList.copyOf(Arrays.asList(args)));
  }

  static InductiveExpressionImpl create(Constructor constructor,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(constructor.getSelectors().size() == Iterables
        .size(args));
    if (Iterables.isEmpty(args)) {
      return new InductiveExpressionImpl(ConstructorImpl.valueOf(constructor));
    } else {
      return new InductiveExpressionImpl(ConstructorImpl.valueOf(constructor), args);
    }
  }

//  private final ConstructorImpl constructor;
  
  private InductiveExpressionImpl(final ConstructorImpl constructor) {
    super(constructor.getExpressionManager(), Kind.DATATYPE_CONSTRUCT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em) throws Exception {
            ExpressionManagerImpl exprManager= constructor.getExpressionManager();
            Type type = exprManager.toCvc4Type(constructor.getType());
            DatatypeType dtt = new DatatypeType(type);
            Datatype dt = dtt.getDatatype();
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.APPLY_CONSTRUCTOR, 
                dt.getConstructor(constructor.getName()));
          }
        });

//    this.constructor = constructor;

    assert (getChildren() != null);
    assert (getChildren().size() == 0);
    
    setType( constructor.getType() );
  }
  
  private InductiveExpressionImpl(ExpressionImpl e) {
    super(e);
    /*this.constructor = InductiveTypeImpl.lookupConstructor(e.getExpressionManager(),
        getCvc4Expression().getOpExpr().toString());*/
  }

  /*
   * private InductiveExpression(final IConstructor constructor, final
   * IExpression first, final IExpression... rest) {
   * super(mkStrategy(constructor), first, rest);
   * 
   * this.constructor = constructor; }
   */
  private InductiveExpressionImpl(final ConstructorImpl constructor,
      Iterable<? extends Expression> args) {
    super(constructor.getExpressionManager(), DATATYPE_CONSTRUCT,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> children)
              throws Exception {
            ExpressionManagerImpl exprManager= constructor.getExpressionManager();
            Type type = exprManager.toCvc4Type(constructor.getType());
            DatatypeType dtt = new DatatypeType(type);
            Datatype dt = dtt.getDatatype();
            vectorExpr argsExpr = new vectorExpr();
            for(Expr child : children)  argsExpr.add(child);
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.APPLY_CONSTRUCTOR, 
                dt.getConstructor(constructor.getName()), argsExpr);
          }
        }, args);

//    this.constructor = constructor;
    setType( constructor.getType() );
  }
  
  private InductiveExpressionImpl(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, InductiveType type, Iterable<? extends ExpressionImpl> children) {
    super(exprManager, kind, expr, type);
  }
  
  protected static InductiveExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, InductiveType type, Iterable<? extends ExpressionImpl> children) {
  	return new InductiveExpressionImpl(exprManager, kind, expr, type, children);
  }

/*  public ConstructorImpl getConstructor() {
    return constructor;
  }*/

  @Override
  public InductiveType getType() {
    return (InductiveType)super.getType();
  }

  
  @Override
  public Expression select(Selector selector) {
    return SelectExpressionImpl.create(getExpressionManager(),selector, this);
  }

  @Override
  public BooleanExpression test(Constructor constructor) {
    return TestExpressionImpl.create(getExpressionManager(),constructor,this);
  }

  static InductiveExpressionImpl valueOf(ExpressionManagerImpl exprManager, ExpressionImpl expr) {
    Preconditions.checkArgument(expr.isInductive());
    if (exprManager.equals(expr.getExpressionManager())) {
      if( expr instanceof InductiveExpressionImpl ) {
        return (InductiveExpressionImpl) expr;
      } else {
        return new InductiveExpressionImpl(expr);
      }
    }

    switch (expr.getKind()) {
    default:
      throw new UnsupportedOperationException();
    }
  }
}
