package edu.nyu.cascade.z3;

import static com.google.common.base.Preconditions.checkArgument;
import static edu.nyu.cascade.prover.Expression.Kind.DATATYPE_CONSTRUCT;

import java.util.Arrays;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.z3.InductiveTypeImpl.ConstructorImpl;

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
  
  private InductiveExpressionImpl(final ConstructorImpl constructor) {
    super(constructor.getExpressionManager(), Kind.DATATYPE_CONSTRUCT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) {
            try {
              return ctx.MkConst(constructor.getZ3Constructor().ConstructorDecl());
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
        });

    assert (getChildren() != null);
    assert (getChildren().size() == 0);
    
    setType( constructor.getType() );
  }
  
  private InductiveExpressionImpl(ExpressionImpl e) {
    super(e);
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
          public Expr apply(Context ctx, Expr[] children) {
            try {
              return ctx.MkApp(constructor.getZ3Constructor().ConstructorDecl(), children);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
        }, args);
//  this.constructor = constructor;
    setType( constructor.getType() );
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
    return selector.apply(this);
  }

  @Override
  public BooleanExpression test(Constructor constructor) {
    return getType().test(constructor, this);
  }

  static InductiveExpressionImpl valueOf(ExpressionImpl expr) {
    Preconditions.checkArgument(expr.isInductive());
    if( expr instanceof InductiveExpressionImpl ) {
      return (InductiveExpressionImpl) expr;
    } else {
      return new InductiveExpressionImpl(expr);
    }
  }
}
