package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.SubrangeBound;
import edu.nyu.acsys.CVC4.SubrangeBounds;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RangeType;

public final class IntegerRangeTypeImpl extends IntegerTypeImpl implements
    RangeType, IntegerType {
  static IntegerRangeTypeImpl create(ExpressionManagerImpl exprManager,
      Expression lowerBound, Expression upperBound) {
    Preconditions.checkArgument(lowerBound.isInteger());
    Preconditions.checkArgument(upperBound.isInteger());
    return new IntegerRangeTypeImpl(exprManager, lowerBound, upperBound);
  }

  static IntegerRangeTypeImpl withLowerBound(ExpressionManagerImpl exprManager,
      Expression lowerBound) {
    Preconditions.checkArgument(lowerBound.isInteger());
    return new IntegerRangeTypeImpl(exprManager, lowerBound, true);
  }

  static IntegerRangeTypeImpl withUpperBound(ExpressionManagerImpl exprManager,
      Expression upperBound) {
    Preconditions.checkArgument(upperBound.isInteger());
    return new IntegerRangeTypeImpl(exprManager, upperBound, false);
  }

  /** Lower bound of the range, null if unbounded */
  private final IntegerExpressionImpl lowerBound;

  /** Upper bound of the range, null if unbounded */
  private final IntegerExpressionImpl upperBound;

  /**
   * Construct a new integer range type given the bounds. A null lower bound
   * means unbounded from below, a null upper bound means unbounded from above.
   * 
   * @param lowerBound
   *          the lower bound
   * @param upperBound
   *          the upper bound @ * @throws Exception
   */
  /*
   * IntegerRangeType(IntegerExpression lowerBound, IntegerExpression
   * upperBound) { super(lowerBound, upperBound); this.lowerBound =
   * (IntegerExpression) lowerBound; this.upperBound = (IntegerExpression)
   * upperBound; }
   */

  IntegerRangeTypeImpl(ExpressionManagerImpl exprManager,
      Expression bound, final boolean isLowerBounded) {
    super(exprManager, new UnaryConstructionStrategy() {
      @Override
      public Type apply(ExprManager em, Expr bound) {
        // Create the type predicate
        try {
          boolean noBound = bound.getType().isString() 
              && ((isLowerBounded && bound.getConstString().equals("_NEGINF"))
                  || (!isLowerBounded && bound.getConstString().equals("_POSINF")));
          Preconditions.checkArgument(noBound 
              || (bound.getKind().equals(edu.nyu.acsys.CVC4.Kind.CONST_RATIONAL)
                  && bound.getConstRational().isIntegral()));
          SubrangeBound b = noBound ? new SubrangeBound() : 
            new SubrangeBound(bound.getConstRational().getNumerator());  
          SubrangeBounds bs = isLowerBounded ?
              new SubrangeBounds(b, new SubrangeBound()) :
                new SubrangeBounds(new SubrangeBound(), b);
          return em.mkSubrangeType(bs);
        } catch (Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, bound);
    if (isLowerBounded) {
      this.lowerBound = exprManager.asIntegerExpression(bound);
      this.upperBound = null;
    } else {
      this.lowerBound = null;
      this.upperBound = exprManager.asIntegerExpression(bound);
    }
  }

  IntegerRangeTypeImpl(ExpressionManagerImpl exprManager,
      Expression lowerBound, Expression upperBound) {
    super(exprManager, new BinaryConstructionStrategy() {
      @Override
      public Type apply(ExprManager em, Expr lowerBound, Expr upperBound) {
        // Create the type predicate
        try {
          boolean noLowerBound = lowerBound.getType().isString() 
              && lowerBound.getConstString().equals("_NEGINF");
          boolean noUpperBound = upperBound.getType().isString()
              && upperBound.getConstString().equals("_POSINF");
          Preconditions.checkArgument(noLowerBound 
              && lowerBound.getKind().equals(edu.nyu.acsys.CVC4.Kind.CONST_RATIONAL)
              && lowerBound.getConstRational().isIntegral());
          Preconditions.checkArgument(noUpperBound 
              && upperBound.getKind().equals(edu.nyu.acsys.CVC4.Kind.CONST_RATIONAL)
              && upperBound.getConstRational().isIntegral());
          SubrangeBound bl = noLowerBound ? new SubrangeBound() : 
            new SubrangeBound(lowerBound.getConstRational().getNumerator());
          SubrangeBound bu = noUpperBound ? new SubrangeBound() : 
            new SubrangeBound(upperBound.getConstRational().getNumerator());
          return em.mkSubrangeType(new SubrangeBounds(bl, bu));
        } catch (Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, lowerBound, upperBound);
    
    this.lowerBound = exprManager.asIntegerExpression(lowerBound);
    this.upperBound = exprManager.asIntegerExpression(upperBound);
  }

  @Override
  public IntegerExpressionImpl getLowerBound() {
    return lowerBound;
  }

  @Override
  public IntegerExpressionImpl getUpperBound() {
    return upperBound;
  }

  @Override
  public edu.nyu.cascade.prover.type.Type getBaseType() {
    return lowerBound != null ? lowerBound.getType() : upperBound.getType();
  }

}
