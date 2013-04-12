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
import edu.nyu.cascade.prover.type.RangeType;
import edu.nyu.cascade.prover.type.RationalType;

public class RationalRangeTypeImpl extends RationalTypeImpl implements
    RangeType, RationalType {
  /** Lower bound of the range, null if unbounded */
  protected RationalExpressionImpl lowerBound = null;

  /** Upper bound of the range, null if unbounded */
  protected RationalExpressionImpl upperBound = null;

  /**
   * Construct a new rational range type given the bounds. A null lower bound
   * means unbounded from below, a null upper bound means unbounded from above.
   * 
   * @param expressionManager
   *          the reponsible expression manager
   * @param lowerBound
   *          the lower bound
   * @param upperBound
   *          the upper bound
   * @throws Exception
   */

  RationalRangeTypeImpl(ExpressionManagerImpl em,
      Expression lowerBound,
      Expression upperBound) {
    super(em, new BinaryConstructionStrategy() {

      @Override
      public Type apply(ExprManager em, Expr lowerBound, Expr upperBound) {
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
    this.lowerBound = em.asRationalExpression(lowerBound);
    this.upperBound = em.asRationalExpression(upperBound);
  }

  @Override
  public RationalExpressionImpl getLowerBound() {
    return lowerBound;
  }

  @Override
  public RationalExpressionImpl getUpperBound() {
    return upperBound;
  }

  @Override
  public edu.nyu.cascade.prover.type.Type getBaseType() {
    return lowerBound!=null ? lowerBound.getType() : upperBound.getType();
  }
}
