package edu.nyu.cascade.ir.expr;

import java.io.PrintStream;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.ValidityResult;

public abstract class AbstractPathEncoding implements
    PathEncoding {
  private final ExpressionEncoder encoder;

  protected AbstractPathEncoding(ExpressionEncoder encoder) {
    this.encoder = encoder;
  }

  protected abstract BooleanExpression assertionToBoolean(Expression path,
      ExpressionClosure bool);

  @Override
  public Expression assign(Expression pre, IRExpression lhs, IRExpression rhs) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return assign(pre, lhs.toLval(encoder), rhs.toExpression(encoder));
  }

  @Override
  public Expression assume(Expression pre, IRExpression b) {
    return assume(pre, b.toBoolean(getExpressionEncoder()));
  }
  
  @Override
  public Expression alloc(Expression pre, IRExpression ptr, IRExpression size) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return alloc(pre, ptr.toLval(encoder), size.toExpression(encoder));
  }
  
  @Override
  public Expression declareArray(Expression pre, IRExpression ptr, IRExpression size) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return declareArray(pre, ptr.toLval(encoder), size.toExpression(encoder));
  }
  
  @Override
  public Expression declareStruct(Expression pre, IRExpression ptr, IRExpression size) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return declareStruct(pre, ptr.toLval(encoder), size.toExpression(encoder));
  }
  
  @Override
  public Expression free(Expression pre, IRExpression ptr) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return free(pre, ptr.toExpression(encoder));
  }
  
  @Override
  public Expression fieldAssign(Expression pre, IRExpression lhs, String field, IRExpression rhs) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return fieldAssign(pre, lhs.toExpression(encoder), field, rhs.toExpression(encoder));
  }

  @Override
  public Expression havoc(Expression pre, IRExpression lhs) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return havoc(pre, lhs.toLval(encoder));
  }
  
  @Override
  public ValidityResult<?> checkAssertion(Expression path, ExpressionClosure bool)
      throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    ExpressionManager exprManager = exprEncoding.getExpressionManager();

    try {
      if (bool == null) {
        return ValidityResult.valid(exprManager.tt());
      }
      TheoremProver tp = exprManager.getTheoremProver();
      ImmutableSet<? extends BooleanExpression> assumptions = exprEncoding
          .getAssumptions();
      BooleanExpression assertion = assertionToBoolean(path, bool);
      tp.assume(assumptions);
      ValidityResult<?> res = tp.checkValidity(assertion);
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    } catch (ExpressionFactoryException e) {
      throw new PathFactoryException(e);
    }
  }

  @Override
  public SatResult<?> checkPath(Expression path) throws PathFactoryException {
    ExpressionEncoding exprFactory = getExpressionEncoding();
    TheoremProver tp = exprFactory.getExpressionManager().getTheoremProver();
    try {
      ImmutableSet<? extends BooleanExpression> assumptions = exprFactory
          .getAssumptions();
      tp.assume(assumptions);
      SatResult<?> res = tp.checkSat(pathToBoolean(path));
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    } catch (ExpressionFactoryException e) {
      throw new PathFactoryException(e);
    }
  }

  /**
   * {@inheritDoc}
   * 
   * Default implementation: returns the expression factory associated with the
   * expression interpreter.
   */
  @Override
  public ExpressionEncoding getExpressionEncoding() {
    return getExpressionEncoder().getEncoding();
  }

  @Override
  public ExpressionEncoder getExpressionEncoder() {
    return encoder;
  }

  @Override
  public MemoryModel getMemoryModel() {
    return getExpressionEncoder().getMemoryModel();
  }

  /**
   * {@inheritDoc}
   * 
   * Default implementation: returns the expression manager associated with the
   * expression interpreter.
   */
  @Override
  public ExpressionManager getExpressionManager() {
    return getExpressionEncoder().getExpressionManager();
  }

  @Override
  public Expression noop(Expression pre) {
    return pre;
  }

  protected abstract BooleanExpression pathToBoolean(Expression path);

  @Override
  public void printCounterExample(PrintStream out, Iterable<?> counterExample) {
    // ITheoremProver tp =
    // getExpressionFactory().getExpressionManager().getTheoremProver();
    // Set<?> counterExample = tp.getCounterExample();
    out.println("Assertions that invalidate the query:");
    for (Object o : counterExample) {
      out.println("ASSERT " + o + ";");
    }
  }
}
