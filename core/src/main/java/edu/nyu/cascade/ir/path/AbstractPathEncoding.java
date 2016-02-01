package edu.nyu.cascade.ir.path;

import java.io.PrintStream;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.memory.model.MemoryModel;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.prover.BooleanExpression;
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

  protected abstract BooleanExpression assertionToBoolean(StateExpression path,
      StateExpressionClosure bool);
  
	@Override
  public StateExpression declare(StateExpression prefix, IRExpression s) {
	  ExpressionEncoder encoder = getExpressionEncoder();
	  return declare(prefix, s.toLval(encoder));
  }
	
	@Override
	public StateExpression declareEnum(StateExpression prefix, IRExpression ... operands) {
		ExpressionEncoder encoder = getExpressionEncoder();
    StateExpressionClosure[] operandClosures = new StateExpressionClosure[operands.length];
    for(int i = 0; i < operandClosures.length; i++) {
    	operandClosures[i] = operands[i].toExpression(encoder);
    }
		return declareEnum(prefix, operandClosures);
	}

  @Override
  public StateExpression assign(StateExpression pre, IRExpression lhs, IRExpression rhs) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return assign(pre, lhs.toLval(encoder), rhs.toExpression(encoder));
  }

  @Override
  public StateExpression assume(StateExpression pre, IRExpression b) {
    return assume(pre, b.toBoolean(getExpressionEncoder()));
  }
  
  @Override
  public StateExpression alloc(StateExpression pre, IRExpression ptr, IRExpression size) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return alloc(pre, ptr.toLval(encoder), size.toExpression(encoder));
  }
  
  @Override
  public StateExpression free(StateExpression pre, IRExpression ptr) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return free(pre, ptr.toExpression(encoder));
  }

  @Override
  public StateExpression havoc(StateExpression pre, IRExpression lhs) {
    ExpressionEncoder encoder = getExpressionEncoder();
    return havoc(pre, lhs.toLval(encoder));
  }
  
  @Override
  public StateExpression call(StateExpression pre, String func, IRExpression ... operands) {
    ExpressionEncoder encoder = getExpressionEncoder();
    StateExpressionClosure[] operandClosures = new StateExpressionClosure[operands.length];
    for(int i = 0; i < operandClosures.length; i++) {
    	operandClosures[i] = operands[i].toExpression(encoder);
    }
    return call(pre, func, operandClosures);
  }
  
  @Override
  public ValidityResult<?> checkAssertion(StateExpression path, StateExpressionClosure bool)
      throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    ExpressionManager exprManager = exprEncoding.getExpressionManager();

    try {
      if (bool == null) {
        return ValidityResult.valid(exprManager.tt());
      }
      TheoremProver tp = exprManager.getTheoremProver();
      BooleanExpression assertion = assertionToBoolean(path, bool);
      ImmutableSet<? extends BooleanExpression> assumptions = exprEncoding
          .getAssumptions();
      tp.assume(assumptions);
      ValidityResult<?> res = tp.checkValidity(assertion);
      exprEncoding.clearAssumptions();
      tp.clearAssumptions();
      return res;
    } catch (TheoremProverException e) {
      throw new PathFactoryException(e);
    } catch (ExpressionFactoryException e) {
      throw new PathFactoryException(e);
    }
  }

  @Override
  public SatResult<?> checkPath(StateExpression path) throws PathFactoryException {
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    TheoremProver tp = exprEncoding.getExpressionManager().getTheoremProver();
    try {
      BooleanExpression assertion = pathToBoolean(path);
      ImmutableSet<? extends BooleanExpression> assumptions = exprEncoding
          .getAssumptions();
      tp.assume(assumptions);
      SatResult<?> res = tp.checkSat(assertion);
      exprEncoding.clearAssumptions();
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
  public MemoryModel<?> getMemoryModel() {
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
    return getExpressionEncoder().getEncoding().getExpressionManager();
  }

  @Override
  public StateExpression noop(StateExpression pre) {
    return pre;
  }

  @Override
  public void printCounterExample(PrintStream out, Iterable<?> counterExample) {
    out.println("Assertions that invalidate the query:");
    for (Object o : counterExample) {
      out.println("ASSERT " + o + ";");
    }
  }
  
	protected abstract BooleanExpression pathToBoolean(StateExpression path);
}
