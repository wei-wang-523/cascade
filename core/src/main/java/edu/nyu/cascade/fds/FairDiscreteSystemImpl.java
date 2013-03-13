/**
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>
 */

package edu.nyu.cascade.fds;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

/**
 * A Prior/SPL fair discrete system.
 * 
 * @author <a href="mailto:mdeters@cs.nyu.edu">Morgan Deters</a>
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 */
public class FairDiscreteSystemImpl implements FairDiscreteSystem {
  public static class Builder {
    private final TemporalExpressionEncoding encoding;

    /** Set of compassion requirements */
    private final ImmutableSet.Builder<Pair<StateProperty, StateProperty>> compassion;
    /** Initial condition specification */
    private final ImmutableSet.Builder<StateProperty> initialConditions;
    /** Set of justice requirements */
    private final ImmutableSet.Builder<StateProperty> justice;
    /** Side condition specification */
    private final ImmutableSet.Builder<StateProperty> sideConditions;
    /** Set of transitions */
    private final ImmutableSet.Builder<StateProperty> transitions;
    /** Set of variables */
    private final ImmutableSet.Builder<StateVariable> variables;
    /** Set of internal variables, which aren't relevant to the user */
    private final ImmutableSet.Builder<StateVariable> internalVariables;
    
    public Builder(TemporalExpressionEncoding exprFactory) {
      this.encoding = exprFactory;
      this.compassion = ImmutableSet.builder();
      this.justice = ImmutableSet.builder();
      this.initialConditions = ImmutableSet.builder();
      this.sideConditions = ImmutableSet.builder();
      this.transitions = ImmutableSet.builder();
      this.variables = ImmutableSet.builder();
      this.internalVariables = ImmutableSet.builder();
    }
    
    /**
     * Add a compassion requirement to this FDS.
     */
    public void addCompassionRequirement(StateProperty isp1,
        StateProperty isp2) {
      Preconditions.checkNotNull(isp1);
      Preconditions.checkNotNull(isp2);
      Pair<StateProperty, StateProperty> req = Pair.of(isp1, isp2);
      compassion.add(req);
    }

    /**
     * Set an initial condition in this FDS. Add here the initial state of user
     * and control variables.
     */
    public void addInitialCondition(StateProperty isp) {
      Preconditions.checkNotNull(isp);
      initialConditions.add(isp);
    }

    /**
     * Add a justice requirement to this FDS.
     */
    public void addJusticeRequirement(StateProperty isp) {
      Preconditions.checkNotNull(isp);
      justice.add(isp);
    }

    /**
     * Set a side condition in this FDS. Permitting a null argument makes call
     * sites more declarative in edge cases where there's nothing to add.
     */
    public void addSideCondition(StateProperty isp) {
      if (isp != null) {
        sideConditions.add(isp);
      }
    }

    /**
     * Add a transition to this FDS.
     */
    public void addTransition(StateProperty isp) {
      transitions.add(isp);
    }


    public void addInternalVariable(StateVariable isv) {
      addVariable(isv);
      internalVariables.add(isv);
    }

    /**
     * Add a variable to this FDS.
     */
    public void addVariable(StateVariable isv) {
      variables.add(isv);
    }
    
    public void addVariables(Iterable<? extends StateVariable> xs) {
      variables.addAll(xs);
    }
    
    public FairDiscreteSystemImpl build() {
      FairDiscreteSystemImpl fds = new FairDiscreteSystemImpl();
      fds.setVariables(variables.build());
      fds.setInternalVariables(internalVariables.build());
      fds.setInitialConditions(
          encoding.and(initialConditions.build()));
      fds.setTransitions(transitions.build());
      fds.setCompassionRequirements(compassion.build());
      fds.setJusticeRequirements(justice.build());
      fds.setSideConditions(
          encoding.and(sideConditions.build()).asStateProperty());
      return fds;
    }
  }
  
  
  /** Set of compassion requirements */
  private ImmutableSet<Pair<StateProperty, StateProperty>> compassion;
  /** Initial state specification */
  private StateProperty initialConditions;
  /** Set of justice requirements */
  private ImmutableSet<StateProperty> justice;
  /** Side condition specification */
  private StateProperty sideConditions;
  /** Set of transitions */
  private ImmutableSet<StateProperty> transitions;
  /** Set of variables */
  private ImmutableSet<StateVariable> variables;
  private ImmutableSet<StateVariable> internalVariables;
  
/*  public FairDiscreteSystem(Set<IStateVariable> vars, IStateProperty initConds,
      Set<IStateProperty> transitions,
      Set<Pair<IStateProperty, IStateProperty>> compassion,
      Set<IStateProperty> justice, IStateProperty sideConds) {
    this.compassion = ImmutableSet.copyOf(compassion);
    this.initialConditions = initConds;
    this.justice = ImmutableSet.copyOf(justice);
    this.sideConditions = sideConds;
    this.transitions = ImmutableSet.copyOf(transitions);
    this.variables = ImmutableSet.copyOf(vars);
  }*/

  @SuppressWarnings("unchecked")
  @Override
  public SatResult<?> checkSat(StateProperty p) {
    BooleanExpression bool = sideConditions().implies(p).toBooleanExpression();
    IOUtils.debug().pln("FDS.checkSat: " + bool);
    TheoremProver tp = bool.getExpressionManager().getTheoremProver();
    SatResult<?> res = tp.checkSat(bool);
    if( res.isUnsatisfiable() ) {
      return res;
    } else {
      return SatResult.valueOf(res.getType(), res.getFormula(), res
          .getAssumptions(), (List) stripInternalVars(res.getSatisfyingAssertions()));
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public ValidityResult<?> checkValidity(StateProperty p) {
    IOUtils.debug().pln("FDS.checkValidity: " + p);
    TheoremProver tp = p.getExpressionManager().getTheoremProver();
    tp.assume(sideConditions().toBooleanExpression());
    ValidityResult<?> res = tp.checkValidity(p.toBooleanExpression());
    tp.clearAssumptions();
    if (res.isValid()) {
      return res;
    } else {
      return ValidityResult.valueOf(res.getType(), res.getFormula(), res
          .getAssumptions(), (List) stripInternalVars(res.getCounterExample()));
    }
  }

  /**
   * A set of (p,q) pairs, where p and q are state properties. Each (p,q)
   * represents the constraint that any valid trace of the system with
   * infinitely many p-states will also have infinitely many q states.
   */
  @SuppressWarnings("unchecked")
  @Override
  public Pair<? extends StateProperty, ? extends StateProperty>[] compassionRequirements() {
    Pair<? extends StateProperty, ? extends StateProperty>[] result = new Pair[compassion
        .size()];
    return compassion.toArray(result);
  }
  
  public ImmutableSet<Pair<StateProperty, StateProperty>> compassionSet() {
    return compassion;
  }

  /**
   * Returns a property characterizing the initial state of the system.
   */
  @Override
  public StateProperty initialStates() {
    return initialConditions;
  }

  public ImmutableSet<StateVariable> internalVariables() {
    return internalVariables;
  }
  
  /**
   * A set of state properties. Each property J represents the constraint that
   * any valid trace of the system must have infinitely many J-states.
   */
  @Override
  public StateProperty[] justiceRequirements() {
    StateProperty[] result = new StateProperty[justice.size()];
    return justice.toArray(result);
  }

  protected ImmutableSet<StateProperty> justiceSet() {
    return justice;
  }
  
  protected void setCompassionRequirements(
      Iterable<? extends Pair<StateProperty, StateProperty>> compassion) {
    this.compassion = ImmutableSet.copyOf(compassion);
  }

  protected void setInitialConditions(StateProperty initialConditions) {
    this.initialConditions = initialConditions;
  }

  protected void setJusticeRequirements(Iterable<StateProperty> justice) {
    this.justice = ImmutableSet.copyOf(justice);
  }

  protected void setSideConditions(StateProperty sideConditions) {
    this.sideConditions = sideConditions;
  }

  protected void setTransitions(Iterable<? extends StateProperty> transitions) {
    this.transitions = ImmutableSet.copyOf(transitions);
  }

  protected void setInternalVariables(Iterable<? extends StateVariable> variables) {
    this.internalVariables = ImmutableSet.copyOf(variables);
  }
  
  protected void setVariables(Iterable<? extends StateVariable> variables) {
    this.variables = ImmutableSet.copyOf(variables);
  }

  /**
   * Returns a property characterizing the initial states of the system.
   */
  protected StateProperty sideConditions() {
    return sideConditions;
  }

  @Override
  public String toString() {
    StringBuffer sb = new StringBuffer();
    sb.append("========= FAIR DISCRETE SYSTEM ========\n");
    sb.append("Variables -----------------------------\n");
    sb.append(variables()).append("\n");
    sb.append("Side conditions -----------------------\n");
    sb.append(sideConditions()).append("\n");
    sb.append("Initial states ------------------------\n");
    sb.append(initialStates()).append("\n");
    sb.append("Transitions ---------------------------\n");
    for (StateProperty t : transitions())
      sb.append(t).append("\n");
    sb.append("Justice requirements ------------------\n");
    for (StateProperty req : justiceRequirements())
      sb.append(req).append("\n");
    sb.append("Compassion requirements ---------------\n");
    for (Pair<? extends StateProperty, ? extends StateProperty> req : compassionRequirements())
      sb.append(req).append("\n");
    sb.append("=======================================\n");
    return sb.toString();
  }

  @Override
  public StateProperty transitionRelation() {
    return StateProperties.or(transitions);
  }

  @Override
  public ImmutableSet<StateProperty> transitions() {
    return transitions;
  }

  /**
   * Returns the set of state variables in the system.
   */
  @Override
  public ImmutableSet<StateVariable> variables() {
    return variables;
  }

  @Override
  public List<Expression> stripInternalVars(
      List<? extends Expression> children) {
    IOUtils.debug().pln("Stripping internal vars: " + internalVariables());
    return relevantize(children);
  }
  
  public List<Expression> relevantize(
      List<? extends Expression> children) {
    List<Expression> relevantChildren = Lists
        .newArrayListWithCapacity(children.size());
    for (Expression child : children) {
      Expression relevantChild = relevantize(child);
      if (relevantChild != null) {
        relevantChildren.add(relevantChild);
      }
    }
    return relevantChildren;
  }

  @SuppressWarnings("unchecked")
  private
  Expression relevantize(Expression ibe) {
    List<? extends Expression> children = ibe.getChildren();
    List<Expression> relevantChildren = relevantize((List<Expression>) children);

    switch (ibe.getKind()) {
    case AND:
      if (relevantChildren.isEmpty()) {
        return null;
      } else {
        return (Expression) ibe.getExpressionManager().and(
            (List) relevantChildren);
      }

    case CONSTANT:
      return ibe;

    case EQUAL:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) child1.eq((Expression) child2);
      }

    case GEQ:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().greaterThanOrEqual(
            (Expression) child1, (Expression) child2);
      }

    case GT:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().greaterThan(
            (Expression) child1, (Expression) child2);
      }
      
    case LEQ:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().lessThanOrEqual(
            (Expression) child1, (Expression) child2);
      }

    case LT:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().lessThan(
            (Expression) child1, (Expression) child2);
      }

    case MULT:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() == 2);
        Expression child1 = relevantChildren.get(0);
        Expression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().mult(
            (Expression) child1, (Expression) child2);
      }

    case NOT:
      if( relevantChildren.isEmpty() ) {
        return null;
      } else {
        assert (relevantChildren.size() == 1);
        return (Expression) ibe.getExpressionManager().not(
            (Expression) relevantChildren.get(0));
      }
      
    case PLUS:
      if (relevantChildren.size() < 2) {
        return null;
      } else {
        assert (relevantChildren.size() >= 2);
//        IExpression child1 = relevantChildren.get(0);
//        IExpression child2 = relevantChildren.get(1);
        return (Expression) ibe.getExpressionManager().plus(
            (Iterable) relevantChildren);
//            (IExpression) child1, (IExpression) child2);
      }

    case SKOLEM:
      IOUtils.debug().pln("Ignoring skolem var: " + ibe);
      return null;
      
    case VARIABLE:
      // FIXME: Unsafe cast
      if (internalVariables.contains(StateVariableImpl
          .lookup((VariableExpression) ibe))) {
        IOUtils.debug().pln("Ignoring internal var: " + ibe);
        return null;
      } else {
        IOUtils.debug().pln("Relevant var: " + ibe);
        return ibe;
      }

    default:
      throw new UnsupportedOperationException("Unhandled expr in relevantize: "
          + ibe);
    }
  }
}
