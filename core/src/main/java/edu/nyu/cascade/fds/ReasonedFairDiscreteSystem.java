package edu.nyu.cascade.fds;

import java.util.Iterator;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.util.Pair;

/**
 * A Prior/SPL fair discrete system. This version includes "reason annotations",
 * used only in toString(), as a way of debugging the FDSBuilder.
 * 
 * @author <a href="mailto:mdeters@cs.nyu.edu">Morgan Deters</a>
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
*/
public class ReasonedFairDiscreteSystem extends FairDiscreteSystemImpl {
  public static class Builder extends FairDiscreteSystemImpl.Builder {
    /** Compassion requirements' reasons */
    private final ImmutableMultimap.Builder<Pair<? extends StateProperty, ? extends StateProperty>, Object> compassionReasons;
    /** Initial states' reasons */
    private final ImmutableMultimap.Builder<StateProperty, Object> initialConditionReasons;
    /** Justice requirements' reasons */
    private final ImmutableMultimap.Builder<StateProperty, Object> justiceReasons;
    /** Side conditions' reasons */
    private final ImmutableMultimap.Builder<StateProperty, Object> sideConditionReasons;
    /** Transitions' reasons */
    private final ImmutableMultimap.Builder<StateProperty, Object> transitionReasons;
    
    public Builder(TemporalExpressionEncoding encoding) {
      super(encoding);
      this.compassionReasons = ImmutableMultimap.builder();
      this.justiceReasons = ImmutableMultimap.builder();
      this.initialConditionReasons = ImmutableMultimap.builder();
      this.sideConditionReasons = ImmutableMultimap.builder();
      this.transitionReasons = ImmutableMultimap.builder();
    }
    
    /**
     * Add a compassion requirement to this FDS.
     */
    public void addCompassionRequirement(StateProperty isp1,
        StateProperty isp2, Object reason) {
      Preconditions.checkNotNull(isp1);
      Preconditions.checkNotNull(isp2);
      super.addCompassionRequirement(isp1, isp2);
      Pair<StateProperty, StateProperty> req = Pair.of(isp1, isp2);
      compassionReasons.put(req, reason);
    }

    /**
     * Set an initial condition in this FDS. Add here the initial state of user
     * and control variables.
     */
    public void addInitialCondition(StateProperty isp, Object reason) {
      Preconditions.checkNotNull(isp);
      super.addInitialCondition(isp);
      initialConditionReasons.put(isp, reason);
    }

    /**
     * Add a justice requirement to this FDS.
     */
    public void addJusticeRequirement(StateProperty isp, Object reason) {
      Preconditions.checkNotNull(isp);
      justiceReasons.put(isp, reason);
      super.addJusticeRequirement(isp);
    }

    /**
     * Set a side condition in this FDS. Permitting a null argument makes call
     * sites more declarative in edge cases where there's nothing to add.
     */
    public void addSideCondition(StateProperty isp, Object reason) {
      if (isp != null) {
        sideConditionReasons.put(isp, reason);
        super.addSideCondition(isp);
      }
    }

    /**
     * Add a transition to this FDS.
     */
    public void addTransition(StateProperty isp, Object reason) {
      transitionReasons.put(isp, reason);
      super.addTransition(isp);
    }
    
    public ReasonedFairDiscreteSystem build() {
      FairDiscreteSystemImpl fds = super.build();
      ReasonedFairDiscreteSystem rfds = new ReasonedFairDiscreteSystem(fds);
      rfds.setInitialConditionReasons(initialConditionReasons.build());
      rfds.setTransitionReasons(transitionReasons.build());
      rfds.setCompassionReasons(compassionReasons.build());
      rfds.setJusticeReasons(justiceReasons.build());
      rfds.setSideConditionReasons(sideConditionReasons.build());
      return rfds;
    }
  }
  
  /** Compassion requirements' reasons */
  private ImmutableMultimap<Pair<? extends StateProperty, ? extends StateProperty>, Object> compassionReasons;
  /** Initial states' reasons */
  private ImmutableMultimap<StateProperty, Object> initialConditionReasons;

  /** Justice requirements' reasons */
  private ImmutableMultimap<StateProperty, Object> justiceReasons;

  /** Side conditions' reasons */
  private ImmutableMultimap<StateProperty, Object> sideConditionReasons;

  /** Transitions' reasons */
  private ImmutableMultimap<StateProperty, Object> transitionReasons;

  private ReasonedFairDiscreteSystem(FairDiscreteSystemImpl fds) {
    setVariables(fds.variables());
    setInternalVariables(fds.internalVariables());
    setInitialConditions(fds.initialStates());
    setTransitions(fds.transitions());
    setCompassionRequirements(fds.compassionSet());
    setJusticeRequirements(fds.justiceSet());
    setSideConditions(fds.sideConditions());
  }

  protected void setCompassionReasons(
      Multimap<Pair<? extends StateProperty, ? extends StateProperty>, Object> compassionReasons) {
    this.compassionReasons = ImmutableMultimap.copyOf(compassionReasons);
  }
  protected void setInitialConditionReasons(
      Multimap<StateProperty, Object> initialConditionReasons) {
    this.initialConditionReasons = ImmutableMultimap.copyOf(initialConditionReasons);
  }
  protected void setJusticeReasons(
      Multimap<StateProperty, Object> justiceReasons) {
    this.justiceReasons = ImmutableMultimap.copyOf(justiceReasons);
  }
  protected void setSideConditionReasons(
      Multimap<StateProperty, Object> sideConditionReasons) {
    this.sideConditionReasons = ImmutableMultimap.copyOf(sideConditionReasons);
  }

  protected void setTransitionReasons(
      Multimap<StateProperty, Object> transitionReasons) {
    this.transitionReasons = ImmutableMultimap.copyOf(transitionReasons);
  }
  
/*  public ReasonedFairDiscreteSystem(
      Set<IStateVariable> vars,
      IStateProperty initConds,
      Set<IStateProperty> transitions,
      Set<Pair<IStateProperty, IStateProperty>> compassion,
      Set<IStateProperty> justice,
      IStateProperty sideConds,
      Multimap<IStateProperty, Object> initCondReasons,
      Multimap<IStateProperty, Object> transitionReasons,
      Multimap<Pair<? extends IStateProperty, ? extends IStateProperty>, Object> compassionReasons,
      Multimap<IStateProperty, Object> justiceReasons,
      Multimap<IStateProperty, Object> sideCondReasons) {
    super(vars, initConds, transitions, compassion, justice, sideConds);

    this.initialConditionReasons = ImmutableMultimap.copyOf(initCondReasons);
    this.transitionReasons = ImmutableMultimap.copyOf(transitionReasons);
    this.compassionReasons = ImmutableMultimap.copyOf(compassionReasons);
    this.justiceReasons = ImmutableMultimap.copyOf(justiceReasons);
    this.sideConditionReasons = ImmutableMultimap.copyOf(sideCondReasons);
  }*/

  @Override
  public String toString() {
    StringBuffer sb = new StringBuffer();
    sb.append("========= FAIR DISCRETE SYSTEM ========\n");
    sb.append("Variables -----------------------------\n");
    sb.append(variables()).append("\n");
    sb.append("Side conditions ----------------------- Reasons\n");
    sb.append(sideConditions()).append("\nReasons:\n");
    for (StateProperty scond : sideConditionReasons.keySet()) {
      String s = scond.toString();
      sb.append(String.format("%-40s", s));
      if (s.length() > 40)
        sb.append(String.format("\n%-40s", ""));
      if (sideConditionReasons.containsKey(scond)
          && !sideConditionReasons.get(scond).isEmpty()) {
        for (Iterator<Object> i = sideConditionReasons.get(scond).iterator(); i
            .hasNext();)
          sb.append(i.next()).append(
              i.hasNext() ? String.format("\n%-40s", "") : "\n");
      } else
        sb.append("[no reason]\n");
    }
    sb.append("Initial states ------------------------ Reasons\n");
    sb.append(initialStates()).append("\nReasons:\n");
    for (StateProperty istate : initialConditionReasons.keySet()) {
      String s = istate.toString();
      sb.append(String.format("%-40s", s));
      if (s.length() > 40)
        sb.append(String.format("\n%-40s", ""));
      if (initialConditionReasons.containsKey(istate)
          && !initialConditionReasons.get(istate).isEmpty()) {
        for (Iterator<Object> i = initialConditionReasons
            .get(istate)
            .iterator(); i.hasNext();)
          sb.append(i.next()).append(
              i.hasNext() ? String.format("\n%-40s", "") : "\n");
      } else
        sb.append("[no reason]\n");
    }
    sb.append("Transitions --------------------------- Reasons\n");
    for (StateProperty t : transitions()) {
      String s = t.toString();
      sb.append(String.format("%-40s", s));
      if (s.length() > 40)
        sb.append(String.format("\n%-40s", ""));
      if (transitionReasons.containsKey(t)
          && !transitionReasons.get(t).isEmpty()) {
        for (Iterator<Object> i = transitionReasons.get(t).iterator(); i
            .hasNext();)
          sb.append(i.next()).append(
              i.hasNext() ? String.format("\n%-40s", "") : "\n");
      } else
        sb.append("[no reason]\n");
    }
    sb.append("Justice requirements ------------------ Reasons\n");
    for (StateProperty req : justiceRequirements()) {
      String s = req.toString();
      sb.append(String.format("%-40s", s));
      if (s.length() > 40)
        sb.append(String.format("\n%-40s", ""));
      if (justiceReasons.containsKey(req) && !justiceReasons.get(req).isEmpty()) {
        for (Iterator<Object> i = justiceReasons.get(req).iterator(); i
            .hasNext();)
          sb.append(i.next()).append(
              i.hasNext() ? String.format("\n%-40s", "") : "\n");
      } else
        sb.append("[no reason]\n");
    }
    sb.append("Compassion requirements --------------- Reasons\n");
    for (Pair<? extends StateProperty, ? extends StateProperty> req : compassionRequirements()) {
      String s = req.toString();
      sb.append(String.format("%-40s", s));
      if (s.length() > 40)
        sb.append(String.format("\n%-40s", ""));
      if (compassionReasons.containsKey(req)
          && !compassionReasons.get(req).isEmpty()) {
        for (Iterator<Object> i = compassionReasons.get(req).iterator(); i
            .hasNext();)
          sb.append(i.next()).append(
              i.hasNext() ? String.format("\n%-40s", "") : "\n");
      } else
        sb.append("[no reason]\n");
    }
    sb.append("=======================================\n");
    return sb.toString();
  }
}
