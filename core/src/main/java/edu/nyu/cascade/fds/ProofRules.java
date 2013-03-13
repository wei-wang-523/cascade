package edu.nyu.cascade.fds;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;

public class ProofRules {

  /*
   * Attempt to prove that the property <code>p</code> is an inductive invariant
   * in <code>tsn</code>.
   */
  public static ValidityResult<?> binv(StateProperty p, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule BINV to: " + p);

    /* I1. I ⇒ p */
    IOUtils.out().println("Checking Premise I1");
    StateProperty i1 = tsn.initialStates().implies(p);
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);

    if (!res.isValid()) {
      IOUtils.out().println("Premise I1 is not valid.");
      IOUtils.out().println("Counterexample:");
      printCounterExample(res);
      return res;
    }

    /* I2. p ∧ T ⇒ p', where T=tsn.transitions() */
    IOUtils.out().println("Premise I1 is valid. Checking Premise I2.");
//    for (IStateProperty t : tsn.transitions()) {
//      IStateProperty i2 = p.and(t).implies(p.prime());
      StateProperty i2 = p.and(tsn.transitionRelation()).implies(p.prime());
      IOUtils.debug().pln(i2.toString());
      res = tsn.checkValidity(i2);
      if (!res.isValid()) {
        IOUtils.out().println("Premise I2 is not valid.");
        IOUtils.out().println("Counterexample:");
        printCounterExample(res);
        return res;
      }
//    }
    IOUtils.out()
          .println("Premise I2 is valid.\n * * * Assertion p is invariant.\n");
    return res;
  }

  private static void printCounterExample(ValidityResult<?> res) {
    for (BooleanExpression ibe : res.getCounterExample()) {
      IOUtils.out().println(ibe);
    }
  }

  /*
   * Attempt to prove that the property <code>p</code> is an invariant
   * in <code>tsn</code> using the inductive strengthening <code>phi</code>.
   */
  public static ValidityResult<?> inv(StateProperty p, StateProperty phi, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule INV to: " + p + "\nStrengthening invariant: " + phi);
    
    /* I1. I ⇒ φ */
    IOUtils.out().println("Checking Premise I1");
    StateProperty i1 = tsn.initialStates().implies(phi);
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);

    if (!res.isValid()) {
      IOUtils.out().println("Premise I1 is not valid.");
      IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
      return res;
    }

    /* I2. φ ∧ T ⇒ φ', where T=tsn.transitions() */
    IOUtils.out().println("Premise I1 is valid. Checking Premise I2.");
//    for (IStateProperty t : tsn.transitions()) {
      StateProperty i2 = phi.and(tsn.transitionRelation()).implies(phi.prime());
      IOUtils.debug().pln(i2.toString());
      res = tsn.checkValidity(i2);
      if (!res.isValid()) {
        IOUtils.out().println("Premise I2 is not valid.");
        IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
        return res;
      }
//    }
    
    /* I3. φ ⇒ p */
    IOUtils.out().println("Premise I2 is valid. Checking Premise I3.");
    StateProperty i3 = phi.implies(p);
    IOUtils.debug().pln(i3.toString());
    res = tsn.checkValidity(i3);
    if (!res.isValid()) {
      IOUtils.out().println("Premise I3 is not valid.");
      IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
      return res;
    } 
    
    IOUtils.out()
          .println("Premise I3 is valid.\n * * * Assertion p is invariant.\n");
    return res;
  }
  
  /*
   * Attempt to prove the property "start ⇒ ⋄goal" (if start holds, goal will
   * eventually hold) using the rule WELL. The rule uses an invariant, a set of
   * "helpful" assertions, and a ranking function delta over some well-founded
   * set. Each helpful assertion helpful[i] should contradict the ith justice
   * requirement of the fair discrete system. The rule proceeds by showing (1)
   * start and the invariant imply the goal or one of the helpful assertions and
   * (2) whenever the invariant and a helpful assertion helpful[i] hold in one
   * state, either (a) helpful[i] holds in the next state, the rank stays the
   * same, and the i'th justice requirement does not hold, (b) another helpful
   * assertion holds in the next state and the rank strictly decreases, or (c)
   * goal holds in the next state.
   */
  static ValidityResult<?> wellx(
      StateProperty start, StateProperty goal, StateProperty inv,
      StateProperty helpfuls[], IntegerStateExpression delta,
      FairDiscreteSystem fds) {
    /*
     * In comments below: p=start, q=goal, φ=inv, h=helpfuls, δ=delta,
     * T=fds.transitions(), and J=fds.justiceRequirements
     */
    Preconditions
        .checkArgument(helpfuls.length == fds.justiceRequirements().length);

    /* Preparation. Construct a disjunction of helpfuls. */
    StateProperty pend = StateProperties.or(Arrays.asList(helpfuls));

    /* W1. p ∧ φ ⇒ q ∨ ∃j: h[j] */
    StateProperty w1 = start.and(inv).implies(goal.or(pend));
    ValidityResult<?> res = fds.checkValidity(w1);

    if (!res.isValid()) {
      IOUtils.out().println("Premise 1 false.");
      return res;
    }

    /*
     * W2. ∀i: φ ∧ h[i] ∧ T ⇒ (h[i]' ∧ δ = δ' ∧ ¬J[i]) ∨ q' ∨ (δ > δ' ∧ ∃j:
     * h[j]')
     */
    for (int i = 0; i < helpfuls.length; i++) {
      StateProperty w2 = inv.and(helpfuls[i]).and(fds.transitionRelation())
          .implies(
              helpfuls[i].prime().and(delta.eq(delta.prime()),
                  fds.justiceRequirements()[i].not()).or(goal.prime()).or(
                  delta.greaterThan(delta.prime()).and(pend.prime())));
      res = fds.checkValidity(w2);

      if (!res.isValid()) {
        IOUtils.out().println("Premise 2 false for i=" + i);
        return res;
      }
    }
    assert (res.isValid());
    IOUtils.out().println("Property is valid.");
    return res;
  }

  /*
   * Attempt to prove the property "if start holds, goal will eventually hold."
   * with parameterized systems using the rule DISTR-RANK. The rule uses an
   * invariant, a set of "helpful" assertions, and a set of ranking functions
   * over some well-founded set.
   * @author Chanseok Oh
   */
  static ValidityResult<?> well(
      StateProperty start, StateProperty goal, StateProperty inv,
      StateProperty helpfuls[], IntegerStateExpression deltas[],
      FairDiscreteSystem fds) {
    /*
     * In comments below: p=start, q=goal, i=inv, h=helpfuls, d=deltas,
     * T=fds.transitions(), and J=fds.justiceRequirements
     */
    Preconditions
        .checkArgument(helpfuls.length == fds.justiceRequirements().length);

    /* Preparation. Construct a disjunction of helpfuls. */
    StateProperty pend = StateProperties.or(Arrays.asList(helpfuls));

    /* D1. p & i -> q | (OR over h) */
    StateProperty d1 = start.and(inv).implies(goal.or(pend));
    ValidityResult<?> res = fds.checkValidity(d1);

    if (!res.isValid()) {
      IOUtils.out().println("Premise 1 false.");
      return res;
    }

    /* What would happen if delta.length = 0? */
    List<StateProperty> geqDeltas = Lists.newArrayListWithCapacity(deltas.length);
    List<StateProperty> gtDeltas = Lists.newArrayListWithCapacity(deltas.length);
    for (int i = 0; i < deltas.length; i++) {
        geqDeltas.add(deltas[i].greaterThanOrEqual(deltas[i].prime()));
        gtDeltas.add(deltas[i].greaterThan(deltas[i].prime()));
    }
    /* AND over d[i] >= d[i]' */
    StateProperty conjDeltas = StateProperties.and(geqDeltas);
    /* OR over d[i] > d[i]' */
    StateProperty disjDeltas = StateProperties.and(gtDeltas);

    /* D2. ( i & h[i] & T & !q ) -> ( h[i]' & !J[i] | q' | ((OR over h') & disjDeltas) ) */
    for (int i = 0; i < helpfuls.length; i++) {
      StateProperty d2 = inv.and(helpfuls[i]).and(fds.transitionRelation()).and(goal.not()).implies(
          helpfuls[i].prime().and(
              fds.justiceRequirements()[i].not()).or(goal.prime()).or(
              disjDeltas.and(pend.prime())));
      res = fds.checkValidity(d2);

      if (!res.isValid()) {
        IOUtils.out().println("Premise 2 false for i=" + i);
        return res;
      }
    }

    /* D3. ( i & (OR over h) & T & !q ) -> ( q' | conjDeltas ) */
    StateProperty d3 = inv.and(pend).and(fds.transitionRelation()).and(goal.not()).implies(
        goal.prime().or(conjDeltas));
    res = fds.checkValidity(d3);

    if (!res.isValid()) {
      IOUtils.out().println("Premise 3 false.");
      return res;
    }

    assert (res.isValid());
    IOUtils.out().println("Property is valid.");
    return res;
  }

/******
    Attempt to prove the REFL-B-WAIT rule:
    
    {phi and (not psi)} T {phi}
    _______________________________
    
    phi => phi W psi
   
   @author Liana Hadarean 
      
******/


  public static ValidityResult<?> reflBWait(StateProperty phi, StateProperty psi, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule REFL-B-WAIT to: " + phi + " => " + phi + " W " + psi + "\n");

    /***** 
    W1. phi and (not psi) and T => (phi) 
    *****/
    IOUtils.out().println("Checking Premise W1");
    StateProperty i1 = phi.and((psi.not()),tsn.transitionRelation()).implies(phi.prime());
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);
    if (!res.isValid()) {
      IOUtils.out().println("Premise W1 is not valid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    IOUtils.out().println("Premise W1 is valid.\n * * * The REFL-B-WAIT property is satisfied.\n");
    return res;
  }


/******
    Attempt to prove the REFL-WAIT rule:
    
    W1. p => psi or r
    W2. psi => q or r
    W3. {psi and (not r)} T {psi}
    _______________________________
    
    p => q W r
   
   @author Liana Hadarean 
      
******/

  public static ValidityResult<?> reflWait(StateProperty p, StateProperty q, StateProperty r, StateProperty psi, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule REFL-WAIT to: " + p + " => " + q + " W " + r + "\n");
    IOUtils.out().println("Strengthening " + q +" or " +r + ": " + psi);

    /******
    W1. p => (psi or r) 
    ******/
    
    IOUtils.out().println("Checking Premise W1...");
    StateProperty i1 = p.implies(psi.or(r));
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);
    if (!res.isValid()) {
      IOUtils.out().println("Premise W1 is invalid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    /******
    W2. psi => q or r 
    ******/
    IOUtils.out().println("Premise W1 is valid.");
    IOUtils.out().println("Checking Premise W2...");
    StateProperty i2 = psi.implies(q.or(r));
    IOUtils.debug().pln(i2.toString());
    res = tsn.checkValidity(i2);
    if (!res.isValid()) {
      IOUtils.out().println("Premise W2 is invalid.");
      IOUtils.out().println("Counterexample:");
      printCounterExample(res);
      return res;
    }

    /******
    W3. (psi and (not r) and T) => psi' 
    ******/
    IOUtils.out().println("Premise W2 is valid.");
    IOUtils.out().println("Checking Premise W3");
    StateProperty i3 = psi.and((r.not()).and(tsn.transitionRelation())).implies(psi.prime());
    IOUtils.debug().pln(i3.toString());
    res = tsn.checkValidity(i3);
    if (!res.isValid()) {
      IOUtils.out().println("Premise W3 is invalid.");
      IOUtils.out().println("Counterexample:");
      printCounterExample(res);
      return res;
    }

    IOUtils.out().println("Premise W3 is valid.\n * * * The REFL-WAIT property is satisfied.\n");
    return res;
  }


  /**
   * Attempt to prove the property "p ⇒ q B r" (p-state is preceded by 
   * a succession of q-interval that may be terminated by an occurence 
   * of r) using the rule BACK-TO and an assertion φ. 
   * @author Wei Wang
   */
  public static ValidityResult<?> back(StateProperty p, StateProperty q, StateProperty r, StateProperty phi, TransitionSystem tsn) {

    /*
     * In comments below: p, q, r, φ, T=tsn.transitions().
     */

    IOUtils.out().println("Apply \"Back-to rule\" to:");
    IOUtils.out().println("p:  " + p + "\n  =>" + "\nq:  " + q + "\n  Back to\n" + "r:  " + r + "\nVia strengthening invariant \nφ:  " + phi);

    /*
     * Print the following notes:
     * Apply "Back-to rule" to:
     * p:  
     *   =>
     * q:
     *   Back-to
     * r:
     * 
     * Via strenghtening invariant
     * φ:
     */

    /* B1. p ⇒ φ ∨ r */
    IOUtils.out().println("\nChecking Premise B1");
    StateProperty i1 = p.implies(phi.or(r));
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);

    if (!res.isValid()) {
      IOUtils.out().println("\nPremise B1 is not valid.");
      IOUtils.out().println("\nCounterexample:\n" + res.getCounterExample());
      return res;
    }

    /* B2. φ ⇒ q */
    IOUtils.out().println("\nPremise B1 is valid. Checking Premise B2.");
    StateProperty i2 = phi.implies(q);
    IOUtils.debug().pln(i2.toString());
    res = tsn.checkValidity(i2);

    if (!res.isValid()) {
      IOUtils.out().println("\nPremise B2 is not valid.");
      IOUtils.out().println("\nCounterexample:\n" + res.getCounterExample());
      return res;
    }

    /* B3. φ' ∧ (T^(-1)) ⇒ φ ∨ r, where T = tsn.transitions() */
    IOUtils.out().println("\nPremise B2 is valid. Checking Premise B3.");
    StateProperty i3 = (phi.prime()).and(tsn.transitionRelation()).implies(phi.or(r));
    IOUtils.debug().pln(i3.toString());
    res = tsn.checkValidity(i3);
    
    if (!res.isValid()) {
      IOUtils.out().println("\nPremise B3 is not valid.");
      IOUtils.out().println("\nCounterexample:\n" + res.getCounterExample());
      return res;
    }

    IOUtils.out()
          .println("\nPremise B3 is valid.\n\n * * * Assertion p ⇒ q B r is invariant.\n");
    return res;
  }

  /**
   * Attempt to prove the Nested Back-to formular "p ⇒ q[m-1] B q[m-2] B ... B q[0]",
   * which ensures that every p is preceeded by q[m-1]-interval, preceeded by q[m-2]
   * -interval, ..., preceeded by q[1]-interval, possibly terminated by a q[0]-position.
   * The basic rule for establishing nested back-to properties is rule NBACK. The premise
   * of the rule introduces assertions φ[] and requires that each transition of the
   * program lead from an accessible state that statisfies φ[i], for i > 0, to a
   * predecessor state that satisfies φ[j], for some j <= i.
   * @author Wei Wang
   */

  public static ValidityResult<?> nback(StateProperty p, StateProperty q[], StateProperty phi[], TransitionSystem tsn) {

    /*
     * In comments below: p, q[], φ[], T=tsn.transitions().
     */

    Preconditions
        .checkArgument(q.length == phi.length);

    /*
     * In preconditions, we check if the length of q[] is equal to the length of φ[].
     */

    IOUtils.out().println("Apply rule \"Nested Back-to rule\" to:\np:  " + p + "\n  =>");

    for (int i = (q.length - 1); i >= 0; i--) {
      if (i > 0) {
        IOUtils.out().println("q[" + i + "]:  " + q[i]);
        IOUtils.out().println("  Back-to"); 
      }
      else
        IOUtils.out().println("q[" + i + "]:  " + q[i]);
    }

    IOUtils.out().println("\nVia strenghtening invariants:");

    for (int i = 0; i < phi.length; i++) {
      IOUtils.out().println("φ[" + i + "]:  " + phi[i]);
    }

    /*
     * Print the following notes:
     * Apply rule "Nest Back-to rule" to:
     * p:  
     *   =>
     * q[m-1]:
     *   Back-to
     * q[m-2]:
     *   Back-to
     * ...
     * q[0]:
     *
     * Via strenghtening invariants:
     * φ[0]:
     * φ[1]:
     * ...
     * φ[m-1]:
     */

    /* N1. p ⇒ ∃i: φ[i] */

    StateProperty MI = phi[0];
    for (int i = 0; i < phi.length; i++) {        
      MI = MI.or(phi[i]);
    } 

    /* 
     * MI = phi[0] ∨ ... ∨ phi[phi.length-1].
     */

    StateProperty N1 = p.implies(MI);
    /*
     * We verify the property "N1. p ⇒ ∃i: φ[i]".
     */     

    IOUtils.debug().pln(N1.toString());
    ValidityResult<?> res = tsn.checkValidity(N1);

    if (!res.isValid()) {
      IOUtils.out().println("\nPremise N1 false.");
      IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
      return res;
    }

    /* N2. ∀i: φ[i] ⇒ q[i] */
    IOUtils.out().println("\nPremise N1 is valid. Checking Premise N2.");

    for (int i = 0; i < phi.length; i++) {
      StateProperty N2 = phi[i].implies(q[i]);
      IOUtils.debug().pln(N2.toString());
      res = tsn.checkValidity(N2);

      if (!res.isValid()) {
        IOUtils.out().println("\nPremise N2 false for i=" + i);
        IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
        return res;
      }
    }

    /* N3. ∀i in [1..m]: φ[i]' ∧ (T^(-1)) ⇒  ∃j<=i: φ[j] */

    IOUtils.out().println("\nPremise N2 is valid. Checking Premise N3.");

    for (int i = 1; i < phi.length; i++) {

      StateProperty NI = phi[0];      
      
      for (int j = 0; j <= i; j++) {
        
        NI = NI.or(phi[j]);
        /* 
         * NI = phi[0] ∨ ... ∨ phi[i]
         */
      }
      
      StateProperty N3 = (phi[i].prime().and(tsn.transitionRelation())).implies(NI);
      IOUtils.debug().pln(N3.toString());
      res = tsn.checkValidity(N3);

      /*
       * We verify the property "φ[i]' ∧ (T^(-1)) ⇒  ∃j<=i: φ[j]"
       */

      if (!res.isValid()) {
        IOUtils.out().println("\nPremise N3 false for i=" + i);
        IOUtils.out().println("Counterexample:\n" + res.getCounterExample());
        return res;        
      }

    }//endfor
    
    IOUtils.out().println("\nPremise N3 is valid.\n\n * * * Property is valid.\n");

    return res;
    /*
     * Once we finish the outer for-loop, we know the
     * Premise N3: ∀i: φ[i]' ∧ (T^(-1)) ⇒  ∃j<=i: φ[j], is valid. 
     */

  }

  /*
   * Attempt to prove the basic waiting-for rule such that p => p w q.
   * @author Junjie Chen 
   */
  public static ValidityResult<?> waitB(StateProperty p, StateProperty q, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule WAIT-B to: " + p + " => " + p + " W " + q + "\n");

    /* I1. p /\ T -> (p' \/ q'), where T=tsn.transitions() */
    IOUtils.out().println("Checking Premise I1");
    StateProperty i1 = p.and(tsn.transitionRelation()).implies(p.prime().or(q.prime()));
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);
    if (!res.isValid()) {
      IOUtils.out().println("Premise I1 is not valid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    IOUtils.out().println("Premise I1 is valid.\n * * * The Basic wait-for formula is satisfied.\n");
    return res;
  }

  /*
   * Attempt to prove the waiting-for rule such that p => q W r using the 
   * inductive strengthening phi.
   * @author Junjie Chen
   */
  public static ValidityResult<?> wait(StateProperty p, StateProperty q, StateProperty r, StateProperty phi, TransitionSystem tsn) {
    IOUtils.out().println("Apply rule WAIT to: " + p + " => " + q + " W " + r + "\nStrengthening " + q + ": " + phi);

    /* I1. p -> (phi \/ r) */
    IOUtils.out().println("Checking Premise I1");
    StateProperty i1 = p.implies(phi.or(r));
    IOUtils.debug().pln(i1.toString());
    ValidityResult<?> res = tsn.checkValidity(i1);
    if (!res.isValid()) {
      IOUtils.out().println("Premise I1 is not valid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    /* I2. phi -> q */
    IOUtils.out().println("Premise I1 is valid. Checking Premise I2");
    StateProperty i2 = phi.implies(q);
    IOUtils.debug().pln(i2.toString());
    res = tsn.checkValidity(i2);
    if (!res.isValid()) {
      IOUtils.out().println("Premise I2 is not valid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    /* I3. phi /\ T -> phi' \/ r', where T=tsn.transitions() */
    IOUtils.out().println("Premise I2 is valid. Checking Premise I3");
    StateProperty i3 = phi.and(tsn.transitionRelation()).implies(phi.prime().or(r.prime()));
    IOUtils.debug().pln(i3.toString());
    res = tsn.checkValidity(i3);
    if (!res.isValid()) {
      IOUtils.out().println("Premise I3 is not valid.\n");
      IOUtils.out().println("Counterexample:\n");
      printCounterExample(res);
      return res;
    }

    IOUtils.out().println("Premise I3 is valid.\n * * * The wait-for formula is satisfied.\n");
    return res;
  }

}
