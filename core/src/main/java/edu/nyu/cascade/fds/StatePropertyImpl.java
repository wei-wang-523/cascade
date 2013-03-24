package edu.nyu.cascade.fds;

import java.util.List;
import java.util.Set;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.inject.internal.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.ExpressionTraversal;
import edu.nyu.cascade.prover.ExpressionTraversal.Visitor;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.IOUtils;

public class StatePropertyImpl extends StateExpressionImpl implements
    StateProperty {
  public static class Factory implements StateProperty.Factory {
    @Override
    public StateProperty valueOf(Expression expr) {
      return StatePropertyImpl.valueOf(expr);
    }
  }

  public static StatePropertyImpl valueOf(Expression p) {
    Preconditions.checkArgument(p.isBoolean());
    if (p instanceof StatePropertyImpl) {
      return (StatePropertyImpl) p;
    } else {
      return new StatePropertyImpl(p.asBooleanExpression());
    }
  }

  private final BooleanExpression expr;

// private final ExpressionManager exprManager;

  @Inject
  private StatePropertyImpl(@Assisted BooleanExpression expr) {
    super(expr);
// this.exprManager = expr.getExpressionManager();
    this.expr = expr.asBooleanExpression();
  }

  @Override
  public StatePropertyImpl and(Iterable<? extends Expression> conjuncts) {
    List<Expression> conjExprs = Lists.newArrayList();
    for (Expression p : conjuncts) {
      Preconditions.checkArgument(p.isBoolean());
      conjExprs.add(p);
    }
    return valueOf(toBooleanExpression().and(conjExprs));
  }

  @Override
  public StatePropertyImpl and(StateProperty... conjuncts) {
    List<BooleanExpression> conjExprs = Lists
        .newArrayListWithCapacity(conjuncts.length);
    for (StateProperty p : conjuncts) {
      conjExprs.add(p.toBooleanExpression());
    }
    return valueOf(toBooleanExpression().and(conjExprs));
  }

  /*
   * @Override public SatResult<?> checkSat() { IBooleanExpression bool =
   * toBooleanExpression(); ITheoremProver tp =
   * bool.getExpressionManager().getTheoremProver(); return tp.checkSat(bool); }
   * 
   * @Override public ValidityResult<?> checkValidity() { IBooleanExpression
   * bool = toBooleanExpression(); ITheoremProver tp =
   * bool.getExpressionManager().getTheoremProver(); return
   * tp.checkValidity(bool); }
   */
  @Override
  public StatePropertyImpl exists(Iterable<? extends Expression> vars) {
    return valueOf(toBooleanExpression().exists(vars));
  }

  @Override
  public StatePropertyImpl forall(
      final Iterable<? extends Expression> vars) {
    BooleanExpression bExpr = toBooleanExpression();
    BooleanExpression forallExpr = bExpr.forall(vars);

    Multimap<Expression, Expression> varToTriggerMap = ExpressionTraversal
        .traverse(bExpr, new Visitor<Multimap<Expression, Expression>>() {
          Multimap<Expression, Expression> varToTriggerMap = HashMultimap
              .create();

          @Override
          public Multimap<Expression, Expression> getResult() {
            return varToTriggerMap;
          }

          @Override
          public void visit(Expression expr) {
            IOUtils.debug().pln("Visiting " + expr);
            if (!(expr.isVariable() || expr.isConstant())) {
              for (Expression x : vars) {
                IOUtils.debug().pln("  >> Checking " + x);
                if (expr.getChildren().contains(x)) {
                  IOUtils.debug().pln("    >> Adding " + expr);
                  varToTriggerMap.put(x, expr);
                }
              }
            }
          }
        });

    /* Form the cross-product of all the detected triggers per-variable */
    ImmutableList<ImmutableList<Expression>> triggerLists = null;
    for (Expression x : varToTriggerMap.keySet()) {
      assert (varToTriggerMap.get(x) != null);
      assert (!varToTriggerMap.get(x).isEmpty());

      if (triggerLists == null) {
        /* Initialize triggerLists with current triggers */
        triggerLists = ImmutableList.of(ImmutableList.copyOf(varToTriggerMap
            .get(x)));
      } else {
        assert (!triggerLists.isEmpty());
        /*
         * For every existing multi-trigger m and every trigger p for variable
         * x, form a new multi-trigger {p} ⋃ m.
         */
        ImmutableList.Builder<ImmutableList<Expression>> newTriggers = ImmutableList
            .builder();
        for (ImmutableList<Expression> multiTrigger : triggerLists) {
          for (Expression trigger : varToTriggerMap.get(x)) {
            ImmutableList.Builder<Expression> newMultiTrigger = ImmutableList
                .builder();
            newMultiTrigger.add(trigger);
            newMultiTrigger.addAll(multiTrigger);
            newTriggers.add(newMultiTrigger.build());
          }
        }
        triggerLists = newTriggers.build();
      }
    }
    if (triggerLists != null) {
      IOUtils.debug().pln("Triggers for: " + bExpr + "\n" + triggerLists);
      forallExpr.setMultiTriggers(triggerLists);
    }

    return valueOf(forallExpr);
  }

  /*
   * public ExpressionManager getExpressionManager() { return exprManager; }
   */
  public ImmutableSet<StateVariable> getVariables() {

    return ExpressionTraversal.traverse(expr,
        new Visitor<ImmutableSet<StateVariable>>() {
          ImmutableSet.Builder<StateVariable> bldr = new ImmutableSet.Builder<StateVariable>();

          @Override
          public ImmutableSet<StateVariable> getResult() {
            return bldr.build();
          }

          @Override
          public void visit(Expression e) {
            if (e.isVariable()) {
              // assert( e.getType() instanceof ComparableType );
              bldr.add(StateVariableImpl.lookup((VariableExpression) e
                  .getExpressionManager().asVariable(e)));
            }
          }
        });
  }

  @Override
  public StatePropertyImpl iff(Expression p) {
    return valueOf(toBooleanExpression().iff(p));
  }

  @Override
  public StateExpression ifThenElse(Expression thenPart, Expression elsePart) {
    return StateExpressionImpl.valueOf(expr.ifThenElse(thenPart, elsePart));
  }

  @Override
  public StatePropertyImpl implies(Expression p) {
    return valueOf(toBooleanExpression().implies(p));
  }

  @Override
  public StatePropertyImpl not() {
    return valueOf(toBooleanExpression().not());
  }

  @Override
  public StatePropertyImpl or(Iterable<? extends Expression> disjuncts) {
    List<Expression> disjExprs = Lists.newArrayList();
    for (Expression p : disjuncts) {
      disjExprs.add(p);
    }
    return valueOf(toBooleanExpression().or(disjExprs));
  }

  @Override
  public StatePropertyImpl or(StateProperty... disjuncts) {
    List<BooleanExpression> disjExprs = Lists
        .newArrayListWithCapacity(disjuncts.length);
    for (StateProperty p : disjuncts) {
      disjExprs.add(p.toBooleanExpression());
    }
    return valueOf(toBooleanExpression().or(disjExprs));
  }

  @Override
  public StatePropertyImpl prime() {
    // IOUtils.debug().indent().pln("PRIMING ISP: " + this);
    // IOUtils.debug().indentMore();

    Set<StateVariable> xs = getVariables();
    Iterable<StateVariable> ys = StateVariables.prime(xs);
    BooleanExpression b = toBooleanExpression();
    // IExpressionManager exprManager = getExpressionManager();

    BooleanExpression bPrime = b.subst(xs, ys).asBooleanExpression();
    if (!Iterables.isEmpty(b.getTriggers())
        && Iterables.isEmpty(bPrime.getTriggers())) {
      /*
       * Expression Manager didn't preserve the triggers. Manually prime them.
       */
      List<List<Expression>> triggersPrime = Lists.newArrayList();
      for (ImmutableList<? extends Expression> multiTrigger : bPrime
          .getTriggers()) {
        List<Expression> multiTriggerPrime = Lists.newArrayList();
        for (Expression trigger : multiTrigger) {
          multiTriggerPrime.add(trigger.subst(xs, ys));
        }
        triggersPrime.add(multiTriggerPrime);
      }
      bPrime.setMultiTriggers(triggersPrime);
    }
    StatePropertyImpl primed = valueOf(bPrime);

    // IOUtils.debug().indentLess();
    // IOUtils.debug().indent().pln("<< " + primed);

    return primed;
  }

  @Override
  public BooleanExpression toBooleanExpression() {
    return expr.asBooleanExpression();
  }

  @Override
  public String toString() {
    return expr.toString();
  }

  @Override
  public StatePropertyImpl unprime() {
    Set<StateVariable> xs = getVariables();
    Iterable<StateVariable> ys = StateVariables.unprime(xs);
    BooleanExpression b = toBooleanExpression();
    ExpressionManager exprManager = getExpressionManager();
    return valueOf(exprManager.asBooleanExpression(exprManager.subst(b, xs, ys)));
  }

  @Override
  public StatePropertyImpl xor(Expression p) {
    return valueOf(toBooleanExpression().xor(p));
  }

  @Override
  public void addMultiTrigger(Iterable<? extends Expression> multiTrigger) {
    // NOTE: This assumes the underlying object returned by toBooleanExpression
    // is the same as expression.
    toBooleanExpression().addMultiTrigger(multiTrigger);
  }

  @Override
  public void addTrigger(Expression p) {
    // NOTE: This assumes the underlying object returned by toBooleanExpression
    // is the same as expression.
    toBooleanExpression().addTrigger(p);
  }

  @Override
  public StatePropertyImpl and(Expression e) {
    return valueOf(toBooleanExpression().and(e));
  }

  @Override
  public ImmutableList<ImmutableList<? extends Expression>> getTriggers() {
    // NOTE: This assumes the underlying object returned by toBooleanExpression
    // is the same as expression.
    return toBooleanExpression().getTriggers();
  }

  @Override
  public StateProperty or(Expression e) {
    return valueOf(toBooleanExpression().or(e));
  }

  @Override
  public void setMultiTriggers(
      Iterable<? extends Iterable<? extends Expression>> multiTriggers) {
    // NOTE: This assumes the underlying object returned by toBooleanExpression
    // is the same as expression.
    toBooleanExpression().setMultiTriggers(multiTriggers);
  }

  @Override
  public void setTriggers(Iterable<? extends Expression> triggers) {
    // NOTE: This assumes the underlying object returned by toBooleanExpression
    // is the same as expression.
    toBooleanExpression().setTriggers(triggers);
  }

  @Override
  public BooleanExpression toExpression() {
    return toBooleanExpression();
  }

  @Override
  public StateProperty exists(Expression firstVar,
      Expression... otherVars) {
    return valueOf(toBooleanExpression().exists(firstVar, otherVars));
  }

  @Override
  public StateProperty forall(Expression firstVar,
      Expression... otherVars) {
    return valueOf(toBooleanExpression().forall(firstVar, otherVars));
  }

  @Override
  public void setBoundVars(Iterable<? extends Expression> vars) {
    toBooleanExpression().setBoundVars(vars);  
  }

  @Override
  public ImmutableList<? extends Expression> getBoundVars() {
    return toBooleanExpression().getBoundVars();
  }

  @Override
  public void setBody(BooleanExpression expr) {
    toBooleanExpression().setBody(expr);
  }

  @Override
  public BooleanExpression getBody() {
    return toBooleanExpression().getBody();
  }
}
