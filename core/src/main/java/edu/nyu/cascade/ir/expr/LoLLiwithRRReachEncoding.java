package edu.nyu.cascade.ir.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class LoLLiwithRRReachEncoding extends ReachEncoding {
  
  public static ReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return ReachMemoryModel.create(encoding, size, size);
  }

  private final Type eltType;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private final Expression f;
  
  /** The (elt, elt, elt) -> bool mapping */
  private final Expression rf_avoid;
  
  /** The elt -> bool mapping */
  private final Expression cycle;
  
  /** The (elt, elt) -> elt mapping */
  private final Expression join;
  
  public LoLLiwithRRReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      
      eltType = wordType;
      
      /* Create function expression */
      
      nil = exprManager.bitVectorZero(eltType.asBitVectorType().getSize()); // nil = 0(NULL);
      f = exprManager.functionVar(FUN_F, exprManager.functionType(FUN_F, eltType, eltType), false);
      rf_avoid = exprManager.functionVar(FUN_RF_AVOID, exprManager.functionType(FUN_RF_AVOID,
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType()), false);
      cycle = exprManager.functionVar(FUN_CYCLE, exprManager.functionType(FUN_CYCLE,
          eltType, exprManager.booleanType()), false);
      join = exprManager.functionVar(FUN_JOIN, 
          exprManager.functionType(FUN_JOIN, ImmutableList.of(eltType, eltType), eltType), false);

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      
      VariableExpression x = eltType.boundVariable("x", true); 
      VariableExpression y = eltType.boundVariable("y", true);
      VariableExpression z = eltType.boundVariable("z", true);
      VariableExpression u = eltType.boundVariable("u", true);
      VariableExpression v = eltType.boundVariable("v", true);
      
      ImmutableList<VariableExpression> vars = null;
      ImmutableList<Expression> triggers = null;
      Expression head, body, _let_0;
      BooleanExpression guard;
      BooleanExpression rrDeductionExpr;
      
      /* Create a f(null)=null assumption */
      
      BooleanExpression nil_assumption = applyF(nil).eq(nil);
      
      rewrite_rulesetBuilder.add(nil_assumption);
      
      /* Create a reflex rule */
      /*
      vars = ImmutableList.of(x, u); // x, u
       Rf_avoid(x, x, u) 
      body = applyRfAvoid(x, x, u);
      BooleanExpression reflex_rule = exprManager.forall(vars, body);
      
      rewrite_rulesetBuilder.add(reflex_rule); 
      */
      /* Create a step rule */
      
      vars = ImmutableList.of(x, u);
      /* Rf_avoid(x, f(x), u) || x = u */
      guard = exprManager.tt();      
      head = exprManager.neq(x, u);
      _let_0 = applyF(x);
      body = applyRfAvoid(x, _let_0, u);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression step_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a selfLoop rule */
      
      vars = ImmutableList.of(x, y); // x, y
      _let_0 = applyF(x); // f(x)
      /* f(x) = x && Rf_avoid(x, y, y) => x = y */
      // FIXME: why cannot put f(x) = x into the head part?
      guard = _let_0.eq(x);
      head = applyRfAvoid(x, y, y);
      body = x.eq(y);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression selfLoop_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(selfLoop_rule);     
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(x, y); // x, y
      /* Rf_avoid(x, y, x) => x = y */
      guard = exprManager.tt(); 
      head = applyRfAvoid(x, y, x);
      body = exprManager.eq(x, y);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression sandwich_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(x, y, u);
      /* Rf_avoid(x, y, u) => Rf_avoid(x, y, y) */
      guard = exprManager.tt(); 
      head = applyRfAvoid(x, y, u);
      body = applyRfAvoid(x, y, y);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression reach_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a linear1 rule */
      
      vars = ImmutableList.of(x, y, u);
      /* Rf_avoid(x, y, y) && x != u => Rf_avoid(x, u, y) || Rf_avoid(x, y, u) */
      // FIXME: why cannot put x.neq(u) as guard?
      guard = exprManager.tt(); 
      head = applyRfAvoid(x, y, y).and(x.neq(u));
      body = exprManager.or(applyRfAvoid(x, u, y), applyRfAvoid(x, y, u));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression line1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(line1_rule);
      
      /* Create a linear2 rule */
      
      vars = ImmutableList.of(x, y, z, u, v);
      /* Rf_avoid(x, y, u) && Rf_avoid(x, z, v) => 
       * (Rf_avoid(x, z, u) && Rf_avoid(z, y, u)) || (Rf_avoid(x, y, v) && Rf_avoid(y, z, v))
       */
      guard = exprManager.tt();
      head = exprManager.and(applyRfAvoid(x, y, u), applyRfAvoid(x, z, v));
      body = exprManager.or(
          exprManager.and(applyRfAvoid(x, z, u),
              applyRfAvoid(z, y, u)), 
          exprManager.and(applyRfAvoid(x, y, v),
              applyRfAvoid(y, z, v)));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression line2_rule =  exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(line2_rule);      
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(x, y, z, u);
      /* Rf_avoid(x, y, u) && Rf_avoid(y, z, u) => Rf(x, z, u)*/
      guard = exprManager.tt();
      head = exprManager.and(applyRfAvoid(x, y, u), applyRfAvoid(y, z, u));
      body = applyRfAvoid(x, z, u);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression trans1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(x, y, z, u);
      /* Rf_avoid(x, y, z) && Rf_avoid(y, u, z) && Rf_avoid(y, z, z) => Rf(x, y, u) */
      // FIXME: why cannot put three clauses into the head?
      guard = applyRfAvoid(y, z, z);
      head = exprManager.and(applyRfAvoid(x, y, z), applyRfAvoid(y, u, z));
      body = applyRfAvoid(x, y, u);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression trans2_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a join1 rule */
      
      vars = ImmutableList.of(x, y); // x, y
      _let_0 = applyJoin(x, y);
      /* Rf_avoid(x, join(x, y), join(x, y) */
      guard = exprManager.tt();
      head = exprManager.tt();
      body = applyRfAvoid(x, _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression join1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(join1_rule);
      
      /* Create a join2 rule */
      
      vars = ImmutableList.of(x, y, z);
      _let_0 = applyJoin(x, y);
      /* Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(y, join(x, y), join(x, y))*/
      guard = exprManager.tt();
      head = exprManager.and(applyRfAvoid(x, z, z), applyRfAvoid(y, z, z));
      body = applyRfAvoid(y, _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression join2_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(join2_rule);
      
      /* Create a join3 rule */
      
      vars = ImmutableList.of(x, y, z);
      _let_0 = applyJoin(x, y);
      /* Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(x, join(x, y), z) */
      guard = exprManager.tt();
      head = exprManager.and(applyRfAvoid(x, z, z), applyRfAvoid(y, z, z));
      body = applyRfAvoid(x, _let_0, z);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression join3_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(join3_rule);
      
      /* Create a join4 rule */
      
      vars = ImmutableList.of(x, y); 
      _let_0 = applyJoin(x, y);
      /* Rf_avoid(y, join(x, y) join(x, y)) || x = join(x, y) */
      guard = exprManager.tt();
      head = exprManager.tt();
      body = exprManager.or(applyRfAvoid(y, _let_0, _let_0), _let_0.eq(x));
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression join4_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(join4_rule);
      
      /* Create a cycle1 rule */
      
      vars = ImmutableList.of(x, y);
      _let_0 = applyCycle(x);
      /* Rf_avoid(x, y, y) && Rf_avoid(y, x, x) => cycle(x) || x = y */
      guard = exprManager.tt();
      head = exprManager.and(applyRfAvoid(x, y, y), applyRfAvoid(y, x, x));
      body = exprManager.or(_let_0, x.eq(y));
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression cycle1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(cycle1_rule);
      
      /* Create a cycle2 rule */
      
      vars = ImmutableList.of(x, y);
      _let_0 = applyCycle(x);
      /* cycle(x) && Rf_avoid(x, y, y) => Rf_avoid(y, x, x) */
      guard = exprManager.tt();
      head = exprManager.and(_let_0, applyRfAvoid(x, y, y));
      body = applyRfAvoid(y, x, x);
      triggers = ImmutableList.of(_let_0);
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression cycle2_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(cycle2_rule);
            
      rewrite_rules = rewrite_rulesetBuilder.build();
      
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  @Override
  public Expression functionCall(String name, Iterable<? extends Expression> argsIter) {
    List<Expression> args = ImmutableList.copyOf(argsIter);
    try {
      if (FUN_F.equals(name)) {
        checkArgument(args.size() == 1);
        return getExpressionManager().applyExpr(f, args.get(0));
      }
      
      if (FUN_RF_AVOID.equals(name)) {
        checkArgument(args.size() == 3);
        return getExpressionManager().applyExpr(rf_avoid, args);
      }
      
      if (FUN_CYCLE.equals(name)) {
        checkArgument(args.size() == 1);
        return getExpressionManager().applyExpr(cycle, args.get(0));
      }
      
      if (FUN_JOIN.equals(name)) {
        checkArgument(args.size() == 2);
        return getExpressionManager().applyExpr(join, args);
      }

      /* Otherwise, pass through to the underlying bit-vector encoding */
      List<BitVectorExpression> newArgs = Lists
          .newArrayListWithCapacity(args.size());
      for (Expression e : args) {
        checkArgument(e.isBitVector());
        newArgs.add(e.asBitVector());
      }

      return super.functionCall(name, newArgs);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions() {
    return ImmutableSet.copyOf(Sets.union(rewrite_rules, super.getAssumptions()));
  }
  
  protected Expression applyF(Expression arg) {
    return getExpressionManager().applyExpr(f, arg);
  }

  protected BooleanExpression applyCycle(Expression arg) {
    return getExpressionManager().applyExpr(cycle, arg).asBooleanExpression();
  }
  
  protected BooleanExpression applyRfAvoid(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 3);
    return getExpressionManager().applyExpr(rf_avoid, argExprs).asBooleanExpression();
  }
  
  protected Expression applyJoin(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 2);
    return getExpressionManager().applyExpr(join, argExprs);
  }

  @Override
  public void instGen(Iterable<? extends Expression> gterms) {
    throw new UnsupportedOperationException("LoLLi with RR encoding doesn't support instGen.");   
  }

  @Override
  public Expression getEltExpr(Expression arg) {
    return arg;
  }
  
  @Override
  public BooleanExpression assignReach(String field, Expression arg1,
      Expression arg2) {
    return applyF(getEltExpr(arg1)).eq(getEltExpr(arg2));
  }

  @Override
  public void updateReach(String field, Expression arg1, Expression arg2) {
    throw new UnsupportedOperationException("LoLLi with RR encoding doesn't support updateReach.");   
  }

  @Override
  public BooleanExpression isRoot(String field, Expression rootExpr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression x_var = exprManager.boundVariable("x", eltType, true);
    rootExpr = getEltExpr(rootExpr);
    BooleanExpression res = exprManager.implies(rootExpr.neq(nil), 
        exprManager.forall(x_var, rootExpr.neq(applyF(x_var))));
    return res;
  }
  
  @Override
  public Type getEltType() {
    return eltType;
  }
  
  @Override
  public Expression getNil() {
    return nil;
  }

  @Override
  public BooleanExpression reach(String field, Expression arg1,
      Expression arg2, Expression arg3) {
    return applyRfAvoid(getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
}
