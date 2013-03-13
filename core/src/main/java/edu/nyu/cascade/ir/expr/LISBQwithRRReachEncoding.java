package edu.nyu.cascade.ir.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.LISBQReachMemoryModel;
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

public class LISBQwithRRReachEncoding extends LISBQReachEncoding {
  
  public static LISBQReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return LISBQReachMemoryModel.create(encoding, size, size);
  }

  private final Type eltType;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private final Expression f;

  /** The (elt, elt, elt) -> bool mapping */
  private final Expression rf;
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public LISBQwithRRReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      
      eltType = wordType;
      
      /* Create function expression */
      
      nil = exprManager.bitVectorZero(eltType.asBitVectorType().getSize()); // nil = 0(NULL);
      f = exprManager.functionVar(FUN_F, exprManager.functionType(FUN_F, eltType, eltType), false);
      rf = exprManager.functionVar(FUN_RF, exprManager.functionType(FUN_RF,
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType()), false);

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      
      VariableExpression x = eltType.boundVariable("x", true);
      VariableExpression x0 = eltType.boundVariable("x0", true);
      VariableExpression x1 = eltType.boundVariable("x1", true);
      VariableExpression x2 = eltType.boundVariable("x2", true); 
      VariableExpression x3 = eltType.boundVariable("x3", true);
      
      /* Create a f(null)=null assumption */
      
      BooleanExpression nil_assumption = applyF(nil).eq(nil);
      
      rewrite_rulesetBuilder.add(nil_assumption);
            
      /* Create a step rule */
      
      ImmutableList<VariableExpression> vars = ImmutableList.of(x);      
      BooleanExpression guard = exprManager.tt();      
      Expression head = exprManager.tt();
      Expression _let_0 = applyF(x);
      Expression body = applyRf(x, _let_0, _let_0);
      ImmutableList<Expression> triggers = ImmutableList.of(_let_0);
      BooleanExpression rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression step_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(x1, x2);
      guard = exprManager.tt();
      head = applyRf(x1, x2, x2);
      body = exprManager.or(exprManager.eq(x1, x2), applyRf(x1, applyF(x1), x2));
      triggers = ImmutableList.of(applyF(x1));
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression reach_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a cycle rule */

      vars = ImmutableList.of(x1, x2);
      guard = exprManager.eq(applyF(x1), x1);      
      head = applyRf(x1, x2, x2);
      body = exprManager.eq(x1, x2);
      triggers = ImmutableList.of(applyF(x1));
      rrDeductionExpr = exprManager.rrDeduction(head, body, triggers);
      BooleanExpression cycle_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(cycle_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(x1, x2);
      guard = exprManager.tt();      
      head = applyRf(x1, x2, x1);
      body = exprManager.eq(x1, x2);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression sandwich_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create an order1 rule */
      
      vars = ImmutableList.of(x1, x2, x3);
      guard = exprManager.tt();      
      head = exprManager.and(applyRf(x1, x2, x2), applyRf(x1, x3, x3));
      body = exprManager.or(applyRf(x1, x2, x3), applyRf(x1, x3, x2));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression order1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(order1_rule);
      
      /* Create an order2 rule */
      
      vars = ImmutableList.of(x1, x2, x3);
      guard = exprManager.tt();      
      head = applyRf(x1, x2, x3);
      body = exprManager.and(applyRf(x1, x2, x2), applyRf(x2, x3, x3));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression order2_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(order2_rule);
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(x1, x2, x3); 
      guard = exprManager.tt();
      head = exprManager.and(applyRf(x1, x2, x2), applyRf(x2, x3, x3));
      body = applyRf(x1, x3, x3);
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression trans1_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(x0, x1, x2, x3);
      guard = exprManager.tt();      
      head = exprManager.and(applyRf(x0, x1, x2), applyRf(x1, x3, x2));
      body = exprManager.and(applyRf(x0, x1, x3), applyRf(x0, x3, x2));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression trans2_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a transitive3 rule */
      
      vars = ImmutableList.of(x0, x1, x2, x3);
      guard = exprManager.tt();      
      head = exprManager.and(applyRf(x0, x1, x2), applyRf(x0, x3, x1));
      body = exprManager.and(applyRf(x0, x3, x2), applyRf(x3, x1, x2));
      rrDeductionExpr = exprManager.rrDeduction(head, body);
      BooleanExpression trans3_rule = exprManager.rewriteRule(vars, guard, rrDeductionExpr);
      
      rewrite_rulesetBuilder.add(trans3_rule);
      
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

      if (FUN_RF.equals(name)) {
        checkArgument(args.size() == 3);
        return getExpressionManager().applyExpr(rf, args);
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

  protected BooleanExpression applyRf(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 3);
    return getExpressionManager().applyExpr(rf, argExprs).asBooleanExpression();
  }

  public Type getEltType() {
    return eltType;
  }

  public Expression getNil() {
    return nil;
  }
}
