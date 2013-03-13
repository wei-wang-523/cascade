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
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class JoinwithQFReachEncoding extends JoinReachEncoding {

  public static JoinReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return JoinReachMemoryModel.create(encoding, size, size);
  }

  private final Type eltType;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private final FunctionType f;

  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf;
  
  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf_avoid;
  
  /** The (elt, elt) -> elt mapping */
  private final FunctionType join;
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public JoinwithQFReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      
      eltType = wordType;
      
      /* Create function expression */
      
      nil = exprManager.bitVectorZero(eltType.asBitVectorType().getSize()); // nil = 0(NULL);
      f = exprManager.functionType(FUN_F, eltType, eltType);
      rf = exprManager.functionType(FUN_RF, 
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType());
      rf_avoid = exprManager.functionType(FUN_RF_AVOID, 
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType());
      join = exprManager.functionType(FUN_JOIN, 
          ImmutableList.of(eltType, eltType), eltType);

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      
      int size = 4;
      VariableExpression[] xvars = new VariableExpression[size];
      Expression[] xbounds = new Expression[size];
      
      for(int i = 0; i < size; i++) {
        xvars[i] = exprManager.variable("x"+ i, eltType, false);
        xbounds[i] = exprManager.boundExpression(i, eltType);
      }
      
      /* Create a f(null)=null assumption */
      
      BooleanExpression nil_assumption = applyF(nil).eq(nil);
      
      rewrite_rulesetBuilder.add(nil_assumption);
      
      ImmutableList<? extends VariableExpression> vars = null;      
      BooleanExpression guard;      
      Expression head, _let_0, body;
      ImmutableList<? extends Expression> triggers = null;
      BooleanExpression ruleExpr;
      
      /* Create a step rule */
      
      vars = ImmutableList.of(xvars[0]);
      _let_0 = applyF(xbounds[0]);
      body = applyRf(xbounds[0], _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression step_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]);
      head = applyRf(xbounds[0], xbounds[1], xbounds[1]);
      body = exprManager.or(exprManager.eq(xbounds[0], xbounds[1]), 
          applyRf(xbounds[0], applyF(xbounds[0]), xbounds[1]));
      triggers = ImmutableList.of(
          applyRf(xbounds[0], xbounds[1], xbounds[1]),
          applyF(xbounds[0]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression reach_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a cycle rule */

      vars = ImmutableList.of(xvars[0], xvars[1]);
      guard = exprManager.eq(applyF(xbounds[0]), xbounds[0]);      
      head = applyRf(xbounds[0], xbounds[1], xbounds[1]);
      body = exprManager.eq(xbounds[0], xbounds[1]);
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[1]));
      ruleExpr = exprManager.implies(exprManager.and(head, guard), body);
      BooleanExpression cycle_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(cycle_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]);      
      head = applyRf(xbounds[0], xbounds[1], xbounds[0]);
      body = exprManager.eq(xbounds[0], xbounds[1]);
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[0]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression sandwich_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create an order1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);     
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[0], xbounds[2], xbounds[2]));
      body = exprManager.or(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[0], xbounds[2], xbounds[1]));
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[0], xbounds[2], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression order1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(order1_rule);
      
      /* Create an order2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);    
      head = applyRf(xbounds[0], xbounds[1], xbounds[2]);
      body = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression order2_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(order2_rule);
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);     
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRf(xbounds[0], xbounds[2], xbounds[2]);
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);   
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[1], xbounds[3], xbounds[2]));
      body = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[3]), 
          applyRf(xbounds[0], xbounds[3], xbounds[2]));
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[1], xbounds[3], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans2_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a transitive3 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);     
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[0], xbounds[3], xbounds[1]));
      body = exprManager.and(applyRf(xbounds[0], xbounds[3], xbounds[2]), 
          applyRf(xbounds[3], xbounds[1], xbounds[2]));
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[0], xbounds[3], xbounds[1]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans3_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(trans3_rule);
      
      /* Create a rf_avoid rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);    
      head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]);
      body = exprManager.or(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
              exprManager.not(applyRf(xbounds[0], xbounds[2], xbounds[2]))));
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression rf_avoid_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(rf_avoid_rule);
      
      /* Create a join1 rule */
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);    
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      head = exprManager.and(applyRf(xbounds[0], xbounds[2], xbounds[2]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRf(xbounds[0], _let_0, xbounds[2]);
      triggers = ImmutableList.of(applyRf(xbounds[0], xbounds[2], xbounds[2]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression join1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(join1_rule);
      
      /* Create a join2 rule */
      vars = ImmutableList.of(xvars[0], xvars[1]);      
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      body = exprManager.or(
          exprManager.and(applyRf(xbounds[0], _let_0, _let_0), applyRf(xbounds[1], _let_0, _let_0)),
          _let_0.eq(nil)
          );
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression join2_rule = exprManager.forall(vars, ruleExpr/*, triggers */);
      
      rewrite_rulesetBuilder.add(join2_rule);
      
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
        return f.apply(args.get(0));
      }

      if (FUN_RF.equals(name)) {
        checkArgument(args.size() == 3);
        return rf.apply(args);
      }
      
      if (FUN_RF_AVOID.equals(name)) {
        checkArgument(args.size() == 3);
        return rf_avoid.apply(args);
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

  public Type getEltType() {
    return eltType;
  }

  public Expression getNil() {
    return nil;
  }
}
