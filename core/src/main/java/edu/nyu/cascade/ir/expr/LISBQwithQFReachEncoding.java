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
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public class LISBQwithQFReachEncoding extends LISBQReachEncoding {
  
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
  private final FunctionType f;

  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf;
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public LISBQwithQFReachEncoding(ExpressionManager exprManager) {
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

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      int size = 4;
      VariableExpression[] xvars = new VariableExpression[size];
      Expression[] xbounds = new Expression[size];
      
      for(int i = 0; i < size; i++) {
        xvars[i] = exprManager.variable("x"+ i, eltType, true);
        xbounds[i] = exprManager.boundExpression(i, eltType);
      }
      
      /* Create a f(null)=null assumption */
      
      BooleanExpression nil_assumption = applyF(nil).eq(nil);
      
      rewrite_rulesetBuilder.add(nil_assumption);
      
      ImmutableList<? extends VariableExpression> vars;
      ImmutableList<? extends Expression> triggers;
      Expression _let_0;
      BooleanExpression head, body;
      
      /* Create a reflexive rule */
      vars = ImmutableList.of(xvars[0]);
      body = applyRf(xbounds[0], xbounds[0], xbounds[0]);
      triggers = ImmutableList.of(applyF(xbounds[0]));
      BooleanExpression reflex_rule = exprManager.forall(vars, body, triggers);
      
//      rewrite_rulesetBuilder.add(reflex_rule);
            
      /* Create a step rule */
      
      vars = ImmutableList.of(xvars[0]);   
      _let_0 = applyF(xbounds[0]);
      body = applyRf(xbounds[0], _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      BooleanExpression step_rule = exprManager.forall(vars, body, triggers);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]);
      
      head = applyRf(xbounds[0], xbounds[1], xbounds[1]);
      body = exprManager.or(exprManager.eq(xbounds[0], xbounds[1]), 
          applyRf(xbounds[0], applyF(xbounds[0]), xbounds[1]));
      triggers = ImmutableList.of(
          applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyF(xbounds[0]));
      BooleanExpression reach_rule = exprManager.forall(vars, head.implies(body), triggers);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a cycle rule */

      vars = ImmutableList.of(xvars[0], xvars[1]);
      
      head = applyRf(xbounds[0], xbounds[1], xbounds[1]).
          and(exprManager.eq(applyF(xbounds[0]), xbounds[0]));
      body = exprManager.eq(xbounds[0], xbounds[1]);
      triggers = ImmutableList.of(
          applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyF(xbounds[0]));
      BooleanExpression cycle_rule = exprManager.forall(vars, head.implies(body), triggers);
      
      rewrite_rulesetBuilder.add(cycle_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]);
      
      head = applyRf(xbounds[0], xbounds[1], xbounds[0]);
      body = exprManager.eq(xbounds[0], xbounds[1]);
      BooleanExpression sandwich_rule = exprManager.forall(vars, head.implies(body));
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create an order1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);
      
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[0], xbounds[2], xbounds[2]));
      body = exprManager.or(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[0], xbounds[2], xbounds[1]));
      BooleanExpression order1_rule = exprManager.forall(vars, head.implies(body));
      
      rewrite_rulesetBuilder.add(order1_rule);
      
      /* Create an order2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);
      
      head = applyRf(xbounds[0], xbounds[1], xbounds[2]);
      body = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      BooleanExpression order2_rule = exprManager.forall(vars, head.implies(body));
      
      rewrite_rulesetBuilder.add(order2_rule);
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]); 
      
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[1]), 
          applyRf(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRf(xbounds[0], xbounds[2], xbounds[2]);
      BooleanExpression trans1_rule = exprManager.forall(vars, head.implies(body));
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);
      
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[1], xbounds[3], xbounds[2]));
      body = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[3]), 
          applyRf(xbounds[0], xbounds[3], xbounds[2]));
      BooleanExpression trans2_rule = exprManager.forall(vars, head.implies(body));
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a transitive3 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);
      
      head = exprManager.and(applyRf(xbounds[0], xbounds[1], xbounds[2]), 
          applyRf(xbounds[0], xbounds[3], xbounds[1]));
      body = exprManager.and(applyRf(xbounds[0], xbounds[3], xbounds[2]), 
          applyRf(xbounds[3], xbounds[1], xbounds[2]));
      BooleanExpression trans3_rule = exprManager.forall(vars, head.implies(body));
      
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
        return f.apply(args.get(0));
      }

      if (FUN_RF.equals(name)) {
        checkArgument(args.size() == 3);
        return rf.apply(args);
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
