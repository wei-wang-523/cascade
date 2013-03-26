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
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public class LISBQExdReachEncoding extends ReachEncoding {

  private static final String FUN_R = "r";
  
  public static LISBQExdReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return LISBQExdReachMemoryModel.create(encoding, size, size);
  }

  private final Type eltType, memType;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;

  /** The (mem, elt, elt, elt) -> bool mapping */
  private final FunctionType r;
  
  public LISBQExdReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      
      eltType = wordType;
      
      memType = exprManager.arrayType(eltType, eltType);
      
      /* Create function expression */
      
      nil = exprManager.bitVectorZero(eltType.asBitVectorType().getSize()); // nil = 0(NULL);
      r = exprManager.functionType(FUN_R, 
          ImmutableList.of(memType, eltType, eltType, eltType), 
          exprManager.booleanType());

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      
      int size = 5;
      VariableExpression[] xvars = new VariableExpression[size];
      Expression[] xbounds = new Expression[size];
      
      for(int i = 0; i < size; i++) {
        if(i==0) {
          xvars[i] = exprManager.variable("x"+ i, memType, true);
          xbounds[i] = exprManager.boundExpression(i, memType);
        } else {
          xvars[i] = exprManager.variable("x"+ i, eltType, true);
          xbounds[i] = exprManager.boundExpression(i, eltType);
        }
      }
      
      ImmutableList<VariableExpression> vars = null;
      ImmutableList<Expression> triggers = null;
      Expression head, body;
      BooleanExpression guard;
      BooleanExpression ruleExpr;
      
      /* Create a reflexive rule */
      vars = ImmutableList.of(xvars[0], xvars[1]);
      body = applyR(xvars[0], xvars[1], xvars[1], xvars[1]);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression reflex_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(reflex_rule);
            
      /* Create a step rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]);      
      Expression _let_0 = xvars[0].asArray().index(xvars[1]);
      body = applyR(xvars[0], xvars[1], _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression step_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);
      head = applyR(xvars[0], xvars[1], xvars[2], xvars[2]);
      _let_0 = xvars[0].asArray().index(xvars[1]);
      body = exprManager.or(exprManager.eq(xvars[1], xvars[2]), 
          applyR(xvars[0], xvars[1], _let_0, xvars[2]));
      triggers = ImmutableList.of(applyR(xvars[0], xvars[1], xvars[2], xvars[2]),
          _let_0);
      ruleExpr = exprManager.rrDeduction(head, body);
      BooleanExpression reach_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a cycle rule */

      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);
      _let_0 = xvars[0].asArray().index(xvars[1]);
      guard = exprManager.eq(_let_0, xvars[1]);      
      head = applyR(xvars[0], xvars[1], xvars[2], xvars[2]);
      body = exprManager.eq(xvars[1], xvars[2]);
      triggers = ImmutableList.of(
          applyR(xvars[0], xvars[1], xvars[2], xvars[2]), 
          _let_0);
      ruleExpr = exprManager.implies(exprManager.and(head, guard), body);
      BooleanExpression cycle_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(cycle_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2]);
      head = applyR(xvars[0], xvars[1], xvars[2], xvars[1]);
      body = exprManager.eq(xvars[1], xvars[2]);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression sandwich_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create an order1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);
      head = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[2]), 
          applyR(xvars[0], xvars[1], xvars[3], xvars[3]));
      body = exprManager.or(applyR(xvars[0], xvars[1], xvars[2], xvars[3]), 
          applyR(xvars[0], xvars[1], xvars[3], xvars[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression order1_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(order1_rule);
      
      /* Create an order2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]);   
      head = applyR(xvars[0], xvars[1], xvars[2], xvars[3]);
      body = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[2]), 
          applyR(xvars[0], xvars[2], xvars[3], xvars[3]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression order2_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(order2_rule);
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3]); 
      head = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[2]), 
          applyR(xvars[0], xvars[2], xvars[3], xvars[3]));
      body = applyR(xvars[0], xvars[1], xvars[3], xvars[3]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans1_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3], xvars[4]);    
      head = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[3]), 
          applyR(xvars[0], xvars[2], xvars[4], xvars[3]));
      body = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[4]), 
          applyR(xvars[0], xvars[1], xvars[4], xvars[3]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans2_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a transitive3 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1], xvars[2], xvars[3], xvars[4]);
      head = exprManager.and(applyR(xvars[0], xvars[1], xvars[2], xvars[3]), 
          applyR(xvars[0], xvars[1], xvars[4], xvars[2]));
      body = exprManager.and(applyR(xvars[0], xvars[1], xvars[4], xvars[3]), 
          applyR(xvars[0], xvars[4], xvars[2], xvars[3]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans3_rule = exprManager.forall(vars, ruleExpr);
      
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
      if (FUN_R.equals(name)) {
        checkArgument(args.size() == 4);
        return r.apply(args);
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

  private BooleanExpression applyR(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 4);
    return getExpressionManager().applyExpr(r, argExprs).asBooleanExpression();
  }
  
  private BooleanExpression applyR(VariableExpression... args) {
    ImmutableList<VariableExpression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 4);
    return getExpressionManager().applyExpr(r, argExprs).asBooleanExpression();
  }

  @Override
  public Expression getEltExpr(Expression arg) {
    return arg;
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
  public void instGen(Iterable<? extends Expression> heapRegions) {
    throw new UnsupportedOperationException("LISBQ extend encoding doesn't support instGen.");
  }
}
