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

public class LoLLiwithQFReachEncoding extends LoLLiReachEncoding {

  public static LoLLiReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return LoLLiReachMemoryModel.create(encoding, size, size);
  }

  private final Type eltType;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private final FunctionType f;
  
  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf_avoid;
  
  /** The elt -> bool mapping */
  private final FunctionType cycle;
  
  /** The (elt, elt) -> elt mapping */
  private final FunctionType join;
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public LoLLiwithQFReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      
      eltType = wordType;
      
      /* Create function expression */
      
      nil = exprManager.bitVectorZero(eltType.asBitVectorType().getSize()); // nil = 0(NULL);
      f = exprManager.functionType(FUN_F, eltType, eltType);
      rf_avoid = exprManager.functionType(FUN_RF_AVOID, 
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType());
      cycle = exprManager.functionType(FUN_CYCLE, eltType, exprManager.booleanType());
      join = exprManager.functionType(FUN_JOIN, 
          ImmutableList.of(eltType, eltType), eltType);

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      
      int size = 5;
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
      Expression head, _let_0, body;
      ImmutableList<? extends Expression> triggers = null;
      BooleanExpression ruleExpr;
      
      /* Create a reflex rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, u
      /* Rf_avoid(x, x, u) */
      body = applyRfAvoid(xbounds[0], xbounds[0], xbounds[1]);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression reflex_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(reflex_rule); 
      
      /* Create a step rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, u
      _let_0 = applyF(xbounds[0]);
      /* Rf_avoid(x, f(x), u) || x = u */
      body = exprManager.or(applyRfAvoid(xbounds[0], _let_0, xbounds[1]),
          xbounds[0].eq(xbounds[1]));
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression step_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a selfLoop rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyF(xbounds[0]); // f(x)
      /* f(x) = x && Rf_avoid(x, y, y) => x = y */
      head = exprManager.and(_let_0.eq(xbounds[0]), 
          applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
      body = exprManager.eq(xbounds[0], xbounds[1]);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression selfLoop_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(selfLoop_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* Rf_avoid(x, y, x) => x = y */
      head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[0]);
      body = exprManager.eq(xbounds[0], xbounds[1]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression sandwich_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(sandwich_rule);
      
      /* Create a reach rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2]);    // u
      /* Rf_avoid(x, y, u) => Rf_avoid(x, y, y) */
      head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]);
      body = applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression reach_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a linear1 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2]);    // u
      /* Rf_avoid(x, y, y) => Rf_avoid(x, u, y) || Rf_avoid(x, y, u) */
      head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]);
      body = exprManager.or(applyRfAvoid(xbounds[0], xbounds[2], xbounds[1]),
          applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression line1_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(line1_rule);
      
      /* Create a linear2 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2],     // z
          xvars[3],     // u
          xvars[4]);    // v
      /* Rf_avoid(x, y, u) && Rf_avoid(x, z, v) => 
       * (Rf_avoid(x, z, u) && Rf_avoid(z, y, u)) || (Rf_avoid(x, y, v) && Rf_avoid(y, z, v))
       */
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]),
          applyRfAvoid(xbounds[0], xbounds[2], xbounds[4]));
      body = exprManager.or(
          exprManager.and(applyRfAvoid(xbounds[0], xbounds[2], xbounds[3]),
              applyRfAvoid(xbounds[2], xbounds[1], xbounds[3])), 
          exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[4]),
              applyRfAvoid(xbounds[1], xbounds[2], xbounds[4])));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression line2_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(line2_rule);      
      
      /* Create a transitive1 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2],     // z
          xvars[3]);    // u
      /* Rf_avoid(x, y, u) && Rf_avoid(y, z, u) => Rf(x, z, u)*/
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]), 
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[3]));
      body = applyRfAvoid(xbounds[0], xbounds[2], xbounds[3]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans1_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(trans1_rule);
      
      /* Create a transitive2 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2],     // z
          xvars[3]);    // u
      /* Rf_avoid(x, y, z) && Rf_avoid(y, u, z) && Rf_avoid(y, z, z) => Rf(x, y, u) */
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]), 
          applyRfAvoid(xbounds[1], xbounds[3], xbounds[2]),
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression trans2_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a join1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(x, join(x, y), join(x, y) */
      body = applyRfAvoid(xbounds[0], _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression join1_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(join1_rule);
      
      /* Create a join2 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2]);    // z
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(y, join(x, y), join(x, y))*/
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]),
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRfAvoid(xbounds[1], _let_0, _let_0);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression join2_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(join2_rule);
      
      /* Create a join3 rule */
      
      vars = ImmutableList.of(
          xvars[0],     // x
          xvars[1],     // y
          xvars[2]);    // z
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(x, join(x, y), z) */
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]), 
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      body = applyRfAvoid(xbounds[0], _let_0, xbounds[2]);
      triggers = ImmutableList.of(_let_0);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression join3_rule = exprManager.forall(vars, ruleExpr/* , triggers */);
      
      rewrite_rulesetBuilder.add(join3_rule);
      
      /* Create a join4 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(y, join(x, y) join(x, y)) || x = join(x, y) */
      body = exprManager.or(applyRfAvoid(xbounds[1], _let_0, _let_0),
          _let_0.eq(xbounds[0]));
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression join4_rule = exprManager.forall(vars, ruleExpr/*, triggers */);
      
      rewrite_rulesetBuilder.add(join4_rule);
      
      /* Create a cycle1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* Rf_avoid(x, y, y) && Rf_avoid(y, x, x) => cycle(x) || x = y */
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]),
          applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
      body = exprManager.and(applyCycle(xbounds[0]), xbounds[0].eq(xbounds[1]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression cycle1_rule = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(cycle1_rule);
      
      /* Create a cycle2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* cycle(x) && Rf_avoid(x, y, y) => Rf_avoid(y, x, x) */
      head = exprManager.and(applyCycle(xvars[0]), 
          applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
      body = applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]);
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression cycle2_rule = exprManager.forall(vars, ruleExpr);
      
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
        return f.apply(args.get(0));
      }
      
      if (FUN_RF_AVOID.equals(name)) {
        checkArgument(args.size() == 3);
        return rf_avoid.apply(args);
      }
      
      if (FUN_CYCLE.equals(name)) {
        checkArgument(args.size() == 1);
        return cycle.apply(args.get(0));
      }
      
      if (FUN_JOIN.equals(name)) {
        checkArgument(args.size() == 2);
        return join.apply(args);
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

  public Type getEltType() {
    return eltType;
  }

  public Expression getNil() {
    return nil;
  }
}
