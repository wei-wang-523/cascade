package edu.nyu.cascade.ir.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public class LISBQwithQFReachEncoding extends ReachEncoding {
  
  public static ReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return ReachMemoryModel.create(encoding, size, size);
  }
  
  private ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private final FunctionType f;

  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf;
  
  /** Constructor and Selector for the elt type*/
  
  private final Type eltType;
  
  private final Constructor consConstr;
  
  private final Selector nextSel;
  
  private final Map<Expression, Expression> boundVarMap;
  
  public LISBQwithQFReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      nextSel = exprManager.selector(NEXT_SELECTOR_NAME, wordType);
      consConstr = exprManager.constructor(ELT_F_CONST, nextSel);
      eltType = exprManager.dataType(ELT_DATATYPE, consConstr);
      
      /* Create function expression */
      
      nil = getEltExpr(exprManager.bitVectorZero(DEFAULT_WORD_SIZE));
      f = exprManager.functionType(FUN_F, eltType, eltType);
      rf = exprManager.functionType(FUN_RF, 
          ImmutableList.of(eltType, eltType, eltType), 
          exprManager.booleanType());

      /* Create data constraints */
      
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      /* Create bound vars */
      boundVarMap = Maps.newHashMap();
      int size = 4;
      VariableExpression[] xvars = new VariableExpression[size];
      Expression[] xbounds = new Expression[size];
      
      for(int i = 0; i < size; i++) {
        xvars[i] = exprManager.variable("x"+ i, eltType, false);
        xbounds[i] = exprManager.boundExpression(i, eltType);
        boundVarMap.put(xbounds[i], xvars[i]);
      }
      
      /* Create a f(null)=null assumption */
      
      BooleanExpression nil_assumption = applyF(nil).eq(nil);
      
      rewrite_rulesetBuilder.add(nil_assumption);
      
      ImmutableList<? extends VariableExpression> vars;
      ImmutableList<? extends Expression> triggers;
      Expression _let_0;
      BooleanExpression head, body;
      
      /* Create a reflexive rule */
//      vars = ImmutableList.of(xvars[0]);
//      body = applyRf(xbounds[0], xbounds[0], xbounds[0]);
//      triggers = ImmutableList.of(applyF(xbounds[0]));
//      BooleanExpression reflex_rule = exprManager.forall(vars, body, triggers);
      
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
      
      head = applyRf(xbounds[1], xbounds[0], xbounds[0]);
      body = exprManager.or(exprManager.eq(xbounds[1], xbounds[0]), 
          applyRf(xbounds[1], applyF(xbounds[1]), xbounds[0]));
      triggers = ImmutableList.of(
          applyRf(xbounds[1], xbounds[0], xbounds[0]), 
          applyF(xbounds[1]));
      BooleanExpression reach_rule = exprManager.forall(vars, head.implies(body), triggers);
      
      rewrite_rulesetBuilder.add(reach_rule);
      
      /* Create a cycle rule */

      vars = ImmutableList.of(xvars[0], xvars[1]);
      
      head = applyRf(xbounds[1], xbounds[0], xbounds[0]).
          and(exprManager.eq(applyF(xbounds[1]), xbounds[1]));
      body = exprManager.eq(xbounds[1], xbounds[0]);
      triggers = ImmutableList.of(
          applyRf(xbounds[1], xbounds[0], xbounds[0]), 
          applyF(xbounds[1]));
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
  
  private Expression applyF(Expression arg) {
    return getExpressionManager().applyExpr(f, arg);
  }

  private BooleanExpression applyRf(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.copyOf(Arrays.asList(args));
    Preconditions.checkArgument(argExprs.size() == 3);
    return getExpressionManager().applyExpr(rf, argExprs).asBooleanExpression();
  }

  /**
   * Check if <code>expr</code> contains applyF sub-expression.
   */
  private ImmutableSet<? extends Expression> checkApplyF(Expression expr) {
    ImmutableSet.Builder<Expression> instCand_builder = ImmutableSet.builder();
    
    if(expr.getArity() == 0)    return instCand_builder.build();   
    if(expr.getKind().equals(Kind.APPLY)) 
      if(f.equals(expr.getFuncDecl()))
        return instCand_builder.add(expr.getChild(0)).build();
  
    for(Expression child : expr.getChildren())
      instCand_builder.addAll(checkApplyF(child));
    
    return instCand_builder.build();
  }
  
  /**
   * Collect instantiation <code>ground_terms</code> set with given <code>size</code>
   */
  private List<ImmutableList<Expression>> collectInstTerms(int size, 
      Iterable<? extends Expression> ground_terms) {
    List<ImmutableList<Expression>> res = Lists.newLinkedList();
    if(size == 1) {
      for(Expression term : ground_terms)   res.add(ImmutableList.of(term));
    } else {
      List<ImmutableList<Expression>> prev_res = collectInstTerms(size-1, ground_terms);
      for(ImmutableList<Expression> prev_list : prev_res) {
        for(Expression term : ground_terms) {
          ImmutableList.Builder<Expression> curr_list_buider = ImmutableList.builder();         
          res.add(curr_list_buider.add(term).addAll(prev_list).build());
        }
      }
    }
    return res;
  }
  
  /**
   * Instantiate the <code>bound_vars</code> to <code>ground_terms</code> in <code>expr</code>
   */
  private ImmutableList<? extends Expression> instantiate(Expression expr, 
      Iterable<? extends Expression> bound_vars, 
      Iterable<? extends Expression> ground_terms) {
    ImmutableList.Builder<Expression> builder = ImmutableList.builder();
    List<ImmutableList<Expression>> inst_terms_list = collectInstTerms(
        Iterables.size(bound_vars), ground_terms);
    for(ImmutableList<Expression> instTerms : inst_terms_list)
      builder.add(expr.subst(bound_vars, instTerms));
    return builder.build();
  }
  
  /**
   * Instantiate partially bound variables in rewrite rules with <code>heapRegions</code>
   */
  @Override
  public void instGen(Iterable<? extends Expression> heapRegions) {
    ImmutableList.Builder<Expression> builder = ImmutableList.builder();
    for(Expression region : heapRegions)
      builder.add(getEltExpr(region));
    
    builder.add(nil);
    ImmutableList<Expression> gterms = builder.build();
    
    ImmutableSet.Builder<BooleanExpression> inst_rulesetBuilder = ImmutableSet
        .builder();
    for(BooleanExpression rule : rewrite_rules) {
      BooleanExpression body = rule.getBody();
      if(body != null) {
        ImmutableSet<? extends Expression> instCand = null;
        if(Preferences.isSet(Preferences.OPTION_PARTIAL_INST)) {          
          instCand = checkApplyF(body); // check if body contains applyF(x)
        } else { // TOTOALLY_INST
          ImmutableSet.Builder<Expression> instCand_builder = ImmutableSet.builder();
          for(Expression key : boundVarMap.keySet()) {
            Expression var = boundVarMap.get(key);
            if(rule.getBoundVars().contains(var) && key.getType().equals(eltType))  
              instCand_builder.add(key);
          }
          instCand = instCand_builder.build();
        }
        if(!instCand.isEmpty()) {
          ImmutableList<? extends Expression> instBodyList = instantiate(body, instCand, gterms);
            
          List<? extends Expression> boundVars = Lists.newArrayList(rule.getBoundVars());
          for(Expression cand : instCand)   boundVars.remove(boundVarMap.get(cand));
          
          /* List<Iterable<? extends Expression>> instTriggerList = Lists.newArrayList();
            Iterable<? extends Expression> triggers = rule.getTriggers().get(0); 
            for(Expression trigger : triggers){
              List<? extends Expression> instTrigger = instantiate(trigger, instCand, gterms);
              instTriggerList.add(instTrigger);
            }          
            Iterator<Iterable<? extends Expression>> iter = instTriggerList.iterator();
           */
          for(Expression instBody : instBodyList) {
            BooleanExpression inst_rule = boundVars.isEmpty() ? instBody.asBooleanExpression() :
              getExpressionManager().forall(boundVars, instBody/*, iter.next()*/);
            inst_rulesetBuilder.add(inst_rule);
          }
          continue;
        }
      }
      inst_rulesetBuilder.add(rule); 
    }
    rewrite_rules = ImmutableSet.copyOf(inst_rulesetBuilder.build());
  }
  
  @Override
  public Expression getEltExpr(Expression arg) {
    Preconditions.checkArgument(arg.getType().
        equals(getExpressionManager().bitVectorType(DEFAULT_WORD_SIZE)));
    return consConstr.apply(arg);
  }

  @Override
  public BooleanExpression assignReach(String field, Expression arg1,
      Expression arg2) {
    return applyF(getEltExpr(arg1)).eq(getEltExpr(arg2));
  }

  @Override
  public void updateReach(String field, Expression arg1, Expression arg2) {
    throw new UnsupportedOperationException("update reach is not supported in LISBQwithQF.");
  }

  @Override
  public BooleanExpression isRoot(String field, Expression rootExpr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression x_var = exprManager.variable("x", eltType, true);
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
    return applyRf(getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
}
