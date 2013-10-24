package edu.nyu.cascade.ir.expr.bak;

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
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public class LoLLiwithQFReachEncoding extends ReachEncoding {

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
  private final FunctionType rf_avoid;
  
  /** The elt -> bool mapping */
  private final FunctionType cycle;
  
  /** The (elt, elt) -> elt mapping */
  private final FunctionType join;
  
  private final Type eltType;
  
  private final Constructor consConstr;
  
  private final Selector nextSel;
  
  private final Map<Expression, Expression> boundVarMap;
  
  public LoLLiwithQFReachEncoding(ExpressionManager exprManager) {
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
      boundVarMap = Maps.newHashMap();
      int size = 5;
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
      
      ImmutableList<? extends VariableExpression> vars = null;   
      Expression head, _let_0, body;
      ImmutableList<? extends Expression> triggers = null;
      BooleanExpression ruleExpr;
      
      /* Create a reflex rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, u
      /* Rf_avoid(x, x, u) */
      body = applyRfAvoid(xbounds[1], xbounds[1], xbounds[0]);
      ruleExpr = body.asBooleanExpression();
      triggers = ImmutableList.of(body);
      BooleanExpression reflex_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(reflex_rule); 
      
      /* Create a step rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, u
      _let_0 = applyF(xbounds[1]);
      /* Rf_avoid(x, f(x), u) || x = u */
      body = exprManager.or(applyRfAvoid(xbounds[1], _let_0, xbounds[0]),
          xbounds[1].eq(xbounds[0]));
      triggers = ImmutableList.of(applyRfAvoid(xbounds[1], _let_0, xbounds[0]));
      ruleExpr = body.asBooleanExpression();
      BooleanExpression step_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(step_rule); 
      
      /* Create a selfLoop rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyF(xbounds[1]); // f(x)
      /* f(x) = x && Rf_avoid(x, y, y) => x = y */
      head = exprManager.and(_let_0.eq(xbounds[1]), 
          applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
      body = exprManager.eq(xbounds[1], xbounds[0]);
      triggers = ImmutableList.of(_let_0, applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression selfLoop_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(selfLoop_rule);
      
      /* Create a sandwich rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* Rf_avoid(x, y, x) => x = y */
      head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[0]);
      body = exprManager.eq(xbounds[0], xbounds[1]);
      ruleExpr = exprManager.implies(head, body);
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[0]));
      BooleanExpression sandwich_rule = exprManager.forall(vars, ruleExpr, triggers);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]));
      BooleanExpression reach_rule = exprManager.forall(vars, ruleExpr/*, triggers*/);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
      BooleanExpression line1_rule = exprManager.forall(vars, ruleExpr/*, triggers*/);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]),
          applyRfAvoid(xbounds[0], xbounds[2], xbounds[4]));
      BooleanExpression line2_rule = exprManager.forall(vars, ruleExpr/*, triggers*/);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]), 
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[3]));
      BooleanExpression trans1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]), 
          applyRfAvoid(xbounds[1], xbounds[3], xbounds[2]),
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      BooleanExpression trans2_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(trans2_rule);
      
      /* Create a join1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(x, join(x, y), join(x, y) */
      body = applyRfAvoid(xbounds[0], _let_0, _let_0);
      ruleExpr = body.asBooleanExpression();
      triggers = ImmutableList.of(body);
      BooleanExpression join1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]),
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression join2_rule = exprManager.forall(vars, ruleExpr, triggers);
      
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
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]), 
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
      ruleExpr = exprManager.implies(head, body);
      BooleanExpression join3_rule = exprManager.forall(vars, ruleExpr, triggers );
      
      rewrite_rulesetBuilder.add(join3_rule);
      
      /* Create a join4 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      _let_0 = applyJoin(xbounds[0], xbounds[1]);
      /* Rf_avoid(y, join(x, y) join(x, y)) || x = join(x, y) */
      body = exprManager.or(applyRfAvoid(xbounds[1], _let_0, _let_0),
          _let_0.eq(xbounds[0]));
      triggers = ImmutableList.of(_let_0);
      ruleExpr = body.asBooleanExpression();
      BooleanExpression join4_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(join4_rule);
      
      /* Create a cycle1 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* Rf_avoid(x, y, y) && Rf_avoid(y, x, x) => cycle(x) || x = y */
      head = exprManager.and(applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]),
          applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
      body = exprManager.or(applyCycle(xbounds[0]), xbounds[0].eq(xbounds[1]));
      ruleExpr = exprManager.implies(head, body);
      triggers = ImmutableList.of(applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]),
          applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
      BooleanExpression cycle1_rule = exprManager.forall(vars, ruleExpr, triggers);
      
      rewrite_rulesetBuilder.add(cycle1_rule);
      
      /* Create a cycle2 rule */
      
      vars = ImmutableList.of(xvars[0], xvars[1]); // x, y
      /* cycle(x) && Rf_avoid(x, y, y) => Rf_avoid(y, x, x) */
      head = exprManager.and(applyCycle(xvars[0]), 
          applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
      body = applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]);
      ruleExpr = exprManager.implies(head, body);
      triggers = ImmutableList.of(applyCycle(xvars[0]), 
          applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
      BooleanExpression cycle2_rule = exprManager.forall(vars, ruleExpr, triggers);
      
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
    ImmutableList<Expression> argExprs = ImmutableList.copyOf(Arrays.asList(args));
    Preconditions.checkArgument(argExprs.size() == 3);
    return getExpressionManager().applyExpr(rf_avoid, argExprs).asBooleanExpression();
  }
  
  protected Expression applyJoin(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.copyOf(Arrays.asList(args));
    Preconditions.checkArgument(argExprs.size() == 2);
    return getExpressionManager().applyExpr(join, argExprs);
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
   * Instantiate partially bound variables in rewrite rules with <code>gterms</code>
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
    return consConstr.apply(arg);
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
  public BooleanExpression assignReach(String field, Expression arg1,
      Expression arg2) {
    return applyF(getEltExpr(arg1)).eq(getEltExpr(arg2));
  }

  @Override
  public void updateReach(String field, Expression arg1, Expression arg2) {
    throw new UnsupportedOperationException("LoLLi with QF encoding doesn't support updateReach.");   
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
  public BooleanExpression reach(String field, Expression arg1,
      Expression arg2, Expression arg3) {
    return applyRfAvoid(getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
}
