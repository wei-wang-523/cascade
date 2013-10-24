package edu.nyu.cascade.ir.expr.bak;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Axiom;
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

public class LoLLiwithQFArrReachEncoding extends ReachEncoding {
  
  public static ReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return ReachMemoryModel.create(encoding, size, size);
  }
  
  private ImmutableSet<Axiom> rewrite_axioms;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The elt -> elt mapping */
  private ArrayExpression f;
  
  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf_avoid;
  
  /** The elt -> bool mapping */
  private final FunctionType cycle;
  
  /** The (elt, elt) -> elt mapping */
  private final FunctionType join;
  
  /** Constructor and Selector for the elt type*/
  
  private final Type eltType;
  
  private final Constructor consConstr;
  
  private final Selector nextSel;
  
  public LoLLiwithQFArrReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);

      /* Create datatype */
      nextSel = exprManager.selector(NEXT_SELECTOR_NAME, wordType);
      consConstr = exprManager.constructor(ELT_F_CONST, nextSel);
      eltType = exprManager.dataType(ELT_DATATYPE, consConstr);
      
      /* Create function expression */
      
      nil = getEltExpr(exprManager.bitVectorZero(DEFAULT_WORD_SIZE));
      f = exprManager.arrayVar(FUN_F, eltType, eltType, true);
      rf_avoid = exprManager.functionType(FUN_RF_AVOID, 
          Arrays.asList(eltType, eltType, eltType), 
          exprManager.booleanType());
      cycle = exprManager.functionType(FUN_CYCLE, eltType, exprManager.booleanType());
      join = exprManager.functionType(FUN_JOIN, 
          Arrays.asList(eltType, eltType), eltType);
      
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
        return f.index(args.get(0));
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
    return ImmutableSet.copyOf(Sets.union(getRewriteRules(), super.getAssumptions()));
  }
  
  protected Expression applyF(Expression arg) {
    return f.index(arg);
  }
  
  protected BooleanExpression applyCycle(Expression arg) {
    return getExpressionManager().applyExpr(cycle, arg).asBooleanExpression();
  }
  
  protected BooleanExpression applyRfAvoid(Expression... args) {
    Preconditions.checkArgument(args.length == 3);
    ImmutableList<Expression> argExprs = new ImmutableList.Builder<Expression>().add(args).build();
    return getExpressionManager().applyExpr(rf_avoid, argExprs).asBooleanExpression();
  }
  
  protected Expression applyJoin(Expression... args) {
    Preconditions.checkArgument(args.length == 2);
    ImmutableList<Expression> argExprs = new ImmutableList.Builder<Expression>().add(args).build();
    return getExpressionManager().applyExpr(join, argExprs);
  }
  
  private ImmutableSet<BooleanExpression> getRewriteRules() {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    composeRewriteRules();
    for(Axiom axiom : rewrite_axioms)
      builder.add(axiom.getRule());
    return builder.build();
  }

  /**
   * Check if <code>expr</code> contains applyF sub-expression.
   */
  private ImmutableSet<? extends Expression> checkApplyF(Expression expr) {
    ImmutableSet.Builder<Expression> instCand_builder = ImmutableSet.builder();
    
    if(expr.getArity() == 0)    return instCand_builder.build();   
    if(expr.getKind().equals(Kind.ARRAY_INDEX)) 
      if(f.equals(expr.getChild(0)))
        return instCand_builder.add(expr.getChild(1)).build();
  
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
      for(Expression term : ground_terms)   res.add(
          new ImmutableList.Builder<Expression>().add(term).build());
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
    
    ImmutableSet.Builder<Axiom> inst_rulesetBuilder = ImmutableSet
        .builder();
    composeRewriteRules();
    for(Axiom axiom : rewrite_axioms) {
      BooleanExpression rule = axiom.getRule();
      BooleanExpression body = rule.getBody();
      if(body != null) {
        ImmutableSet<? extends Expression> instCand = null;
        if(Preferences.isSet(Preferences.OPTION_PARTIAL_INST)) {
          if(!getInstOpt().equals(InstOpt.ELEMENT)) // field instantiation is not applicable here
            throw new IllegalArgumentException("--partial-inst has invalid arg for this theory.");
          instCand = checkApplyF(body); // check if body contains applyF(x)
        } else { // TOTOALLY_INST
          ImmutableSet.Builder<Expression> instCand_builder = ImmutableSet.builder();
          for(Expression key : axiom.getBounds()) {
            Expression var = axiom.getVar(key);
            if(rule.getBoundVars().contains(var) && key.getType().equals(eltType))  
              instCand_builder.add(key);
          }
          instCand = instCand_builder.build();
        }
        if(!instCand.isEmpty()) {
          ImmutableList<? extends Expression> instBodyList = instantiate(body, instCand, gterms);
            
          List<? extends Expression> boundVars = Lists.newArrayList(rule.getBoundVars());
          for(Expression cand : instCand)   boundVars.remove(axiom.getVar(cand));
          
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
            inst_rulesetBuilder.add(Axiom.create(axiom.getName(), inst_rule));
          }
          continue;
        }
      }
      inst_rulesetBuilder.add(axiom); 
    }
    rewrite_axioms = ImmutableSet.copyOf(inst_rulesetBuilder.build());
  }
  
  @Override
  public Expression getEltExpr(Expression arg) {
    Preconditions.checkArgument(arg.getType().
        equals(getExpressionManager().bitVectorType(DEFAULT_WORD_SIZE)));
    return consConstr.apply(arg);
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
  public BooleanExpression reach(String field, Expression arg1, Expression arg2, Expression arg3) {
    return applyRfAvoid(getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
  
  @Override
  public void updateReach(String field, Expression lval, Expression rval) {
    f = f.update(getEltExpr(lval), getEltExpr(rval));
  }

  @Override
  public BooleanExpression assignReach(String field, Expression arg1,
      Expression arg2) {
    return f.index(getEltExpr(arg1)).eq(getEltExpr(arg2));
  }
  
  @Override
  public Type getEltType() {
    return eltType;
  }
  
  @Override
  public Expression getNil() {
    return nil;
  }
  
  /** f(null)=null */
  private Axiom nil_axiom() {
    Axiom axiom = Axiom.create("nil");
    BooleanExpression body = applyF(nil).eq(nil);
    axiom.setRule(body);
    return axiom;
  }
  
  @SuppressWarnings("unused")
  /** Rf_avoid(x, x, u) */
  private Axiom refl_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("refl");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression body = applyRfAvoid(xbounds[1], xbounds[1], xbounds[0]);
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(x, f(x), y) || x = y */
  private Axiom step_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("step");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyF(xbounds[1]);
    BooleanExpression body = exprManager.or(
        applyRfAvoid(xbounds[1], _let_0, xbounds[0]),
        xbounds[1].eq(xbounds[0]));
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** f(x) = x && Rf_avoid(x, y, y) => x = y */
  private Axiom selfLoop_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("selfLoop");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyF(xbounds[1]);
    BooleanExpression head = exprManager.and(
        _let_0.eq(xbounds[1]),
        applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
    BooleanExpression body = xbounds[1].eq(xbounds[0]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, x) => x = y */
  private Axiom sandwich_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("sandwich");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[0]);
    BooleanExpression body = xbounds[1].eq(xbounds[0]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, u) => Rf_avoid(x, y, y) */
  private Axiom reach_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("reach");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]);
    BooleanExpression body = applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, y) => Rf_avoid(x, u, y) || Rf_avoid(x, y, u) */
  private Axiom linear1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("linear1");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]);
    BooleanExpression body = exprManager.or(
        applyRfAvoid(xbounds[0], xbounds[2], xbounds[1]),
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, u) && Rf_avoid(x, z, v) => 
   * (Rf_avoid(x, z, u) && Rf_avoid(z, y, u)) || 
   * (Rf_avoid(x, y, v) && Rf_avoid(y, z, v))
   */
  private Axiom linear2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("linear2");
    Expression xbounds[] = new Expression[5];
    VariableExpression xvars[] = new VariableExpression[5];
    for(int i = 0; i < 5; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]),
        applyRfAvoid(xbounds[0], xbounds[2], xbounds[4]));
    BooleanExpression body = exprManager.or(
        exprManager.and(
            applyRfAvoid(xbounds[0], xbounds[2], xbounds[3]),
            applyRfAvoid(xbounds[2], xbounds[1], xbounds[3])), 
        exprManager.and(
            applyRfAvoid(xbounds[0], xbounds[1], xbounds[4]),
            applyRfAvoid(xbounds[1], xbounds[2], xbounds[4])));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, u) && Rf_avoid(y, z, u) => Rf_avoid(x, z, u)*/
  private Axiom trans1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("trans1");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]), 
        applyRfAvoid(xbounds[1], xbounds[2], xbounds[3]));
    BooleanExpression body = applyRfAvoid(xbounds[0], xbounds[2], xbounds[3]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, y, z) && Rf_avoid(y, u, z) && Rf_avoid(y, z, z) => Rf(f, x, y, u) */
  private Axiom trans2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("trans2");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[2]), 
        applyRfAvoid(xbounds[1], xbounds[3], xbounds[2]),
        applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[0], xbounds[1], xbounds[3]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, join(f, x, y), join(f, x, y) */
  private Axiom join1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join1");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyJoin(xbounds[0], xbounds[1]);
    BooleanExpression body = applyRfAvoid(xbounds[0], _let_0, _let_0);
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(y, join(f, x, y), join(f, x, y))*/
  private Axiom join2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join2");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyJoin(xbounds[0], xbounds[1]);
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]),
        applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[1], _let_0, _let_0);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(x, z, z) && Rf_avoid(y, z, z) => Rf_avoid(x, join(f, x, y), z) */
  private Axiom join3_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join3");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyJoin(xbounds[0], xbounds[1]);
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[2], xbounds[2]), 
        applyRfAvoid(xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[0], _let_0, xbounds[2]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(y, join(f, x, y), join(f, x, y)) || x = join(f, x, y) */
  private Axiom join4_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join4");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    Expression _let_0 = applyJoin(xbounds[0], xbounds[1]);
    BooleanExpression body = exprManager.or(
        applyRfAvoid(xbounds[1], _let_0, _let_0),
        _let_0.eq(xbounds[0]));
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(x, y, y) && Rf_avoid(y, x, x) => cycle(f, x) || x = y */
  private Axiom cycle1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("cycle1");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]),
        applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]));
    BooleanExpression body = exprManager.or(
        applyCycle(xbounds[0]), 
        xbounds[0].eq(xbounds[1]));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** cycle(f, x) && Rf_avoid(x, y, y) => Rf_avoid(y, x, x) */
  private Axiom cycle2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("cycle2");
    Expression xbounds[] = new Expression[2];
    VariableExpression xvars[] = new VariableExpression[2];
    for(int i = 0; i < 2; i++) {
      xbounds[i] = exprManager.boundExpression(i, eltType);
      xvars[i] = exprManager.variable("x", eltType, true);
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Lists.reverse(Arrays.asList(xvars));
    BooleanExpression head = exprManager.and(
        applyCycle(xbounds[0]), 
        applyRfAvoid(xbounds[0], xbounds[1], xbounds[1]));
    BooleanExpression body = applyRfAvoid(xbounds[1], xbounds[0], xbounds[0]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  private void composeRewriteRules() {    
    if(rewrite_axioms == null) {
      ImmutableSet.Builder<Axiom> rewrite_rulesetBuilder = ImmutableSet
        .builder();
      rewrite_rulesetBuilder.add(nil_axiom());
      rewrite_rulesetBuilder.add(step_axiom());
      rewrite_rulesetBuilder.add(selfLoop_axiom());
      rewrite_rulesetBuilder.add(sandwich_axiom());
      rewrite_rulesetBuilder.add(reach_axiom());
      rewrite_rulesetBuilder.add(linear1_axiom());
      rewrite_rulesetBuilder.add(linear2_axiom());
      rewrite_rulesetBuilder.add(trans1_axiom());
      rewrite_rulesetBuilder.add(trans2_axiom());
      rewrite_rulesetBuilder.add(join1_axiom());
      rewrite_rulesetBuilder.add(join2_axiom());
      rewrite_rulesetBuilder.add(join3_axiom());
      rewrite_rulesetBuilder.add(join4_axiom());
      rewrite_rulesetBuilder.add(cycle1_axiom());
      rewrite_rulesetBuilder.add(cycle2_axiom());
      rewrite_axioms = rewrite_rulesetBuilder.build();
    }
  }
}
