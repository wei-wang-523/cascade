package edu.nyu.cascade.ir.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
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

public class LoLLiwithQFDArrReachEncoding extends ReachEncoding {
  
  public static ReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return ReachMemoryModel.create(encoding, size, size);
  }
  
  private ImmutableSet<Axiom> rewrite_axioms;
  
  /** The null variable in elt */
  private final Expression nil;
  
  /** The (elt, elt, elt) -> bool mapping */
  private final FunctionType rf_avoid;
  
  /** The elt -> bool mapping */
  private final FunctionType cycle;
  
  /** The (elt, elt) -> elt mapping */
  private final FunctionType join;
  
  /** Constructor and Selector for the elt type*/
  
  private final Type fldType;
  
  private final Type eltType;
  
  private final Constructor consConstr;
  
  private final Selector nextSel;
  
  private Map<String, ArrayExpression> fldMap;
  
  public LoLLiwithQFDArrReachEncoding(ExpressionManager exprManager) {
    super(exprManager);

    try {
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);
      
      fldMap = Maps.newHashMap();

      /* Create datatype */
      nextSel = exprManager.selector(NEXT_SELECTOR_NAME, wordType);
      consConstr = exprManager.constructor(ELT_F_CONST, nextSel);
      eltType = exprManager.dataType(ELT_DATATYPE, consConstr);
      fldType = exprManager.arrayType(eltType, eltType);
      
      /* Create function expression */
      
      nil = getEltExpr(exprManager.bitVectorZero(DEFAULT_WORD_SIZE));
      rf_avoid = exprManager.functionType(FUN_RF_AVOID,
          ImmutableList.of(fldType, eltType, eltType, eltType), 
          exprManager.booleanType());
      cycle = exprManager.functionType(FUN_CYCLE, 
          ImmutableList.of(fldType, eltType), 
          exprManager.booleanType());
      join = exprManager.functionType(FUN_JOIN, 
          ImmutableList.of(fldType, eltType, eltType), eltType);
      
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  @Override
  public Expression functionCall(String name, Iterable<? extends Expression> argsIter) {
    List<Expression> args = ImmutableList.copyOf(argsIter);
    try {      
      if (FUN_RF_AVOID.equals(name)) {
        checkArgument(args.size() == 4);
        return rf_avoid.apply(args);
      }
      
      if (FUN_CYCLE.equals(name)) {
        checkArgument(args.size() == 2);
        return cycle.apply(args.get(0));
      }
      
      if (FUN_JOIN.equals(name)) {
        checkArgument(args.size() == 3);
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
  
  protected Expression applyF(Expression fldExpr, Expression arg) {
    return fldExpr.asArray().index(arg);
  }
  
  protected BooleanExpression applyCycle(Expression fldExpr, Expression arg) {
    return getExpressionManager().applyExpr(cycle, fldExpr, arg).asBooleanExpression();
  }
  
  protected BooleanExpression applyRfAvoid(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 4);
    return getExpressionManager().applyExpr(rf_avoid, argExprs).asBooleanExpression();
  }
  
  protected Expression applyJoin(Expression... args) {
    ImmutableList<Expression> argExprs = ImmutableList.of(args);
    Preconditions.checkArgument(argExprs.size() == 3);
    return getExpressionManager().applyExpr(join, argExprs);
  }
  
  private ImmutableSet<BooleanExpression> getRewriteRules() {
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    composeRewriteRules();
    for(Axiom axiom : rewrite_axioms)
      builder.add(axiom.getRule());
    return builder.build();
  }
  
  private static class InstCand {
    private final ImmutableSet<? extends Expression> indices;
    private final ImmutableSet<? extends Expression> arrays;
    
    InstCand(ImmutableSet<? extends Expression> indices,
        ImmutableSet<? extends Expression> arrays) {
      this.indices = indices;
      this.arrays = arrays;
    }
    
    public static InstCand create(ImmutableSet<? extends Expression> indices,
        ImmutableSet<? extends Expression> arrays) {
      return new InstCand(indices, arrays);
    }
    
    public ImmutableSet<? extends Expression> getIndices() {
      return indices;
    }
    
    public ImmutableSet<? extends Expression> getArrays() {
      return arrays;
    }
    
    public boolean isNoIndices() {
      return indices.isEmpty();
    }
    
    public boolean isNoArrays() {
      return arrays.isEmpty();
    }
  }
  
  /**
   * Check if <code>expr</code> contains applyF sub-expression.
   */
  private InstCand checkApplyF(Expression expr, 
      List<? extends Expression> bounds) {
    ImmutableSet.Builder<Expression> instIndices_builder = ImmutableSet.builder();   
    ImmutableSet.Builder<Expression> instArrays_builder = ImmutableSet.builder();  
    if(expr.getArity() == 0)    
      return InstCand.create(instIndices_builder.build(), instArrays_builder.build()); 
    if(expr.getKind().equals(Kind.ARRAY_INDEX)) {
      if(expr.getChild(0).getType().equals(fldType) && bounds.contains(expr.getChild(0))) {
        instArrays_builder.add(expr.getChild(0));
        if(expr.getChild(1).getType().equals(eltType) && bounds.contains(expr.getChild(1)))
          instIndices_builder.add(expr.getChild(1));
      }
    }
    for(Expression child : expr.getChildren()) {
      InstCand cand = checkApplyF(child, bounds);
      instIndices_builder.addAll(cand.getIndices());
      instArrays_builder.addAll(cand.getArrays());
    }
    return InstCand.create(instIndices_builder.build(), instArrays_builder.build()); 
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
    
    ImmutableSet.Builder<Axiom> inst_axiomSetBuilder = ImmutableSet
        .builder();
    composeRewriteRules();
    for(Axiom axiom : rewrite_axioms) {
      BooleanExpression rule = axiom.getRule();
      BooleanExpression body = rule.getBody();
      if(body != null) {
        InstCand instCand = null;
        List<? extends Expression> boundVars = Lists.newArrayList(rule.getBoundVars());
        
        if(Preferences.isSet(Preferences.OPTION_PARTIAL_INST)) {          
          instCand = checkApplyF(body, axiom.getBounds()); // check if body contains applyF(x)
        } else { // TOTOALLY_INST
          ImmutableSet.Builder<Expression> instIndices_builder = ImmutableSet.builder();   
          ImmutableSet.Builder<Expression> instArrays_builder = ImmutableSet.builder(); 
          for(Expression key : axiom.getBounds()) {
            Expression var = axiom.getVar(key);
            if(rule.getBoundVars().contains(var) && key.getType().equals(eltType))  
              instIndices_builder.add(key);
            if(key.getType().equals(fldType))
              instArrays_builder.add(key);
          }
          instCand = InstCand.create(instIndices_builder.build(), instArrays_builder.build());
        }
        
        if(!(instCand.isNoArrays() && instCand.isNoIndices())) {
          ImmutableList<? extends Expression> instBodyList = ImmutableList.of(body);
          
          if((getInstOpt().equals(InstOpt.ELEMENT) 
              || getInstOpt().equals(InstOpt.FIELD_OF_ELEMENT))
              && !instCand.isNoIndices()) { // Instantiate x in the applyF(f, x)
            ImmutableList.Builder<Expression> instBodyList_builder = ImmutableList.builder();
            for(Expression instBody : instBodyList)
              instBodyList_builder.addAll(instantiate(instBody, instCand.getIndices(), gterms));
            instBodyList = instBodyList_builder.build();
            for(Expression cand : instCand.getIndices())     boundVars.remove(axiom.getVar(cand));
          }
          
          if((getInstOpt().equals(InstOpt.FIELD) 
              || getInstOpt().equals(InstOpt.FIELD_OF_ELEMENT))
              && !instCand.isNoArrays()) { // Instantiate f in the apply(f, x)
            ImmutableList.Builder<Expression> instBodyList_builder = ImmutableList.builder();
            for(Expression instBody : instBodyList) {
              ImmutableSet.Builder<ArrayExpression> fields_builder = ImmutableSet.builder();
              for(Entry<String, ArrayExpression> entry : fldMap.entrySet())
                fields_builder.add(entry.getValue());
              instBodyList_builder.addAll(instantiate(instBody, instCand.getArrays(), fields_builder.build()));
            }
            instBodyList = instBodyList_builder.build();
            for(Expression cand : instCand.getArrays())     boundVars.remove(axiom.getVar(cand));
          }
          for(Expression instBody : instBodyList) {
            BooleanExpression inst_rule = boundVars.isEmpty() ? instBody.asBooleanExpression() :
              getExpressionManager().forall(boundVars, instBody/*, iter.next()*/);
            inst_axiomSetBuilder.add(Axiom.create(axiom.getName(), inst_rule));
          }
          continue;
        }
      }
      inst_axiomSetBuilder.add(axiom); 
    }
    rewrite_axioms = ImmutableSet.copyOf(inst_axiomSetBuilder.build());
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
    Expression fldExpr = getFldExpr(field);
    BooleanExpression res = exprManager.implies(rootExpr.neq(nil), 
        exprManager.forall(x_var, rootExpr.neq(applyF(fldExpr, x_var))));
    return res;
  }
  
  @Override
  public BooleanExpression reach(String field, Expression arg1, Expression arg2, Expression arg3) {
    ArrayExpression fldExpr = getFldExpr(field);
    return applyRfAvoid(fldExpr, getEltExpr(arg1), getEltExpr(arg2), getEltExpr(arg3));
  }
  
  @Override
  public void updateReach(String field, Expression lval, Expression rval) {
    ArrayExpression fldExpr = getFldExpr(field);
    fldExpr = fldExpr.update(getEltExpr(lval), getEltExpr(rval));
    fldMap.put(field, fldExpr);
  }

  @Override
  public BooleanExpression assignReach(String field, Expression arg1,
      Expression arg2) {
    ArrayExpression fldExpr = getFldExpr(field);
    return fldExpr.index(getEltExpr(arg1)).eq(getEltExpr(arg2));
  }
  
  @Override
  public Type getEltType() {
    return eltType;
  }
  
  @Override
  public Expression getNil() {
    return nil;
  }
  
  private ArrayExpression getFldExpr(String field) {
    if(fldMap.containsKey(field))
      return fldMap.get(field);
    else {
      ArrayExpression fldExpr = getExpressionManager().variable(field, fldType, true).asArray();
      fldMap.put(field, fldExpr);
      return fldExpr;
    }
  }
  
  /** f(null)=null */
  private Axiom nil_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("nil");
    VariableExpression xvar_0 = exprManager.variable("x", fldType, true);
    Expression xbound_0 = exprManager.boundExpression(0, fldType);
    axiom.putBoundVar(xbound_0, xvar_0);
    
    Iterable<? extends VariableExpression> vars = ImmutableList.of(xvar_0);
    BooleanExpression body = applyF(xbound_0, nil).eq(nil);
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  @SuppressWarnings("unused")
  /** Rf_avoid(f, x, x, u) */
  private Axiom refl_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("refl");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression body = applyRfAvoid(xbounds[2], xbounds[1], xbounds[1], xbounds[0]);
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(f, x, f(x), y) || x = y */
  private Axiom step_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("step");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    if(getInstOpt().equals(InstOpt.FIELD)) { // --partial-inst on element or total 
      for(int i = 0; i < 3; i++) {
        if(i == 2) {
          xbounds[i] = exprManager.boundExpression(i, fldType);
          xvars[i] = exprManager.variable("x", fldType, true);
        } else {
          xbounds[i] = exprManager.boundExpression(i, eltType);
          xvars[i] = exprManager.variable("x", eltType, true);
        }
        axiom.putBoundVar(xbounds[i], xvars[i]);
      }
      Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
      Expression _let_0 = applyF(xbounds[2], xbounds[1]);
      BooleanExpression body = exprManager.or(
          applyRfAvoid(xbounds[2], xbounds[1], _let_0, xbounds[0]),
          xbounds[1].eq(xbounds[0]));
      axiom.setRule(exprManager.forall(vars, body));
    } else {
      for(int i = 0; i < 3; i++) {
        if(i == 1) {
          xbounds[i] = exprManager.boundExpression(i, fldType);
          xvars[i] = exprManager.variable("x", fldType, true);
        } else {
          xbounds[i] = exprManager.boundExpression(i, eltType);
          xvars[i] = exprManager.variable("x", eltType, true);
        }
        axiom.putBoundVar(xbounds[i], xvars[i]);
      }
      Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
      Expression _let_0 = applyF(xbounds[1], xbounds[2]);
      BooleanExpression body = exprManager.or(
          applyRfAvoid(xbounds[1], xbounds[2], _let_0, xbounds[0]),
          xbounds[2].eq(xbounds[0]));
      axiom.setRule(exprManager.forall(vars, body));
    }
    return axiom;
  }
  
  /** f(x) = x && Rf_avoid(f, x, y, y) => x = y */
  private Axiom selfLoop_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("selfLoop");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    if(getInstOpt().equals(InstOpt.FIELD)) {
      for(int i = 0; i < 3; i++) {
        if(i == 2) {
          xbounds[i] = exprManager.boundExpression(i, fldType);
          xvars[i] = exprManager.variable("x", fldType, true);
        } else {
          xbounds[i] = exprManager.boundExpression(i, eltType);
          xvars[i] = exprManager.variable("x", eltType, true);
        }
        axiom.putBoundVar(xbounds[i], xvars[i]);
      }
      Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
      Expression _let_0 = applyF(xbounds[2], xbounds[1]);
      BooleanExpression head = exprManager.and(
          _let_0.eq(xbounds[1]),
          applyRfAvoid(xbounds[2], xbounds[1], xbounds[0], xbounds[0]));
      BooleanExpression body = xbounds[1].eq(xbounds[0]);
      axiom.setRule(exprManager.forall(vars, head.implies(body)));
    } else {
      for(int i = 0; i < 3; i++) {
        if(i == 1) {
          xbounds[i] = exprManager.boundExpression(i, fldType);
          xvars[i] = exprManager.variable("x", fldType, true);
        } else {
          xbounds[i] = exprManager.boundExpression(i, eltType);
          xvars[i] = exprManager.variable("x", eltType, true);
        }
        axiom.putBoundVar(xbounds[i], xvars[i]);
      }
      Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
      Expression _let_0 = applyF(xbounds[1], xbounds[2]);
      BooleanExpression head = exprManager.and(
          _let_0.eq(xbounds[2]),
          applyRfAvoid(xbounds[1], xbounds[2], xbounds[0], xbounds[0]));
      BooleanExpression body = xbounds[2].eq(xbounds[0]);
      axiom.setRule(exprManager.forall(vars, head.implies(body)));
    }
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, x) => x = y */
  private Axiom sandwich_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("sandwich");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[2], xbounds[0], xbounds[1], xbounds[0]);
    BooleanExpression body = xbounds[1].eq(xbounds[0]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, u) => Rf_avoid(f, x, y, y) */
  private Axiom reach_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("reach");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      if(i == 3) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[3], xbounds[0], xbounds[1], xbounds[2]);
    BooleanExpression body = applyRfAvoid(xbounds[3], xbounds[0], xbounds[1], xbounds[1]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, y) => Rf_avoid(f, x, u, y) || Rf_avoid(f, x, y, u) */
  private Axiom linear1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("linear1");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      if(i == 3) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = applyRfAvoid(xbounds[3], xbounds[0], xbounds[1], xbounds[1]);
    BooleanExpression body = exprManager.or(
        applyRfAvoid(xbounds[3], xbounds[0], xbounds[2], xbounds[1]),
        applyRfAvoid(xbounds[3], xbounds[0], xbounds[1], xbounds[2]));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, u) && Rf_avoid(f, x, z, v) => 
   * (Rf_avoid(f, x, z, u) && Rf_avoid(f, z, y, u)) || 
   * (Rf_avoid(f, x, y, v) && Rf_avoid(f, y, z, v))
   */
  private Axiom linear2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("linear2");
    Expression xbounds[] = new Expression[6];
    VariableExpression xvars[] = new VariableExpression[6];
    for(int i = 0; i < 6; i++) {
      if(i == 5) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[5], xbounds[0], xbounds[1], xbounds[3]),
        applyRfAvoid(xbounds[5], xbounds[0], xbounds[2], xbounds[4]));
    BooleanExpression body = exprManager.or(
        exprManager.and(
            applyRfAvoid(xbounds[5], xbounds[0], xbounds[2], xbounds[3]),
            applyRfAvoid(xbounds[5], xbounds[2], xbounds[1], xbounds[3])), 
        exprManager.and(
            applyRfAvoid(xbounds[5], xbounds[0], xbounds[1], xbounds[4]),
            applyRfAvoid(xbounds[5], xbounds[1], xbounds[2], xbounds[4])));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, u) && Rf_avoid(f, y, z, u) => Rf_avoid(f, x, z, u)*/
  private Axiom trans1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("trans1");
    Expression xbounds[] = new Expression[5];
    VariableExpression xvars[] = new VariableExpression[5];
    for(int i = 0; i < 5; i++) {
      if(i == 4) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[4], xbounds[0], xbounds[1], xbounds[3]), 
        applyRfAvoid(xbounds[4], xbounds[1], xbounds[2], xbounds[3]));
    BooleanExpression body = applyRfAvoid(xbounds[4], xbounds[0], xbounds[2], xbounds[3]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, z) && Rf_avoid(f, y, u, z) && Rf_avoid(f, y, z, z) => Rf(f, x, y, u) */
  private Axiom trans2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("trans2");
    Expression xbounds[] = new Expression[5];
    VariableExpression xvars[] = new VariableExpression[5];
    for(int i = 0; i < 5; i++) {
      if(i == 4) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[4], xbounds[0], xbounds[1], xbounds[2]), 
        applyRfAvoid(xbounds[4], xbounds[1], xbounds[3], xbounds[2]),
        applyRfAvoid(xbounds[4], xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[4], xbounds[0], xbounds[1], xbounds[3]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, join(f, x, y), join(f, x, y) */
  private Axiom join1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join1");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    Expression _let_0 = applyJoin(xbounds[2], xbounds[0], xbounds[1]);
    BooleanExpression body = applyRfAvoid(xbounds[2], xbounds[0], _let_0, _let_0);
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(f, x, z, z) && Rf_avoid(f, y, z, z) => Rf_avoid(f, y, join(f, x, y), join(f, x, y))*/
  private Axiom join2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join2");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      if(i == 3) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    Expression _let_0 = applyJoin(xbounds[3], xbounds[0], xbounds[1]);
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[3], xbounds[0], xbounds[2], xbounds[2]),
        applyRfAvoid(xbounds[3], xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[3], xbounds[1], _let_0, _let_0);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, x, z, z) && Rf_avoid(f, y, z, z) => Rf_avoid(f, x, join(f, x, y), z) */
  private Axiom join3_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join3");
    Expression xbounds[] = new Expression[4];
    VariableExpression xvars[] = new VariableExpression[4];
    for(int i = 0; i < 4; i++) {
      if(i == 3) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    Expression _let_0 = applyJoin(xbounds[3], xbounds[0], xbounds[1]);
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[3], xbounds[0], xbounds[2], xbounds[2]), 
        applyRfAvoid(xbounds[3], xbounds[1], xbounds[2], xbounds[2]));
    BooleanExpression body = applyRfAvoid(xbounds[3], xbounds[0], _let_0, xbounds[2]);
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** Rf_avoid(f, y, join(f, x, y), join(f, x, y)) || x = join(f, x, y) */
  private Axiom join4_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("join4");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    Expression _let_0 = applyJoin(xbounds[2], xbounds[0], xbounds[1]);
    BooleanExpression body = exprManager.or(
        applyRfAvoid(xbounds[2], xbounds[1], _let_0, _let_0),
        _let_0.eq(xbounds[0]));
    axiom.setRule(exprManager.forall(vars, body));
    return axiom;
  }
  
  /** Rf_avoid(f, x, y, y) && Rf_avoid(f, y, x, x) => cycle(f, x) || x = y */
  private Axiom cycle1_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("cycle1");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = exprManager.and(
        applyRfAvoid(xbounds[2], xbounds[0], xbounds[1], xbounds[1]),
        applyRfAvoid(xbounds[2], xbounds[1], xbounds[0], xbounds[0]));
    BooleanExpression body = exprManager.or(
        applyCycle(xbounds[2], xbounds[0]), 
        xbounds[0].eq(xbounds[1]));
    axiom.setRule(exprManager.forall(vars, head.implies(body)));
    return axiom;
  }
  
  /** cycle(f, x) && Rf_avoid(f, x, y, y) => Rf_avoid(f, y, x, x) */
  private Axiom cycle2_axiom() {
    ExpressionManager exprManager = getExpressionManager();
    Axiom axiom = Axiom.create("cycle2");
    Expression xbounds[] = new Expression[3];
    VariableExpression xvars[] = new VariableExpression[3];
    for(int i = 0; i < 3; i++) {
      if(i == 2) {
        xbounds[i] = exprManager.boundExpression(i, fldType);
        xvars[i] = exprManager.variable("x", fldType, true);
      } else {
        xbounds[i] = exprManager.boundExpression(i, eltType);
        xvars[i] = exprManager.variable("x", eltType, true);
      }
      axiom.putBoundVar(xbounds[i], xvars[i]);
    }
    Iterable<? extends VariableExpression> vars = Iterables.reverse(ImmutableList.of(xvars));
    BooleanExpression head = exprManager.and(
        applyCycle(xbounds[2], xbounds[0]), 
        applyRfAvoid(xbounds[2], xbounds[0], xbounds[1], xbounds[1]));
    BooleanExpression body = applyRfAvoid(xbounds[2], xbounds[1], xbounds[0], xbounds[0]);
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
