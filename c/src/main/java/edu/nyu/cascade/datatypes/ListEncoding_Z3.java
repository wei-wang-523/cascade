package edu.nyu.cascade.datatypes;

/** 
 * The list corresponds to the following pseudo-declaration:
 <pre>
 list =
 cons    { head:Int, tail:list }
 | nil 
 </pre>
 */

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.BitVectorMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.Selector;

public class ListEncoding_Z3 extends ListEncoding {

  private static final String DATATYPE_NAME = "list";

  private static final String CONS_CONSTR_NAME = "cons";

  private static final String NIL_CONSTR_NAME = "nil";

  private static final String HEAD_SELECTOR_NAME = "head";
  
  private static final String TAIL_SELECTOR_NAME = "tail";
  
  private static final String FUN_LIST = DATATYPE_NAME;

  private static final String FUN_LENGTH_LIST = "lengthList";

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return BitVectorMemoryModel.create(encoding, size, size);
  }

  /* The list inductive data type */
  private final InductiveType list;
  
  /* The constructors for list */
  private final Constructor consConstr, nilConstr;
  
  /* Selector for the head of list in consConstr */
  private final Selector headSel;
  /* Selector for the tail of list in consConstr */
  private final Selector tailSel;
  
  private final ImmutableSet<BooleanExpression> rewrite_rules;
  
  /** The list -> length (int) mapping */
  private final FunctionType lengthList;

  public static final int DEFAULT_WORD_SIZE = 8;
  
  public ListEncoding_Z3(ExpressionManager exprManager) {
    super(exprManager);

    try {
      IntegerType lenType = exprManager.integerType();
      
      /* Create datatype constructors */

      // labelTagSel = exprManager.selector(LABEL_TAG_SELECTOR_NAME, tagType);
      headSel = exprManager.selector(HEAD_SELECTOR_NAME, exprManager.integerType());
      tailSel = exprManager.selector(TAIL_SELECTOR_NAME, exprManager
          .inductiveType(DATATYPE_NAME), 0);
      consConstr = exprManager.constructor(CONS_CONSTR_NAME, headSel,
          tailSel);

      nilConstr = exprManager.constructor(NIL_CONSTR_NAME);

      /* Create datatype */
      list = exprManager.dataType(DATATYPE_NAME, consConstr, nilConstr);
      
      lengthList = exprManager.functionType(FUN_LENGTH_LIST, list, lenType);
      

      /* Create data constraints */
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      VariableExpression l_var = exprManager.variable("x_0", list, true);
      Expression l = exprManager.boundExpression(0, list);
      VariableExpression e_var = exprManager.variable("x_1", lenType, true);
      Expression e = exprManager.boundExpression(1, lenType);
      
      ImmutableList<VariableExpression> vars = ImmutableList.of(l_var);      
      BooleanExpression guard = exprManager.testConstructor(nilConstr, l);
      Expression head = applyLengthList(l);
      Expression body = exprManager.zero();      
      BooleanExpression ruleExpr = exprManager.implies(guard, head.eq(body));
      BooleanExpression rewrite_rule1 = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(rewrite_rule1);
      
      vars = ImmutableList.of(e_var, l_var);

      head = applyLengthList(exprManager.construct(consConstr, e, l));
      body = exprManager.plus(exprManager.one(), exprManager.applyExpr(lengthList, Lists.newArrayList(l)));
      ruleExpr = head.eq(body);
      BooleanExpression rewrite_rule2 = exprManager.forall(vars, ruleExpr);
      
      rewrite_rulesetBuilder.add(rewrite_rule2);
      
      rewrite_rules = rewrite_rulesetBuilder.build();
      
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  @Override
  public Expression functionCall(String name, Iterable<? extends Expression> argsIter) {
    List<Expression> args = ImmutableList.copyOf(argsIter);
    try {
      if (FUN_LIST.equals(name)) {
        checkArgument(args.size() == 1);
        return args.get(0);
      }

      if (FUN_LENGTH_LIST.equals(name)) {
        checkArgument(args.size() == 1);
        return lengthList.apply(args.get(0));
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

  public IntegerExpression applyLengthList(Expression x) {
    Preconditions.checkArgument(x.isInductive());
    return lengthList.apply(x).asIntegerExpression();
  }
  
  public Expression applyConsConstr(Expression ... args) {
    ImmutableList<Expression> newArgs = ImmutableList.of(args);
    Preconditions.checkArgument(newArgs.size() == 2);
    return getExpressionManager().construct(consConstr, newArgs);
  }

  public Expression applyNilConstr() {
    return getExpressionManager().construct(nilConstr);
  }

  public Expression applyHeadSel(Expression arg) {
    return getExpressionManager().select(headSel, arg);
  }

  public Expression applyTailSel(Expression arg) {
    return getExpressionManager().select(tailSel, arg);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions() {
    return ImmutableSet.copyOf(Sets.union(rewrite_rules, super.getAssumptions()));
  }
}
