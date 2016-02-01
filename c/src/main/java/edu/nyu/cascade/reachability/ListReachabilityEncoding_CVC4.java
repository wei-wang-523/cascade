package edu.nyu.cascade.reachability;

/** 
 * The list corresponds to the following pseudo-declaration:
 <pre>
 list =
 cons    { head:Int, tail:list }
 | nil 
 </pre>
 */

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.ir.expr.UnimplementedPointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.Selector;

public class ListReachabilityEncoding_CVC4 extends ListReachabilityEncoding {

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
  private final FunctionExpression lengthList;
  
  public static ListReachabilityEncoding_CVC4 create(
      ExpressionManager exprManager) throws ExpressionFactoryException {
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, WORD_SIZE);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    PointerEncoding<Expression> tupleEncoding = new UnimplementedPointerEncoding<Expression>();
    
    return new ListReachabilityEncoding_CVC4(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
  private ListReachabilityEncoding_CVC4(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<Expression> tupleEncoding) {
    super(integerEncoding, booleanEncoding, arrayEncoding, tupleEncoding);

    try {
      ExpressionManager exprManager = getExpressionManager();
      
      IntegerType lenType = exprManager.integerType();
      
      /* Create datatype constructors */
      // labelTagSel = exprManager.selector(LABEL_TAG_SELECTOR_NAME, tagType);
      headSel = exprManager.selector(HEAD_SELECTOR_NAME, exprManager.integerType());
      tailSel = exprManager.selector(TAIL_SELECTOR_NAME, exprManager
          .inductiveType(DATATYPE_NAME));
      consConstr = exprManager.constructor(CONS_CONSTR_NAME, headSel, tailSel);
      nilConstr = exprManager.constructor(NIL_CONSTR_NAME);

      /* Create datatype */
      list = exprManager.dataType(DATATYPE_NAME, consConstr, nilConstr);
      lengthList = exprManager.functionDeclarator(FUN_LENGTH_LIST,
      		exprManager.functionType(list, lenType), false);
      

      /* Create data constraints */
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      Expression l1 = list.boundVar("l1", true);
      Collection<Expression> var = Collections.singletonList(l1);
      BooleanExpression guard = exprManager.testConstructor(nilConstr, l1);
      Expression head = applyLengthList(l1);
      Expression body = exprManager.zero();      
      BooleanExpression rrRewrite = exprManager.rrRewrite(head, body);
      BooleanExpression rewrite_rule1 = exprManager.rewriteRule(var, guard, rrRewrite);
      
      rewrite_rulesetBuilder.add(rewrite_rule1);
      
      Expression l = list.boundVar("l", true);
      Expression e = lenType.boundVar("e", true);
      Collection<Expression> vars = Lists.newArrayList(l, e);
      guard = exprManager.tt();

      head = applyLengthList(exprManager.construct(consConstr, e, l));
      body = exprManager.plus(exprManager.one(), exprManager.applyExpr(lengthList, Lists.newArrayList(l)));
      rrRewrite = exprManager.rrRewrite(head, body);
      BooleanExpression rewrite_rule2 = exprManager.rewriteRule(vars, guard, rrRewrite);
      
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
        return getExpressionManager().applyExpr(lengthList, args.get(0));
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
  public IntegerExpression applyLengthList(Expression x) {
    Preconditions.checkArgument(x.isInductive());
    return getExpressionManager().applyExpr(lengthList, x).asIntegerExpression();
  }
  
  @Override
  public Expression applyConsConstr(Expression ... args) {
    ImmutableList<Expression> newArgs = ImmutableList.copyOf(Arrays.asList(args));
    Preconditions.checkArgument(newArgs.size() == 2);
    return getExpressionManager().construct(consConstr, newArgs);
  }
  
  @Override
  public Expression applyNilConstr() {
    return getExpressionManager().construct(nilConstr);
  }

  @Override
  public Expression applyHeadSel(Expression arg) {
    return getExpressionManager().select(headSel, arg);
  }

  @Override
  public Expression applyTailSel(Expression arg) {
    return getExpressionManager().select(tailSel, arg);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions() {
    return ImmutableSet.copyOf(Sets.union(rewrite_rules, super.getAssumptions()));
  }
}
