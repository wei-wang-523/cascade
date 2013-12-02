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

import java.util.Arrays;
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
import edu.nyu.cascade.ir.expr.DefaultPointerEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.FlatMemoryModel;
import edu.nyu.cascade.ir.expr.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.util.Preferences;

public class ListEncoding_CVC4 extends ListEncoding {

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding, IRSingleHeapEncoder heapEncoder) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    return FlatMemoryModel.create(encoding, heapEncoder);
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
  private final Expression lengthList;

  public static int DEFAULT_WORD_SIZE;
  
  public static ListEncoding_CVC4 create(
      ExpressionManager exprManager) throws ExpressionFactoryException {
    int cellSize = 
    		Preferences.isSet(Preferences.OPTION_MULTI_CELL) ? 
    				DefaultSize
    				: Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
    						Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
    						: DefaultSize;

    int intCellSize = 
    		Preferences.isSet(Preferences.OPTION_MULTI_CELL) ? 
    				(int) (cAnalyzer.getSize(xtc.type.NumberT.INT) * cellSize) 
    				: cellSize;
    
    DEFAULT_WORD_SIZE = intCellSize;
    
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    PointerEncoding<TupleExpression> tupleEncoding = new DefaultPointerEncoding(exprManager);
    
    return new ListEncoding_CVC4(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
  public ListEncoding_CVC4(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> tupleEncoding) {
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
      lengthList = exprManager.functionVar(FUN_LENGTH_LIST, 
          exprManager.functionType(FUN_LENGTH_LIST, list, lenType), false);
      

      /* Create data constraints */
      ImmutableSet.Builder<BooleanExpression> rewrite_rulesetBuilder = ImmutableSet
          .builder();
      
      VariableExpression l = list.boundVariable("l", true);
      IntegerVariableExpression e = (IntegerVariableExpression) lenType.boundVariable("e", true);
      
      ImmutableList<VariableExpression> vars = ImmutableList.of(l);      
      BooleanExpression guard = exprManager.testConstructor(nilConstr, l);
      Expression head = applyLengthList(l);
      Expression body = exprManager.zero();      
      BooleanExpression rrRewrite = exprManager.rrRewrite(head, body);
      BooleanExpression rewrite_rule1 = exprManager.rewriteRule(vars, guard, rrRewrite);
      
      rewrite_rulesetBuilder.add(rewrite_rule1);
      
      vars = ImmutableList.of(e, l);
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

  public IntegerExpression applyLengthList(Expression x) {
    Preconditions.checkArgument(x.isInductive());
    return getExpressionManager().applyExpr(lengthList, x).asIntegerExpression();
  }
  
  public Expression applyConsConstr(Expression ... args) {
    ImmutableList<Expression> newArgs = ImmutableList.copyOf(Arrays.asList(args));
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
