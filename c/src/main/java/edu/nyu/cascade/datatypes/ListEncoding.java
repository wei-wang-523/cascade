package edu.nyu.cascade.datatypes;

/** 
 * The list corresponds to the following pseudo-declaration:
 <pre>
 list =
 cons    { head:Int, tail:list }
 | nil 
 </pre>
 */

import com.google.common.base.Preconditions;
import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModel;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.UnimplementedTupleEncoding;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TupleExpression;

public abstract class ListEncoding extends AbstractExpressionEncoding {

  protected static final String DATATYPE_NAME = "list";

  protected static final String CONS_CONSTR_NAME = "cons";

  protected static final String NIL_CONSTR_NAME = "nil";

  protected static final String HEAD_SELECTOR_NAME = "head";
  
  protected static final String TAIL_SELECTOR_NAME = "tail";
  
  protected static final String FUN_LIST = DATATYPE_NAME;

  protected static final String FUN_LENGTH_LIST = "lengthList";

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    return BitVectorMemoryModel.create(encoding);
  }

  public static final int DEFAULT_WORD_SIZE = 8;
  
  public ListEncoding(ExpressionManager exprManager) {
    super(BitVectorIntegerEncoding.create(exprManager, DEFAULT_WORD_SIZE),
        new DefaultBooleanEncoding(exprManager),
        new DefaultArrayEncoding(exprManager),
        new UnimplementedTupleEncoding<TupleExpression>());
  }

  public abstract IntegerExpression applyLengthList(Expression x) ;
  
  public abstract Expression applyConsConstr(Expression ... args) ;

  public abstract Expression applyNilConstr() ;

  public abstract Expression applyHeadSel(Expression arg) ;

  public abstract Expression applyTailSel(Expression arg) ;
}
