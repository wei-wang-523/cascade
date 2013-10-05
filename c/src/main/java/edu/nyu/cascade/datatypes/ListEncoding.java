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
import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModelSound;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.TupleEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
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
    return BitVectorMemoryModelSound.create(encoding);
  }
  
  public ListEncoding(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      TupleEncoding<TupleExpression> tupleEncoding) {
    super(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }

  public abstract IntegerExpression applyLengthList(Expression x) ;
  
  public abstract Expression applyConsConstr(Expression ... args) ;

  public abstract Expression applyNilConstr() ;

  public abstract Expression applyHeadSel(Expression arg) ;

  public abstract Expression applyTailSel(Expression arg) ;
}
