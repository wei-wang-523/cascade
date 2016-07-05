package edu.nyu.cascade.reachability;

/** 
 * The list corresponds to the following pseudo-declaration:
 <pre>
 list =
 cons    { head:Int, tail:list }
 | nil 
 </pre>
 */

import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;

public abstract class ListReachabilityEncoding extends
		AbstractExpressionEncoding {

	protected static final String DATATYPE_NAME = "list";
	protected static final String CONS_CONSTR_NAME = "cons";
	protected static final String NIL_CONSTR_NAME = "nil";
	protected static final String HEAD_SELECTOR_NAME = "head";
	protected static final String TAIL_SELECTOR_NAME = "tail";
	protected static final String FUN_LIST = DATATYPE_NAME;
	protected static final String FUN_LENGTH_LIST = "lengthList";

	public ListReachabilityEncoding(
			IntegerEncoding<BitVectorExpression> integerEncoding,
			BooleanEncoding<BooleanExpression> booleanEncoding,
			ArrayEncoding<ArrayExpression> arrayEncoding,
			PointerEncoding<Expression> tupleEncoding) {
		super(integerEncoding, booleanEncoding, arrayEncoding, tupleEncoding);
	}

	public abstract IntegerExpression applyLengthList(Expression x);

	public abstract Expression applyConsConstr(Expression... args);

	public abstract Expression applyNilConstr();

	public abstract Expression applyHeadSel(Expression arg);

	public abstract Expression applyTailSel(Expression arg);
}
