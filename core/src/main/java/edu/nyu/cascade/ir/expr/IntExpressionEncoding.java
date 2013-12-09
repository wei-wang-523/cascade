package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an bitvector-to-bitvector array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TupleExpression;

public class IntExpressionEncoding extends AbstractExpressionEncoding {
  
  public static IntExpressionEncoding create(ExpressionManager exprManager) {
    IntegerEncoding<IntegerExpression> integerEncoding = new DefaultIntegerEncoding(exprManager);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    PointerEncoding<TupleExpression> pointerEncoding = new UnimplementedPointerEncoding<TupleExpression>();
    return new IntExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }

  public IntExpressionEncoding(
      IntegerEncoding<IntegerExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> pointerEncoding) {
    super(integerEncoding, booleanEncoding, arrayEncoding, pointerEncoding);
  }
}
