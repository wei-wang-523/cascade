package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;

public class BitVectorExpressionEncoding
    extends
    AbstractExpressionEncoding {

  public static BitVectorExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    TupleEncoding<TupleExpression> tupleEncoding = new UnimplementedTupleEncoding<TupleExpression>();
    return new BitVectorExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
  private BitVectorExpressionEncoding(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      TupleEncoding<TupleExpression> tupleEncoding)
  {
    super(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
}
