package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an bitvector-to-bitvector array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TupleExpression;

public class IntExpressionFactory extends AbstractExpressionEncoding {
//  private static final String UNKNOWN_VARIABLE_NAME = "unknown";
//  private static final String MEMORY_ARRAY_VARIABLE_NAME = "m";
  
  public static IntExpressionFactory create(ExpressionManager exprManager) {
    IntegerEncoding<IntegerExpression> integerEncoding = new DefaultIntegerEncoding(exprManager);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    PointerEncoding<TupleExpression> tupleEncoding = new DefaultPointerEncoding(exprManager);
    return new IntExpressionFactory(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
//  private final VariableExpression<ArrayType<IntegerType,IntegerType>> memArray;
//  private final ArrayType<IntegerType,IntegerType> memArrayType;

  public IntExpressionFactory(
      IntegerEncoding<IntegerExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> tupleEncoding) {
    super(integerEncoding, booleanEncoding, arrayEncoding, tupleEncoding);
//    try {
//      IntegerType intType = exprManager.integerType();
//      memArrayType = exprManager.arrayType(intType, intType);
//      memArray = memArrayType.variable(MEMORY_ARRAY_VARIABLE_NAME, true);
//    } catch (TheoremProverException e) {
//      throw new ExpressionFactoryException(e);
//    }
  }
}
