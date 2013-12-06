package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class PointerExpressionEncoding extends AbstractExpressionEncoding {
	
  public static PointerExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {
    IntegerEncoding<?> integerEncoding = null;
    if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    	integerEncoding = new DefaultIntegerEncoding(exprManager);
    } else {
    	integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    }
    
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    PointerSyncEncoding pointerEncoding = PointerSyncEncoding.create(exprManager, SizeTSize);
    return new PointerExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private PointerExpressionEncoding(
      IntegerEncoding<?> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerSyncEncoding pointerEncoding) {
    super(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
}
