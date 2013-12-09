package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public class PointerExpressionEncoding extends AbstractExpressionEncoding {
	
  public static PointerExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {   
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    
    UninterpretedEncoding<UninterpretedExpression> uninterpretedEncoding = 
    		new DefaultUninterpretedEncoding(exprManager, Identifiers.REF_TYPE_NAME);
    
    IntegerEncoding<?> integerEncoding = null;
    PointerEncoding<TupleExpression> pointerEncoding = null;
    
    if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    	integerEncoding = new DefaultIntegerEncoding(exprManager);
    	pointerEncoding = DefaultPointerEncoding.create(
    			new DefaultTupleEncoding(exprManager).getInstance(
    					Identifiers.PTR_TYPE_NAME, uninterpretedEncoding, integerEncoding));
    } else {
    	integerEncoding = BitVectorIntegerEncoding.create(exprManager, cAnalyzer, WORD_SIZE);
    	IntegerEncoding<?> offsetEncoding = BitVectorOffsetEncoding.create(exprManager, 
    			(BitVectorIntegerEncoding) integerEncoding);
    	pointerEncoding = DefaultPointerEncoding.create(
    			new DefaultTupleEncoding(exprManager).getInstance(
    					Identifiers.PTR_TYPE_NAME, uninterpretedEncoding, offsetEncoding));
    }

    return new PointerExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private PointerExpressionEncoding(
      IntegerEncoding<?> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> pointerEncoding) {
    super(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
}
