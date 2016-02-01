package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import xtc.type.NumberT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public class PointerExpressionEncoding extends AbstractExpressionEncoding {
	
  public static PointerExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {   
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    IntegerEncoding<?> integerEncoding = null;
  	PointerEncoding<?> pointerEncoding = null;
    
    if(Preferences.isSet(Preferences.OPTION_MEM_ENCODING) && 
    		Preferences.MEM_ENCODING_SYNC.equals(Preferences.get(Preferences.OPTION_MEM_ENCODING))) {
    	UninterpretedEncoding<UninterpretedExpression> uninterpretedEncoding = 
    			new DefaultUninterpretedEncoding(exprManager, Identifiers.REF_TYPE_NAME);
    
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		integerEncoding = new DefaultIntegerEncoding(exprManager);
    		pointerEncoding = SyncPointerEncoding.create(
    			new DefaultTupleEncoding(exprManager).getInstance(
    					Identifiers.PTR_TYPE_NAME, uninterpretedEncoding, integerEncoding));
    	} else {
    		integerEncoding = BitVectorIntegerEncoding.create(exprManager, WORD_SIZE);
    		
    		long offsetSize = WORD_SIZE;
    		
    		if( Preferences.isSet(Preferences.OPTION_BYTE_BASED) ) {
    			offsetSize = CType.getSizeofType(NumberT.LONG) * WORD_SIZE;
    		}
    		
    		IntegerEncoding<?> offsetEncoding = BitVectorFixedSizeEncoding.create(exprManager, 
    				(BitVectorIntegerEncoding) integerEncoding, offsetSize);
    		pointerEncoding = SyncPointerEncoding.create(
    				new DefaultTupleEncoding(exprManager).getInstance(
    						Identifiers.PTR_TYPE_NAME, uninterpretedEncoding, offsetEncoding));
    	}
    } else {
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		integerEncoding = new DefaultIntegerEncoding(exprManager);
    	} else {
    		integerEncoding = BitVectorIntegerEncoding.create(exprManager, WORD_SIZE);
    	}
  		pointerEncoding = LinearPointerEncoding.create(integerEncoding);
    }
    
    return new PointerExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private PointerExpressionEncoding(
      IntegerEncoding<?> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<?> pointerEncoding) {
    super(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
}
