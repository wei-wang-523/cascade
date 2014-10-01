package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class BitVectorExpressionEncoding
    extends
    AbstractExpressionEncoding {
	
  public static BitVectorExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, WORD_SIZE);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    
		long size = WORD_SIZE;
		
		if( Preferences.isSet(Preferences.OPTION_BYTE_BASED) ) {
			size = CType.getSizeofType(new PointerT(new VoidT())) * WORD_SIZE;
		}
  	
    PointerEncoding<? extends Expression> pointerEncoding = LinearPointerEncoding.create(
    		BitVectorFixedSizeEncoding.create(exprManager, (BitVectorIntegerEncoding) integerEncoding, size));
    return new BitVectorExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private BitVectorExpressionEncoding(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<? extends Expression> pointerEncoding)
  {
    super(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
}
