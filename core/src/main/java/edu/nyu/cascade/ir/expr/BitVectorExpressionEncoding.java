package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.util.Preferences;

public class BitVectorExpressionEncoding
    extends
    AbstractExpressionEncoding {

  private static int CellSize;	
	
  public static BitVectorExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  {
    int cellSize = 
    		Preferences.ENCODING_FIX.equals(
    				Preferences.getString(Preferences.OPTION_EXPR_ENCODING)) ? 
    						DefaultSize
                : Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
                		Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
                    : DefaultSize;

    int intCellSize = 
    		Preferences.ENCODING_FIX.equals(
            Preferences.getString(Preferences.OPTION_EXPR_ENCODING)) ? 
                (int) (cAnalyzer.getSize(xtc.type.NumberT.INT) * cellSize) 
                : cellSize;
    
    CellSize = intCellSize;
    
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    PointerEncoding<TupleExpression> tupleEncoding = new UnimplementedPointerEncoding<TupleExpression>();
    return new BitVectorExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
  private BitVectorExpressionEncoding(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> tupleEncoding)
  {
    super(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
  }
  
  @Override
  public int getCellSize() {
    return CellSize;
  }
}
