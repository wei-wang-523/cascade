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
        Preferences.isSet(Preferences.OPTION_THEORY) ? 
            Preferences.get(Preferences.OPTION_THEORY).equals(
                Preferences.OPTION_THEORY_BURSTALLFIX) ? 
                DefaultSize
                : Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
                    Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
                    : DefaultSize
                    : Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
                        Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
                        : DefaultSize;

    int intCellSize = 
        Preferences.isSet(Preferences.OPTION_THEORY) ?
            Preferences.get(Preferences.OPTION_THEORY).equals(
                Preferences.OPTION_THEORY_BURSTALLFIX) ?
                (int) (cAnalyzer.getSize(xtc.type.NumberT.INT) * cellSize) 
                : cellSize
                : cellSize;
    
    CellSize = intCellSize;
    
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
  
  @Override
  public int getCellSize() {
    return CellSize;
  }
}
