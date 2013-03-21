package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public abstract class LoLLiReachEncoding extends AbstractExpressionEncoding {

  protected static final String FUN_F = "f";
  
  protected static final String FUN_CYCLE = "cycle";

  protected static final String FUN_RF_AVOID = "rf_avoid";
  
  protected static final String FUN_JOIN = "join";
  
  public static LoLLiReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return LoLLiReachMemoryModel.create(encoding, size, size);
  }
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public LoLLiReachEncoding(ExpressionManager exprManager) {
    super(BitVectorIntegerEncoding.create(exprManager, DEFAULT_WORD_SIZE),
        new DefaultBooleanEncoding(exprManager),
        new DefaultArrayEncoding(exprManager));
  }

  protected abstract BooleanExpression applyCycle(Expression arg) ;
  
  protected abstract Expression applyF(Expression arg) ;
  
  protected abstract BooleanExpression applyRfAvoid(Expression... args) ;
  
  protected abstract Expression applyJoin(Expression... args) ;

  public abstract Type getEltType() ;

  public abstract Expression getNil() ;
}
