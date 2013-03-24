package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.LISBQReachMemoryModel;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public abstract class LISBQReachEncoding extends AbstractExpressionEncoding {

  protected static final String FUN_F = "f";
  protected static final String FUN_RF = "rf";
  
  public static LISBQReachMemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    return LISBQReachMemoryModel.create(encoding, size, size);
  }
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  public LISBQReachEncoding(ExpressionManager exprManager) {
    super(BitVectorIntegerEncoding.create(exprManager, DEFAULT_WORD_SIZE),
        new DefaultBooleanEncoding(exprManager),
        new DefaultArrayEncoding(exprManager));
  }
  
  protected abstract Expression applyF(Expression arg) ;

  protected abstract BooleanExpression applyRf(Expression... args) ;

  public abstract Type getEltType() ;

  public abstract Expression getNil() ;
  
  public abstract void instGen(Iterable<Expression> gterms) ;
}
