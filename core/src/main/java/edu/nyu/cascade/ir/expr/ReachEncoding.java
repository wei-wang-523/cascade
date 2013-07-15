package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public abstract class ReachEncoding extends AbstractExpressionEncoding {
  
  protected static final String NEXT_SELECTOR_NAME = "next_of";  
  protected static final String ELT_F_CONST = "next_cons";  
  protected static final String ELT_NIL_CONST = "nil_cons";
  protected static final String ELT_DATATYPE = "elt";
  
  protected static final String FUN_F = "f";
  protected static final String FUN_CYCLE = "cycle";
  protected static final String FUN_RF_AVOID = "rf_avoid";
  protected static final String FUN_JOIN = "join";
  protected static final String FUN_RF = "rf";
  
  public static final int DEFAULT_WORD_SIZE = 8;
  
  protected enum InstOpt{ // Partial quantifier instantiation option
    FIELD,
    ELEMENT,
    FIELD_OF_ELEMENT,
    ERROR;
  }
  
  public ReachEncoding(ExpressionManager exprManager) {
    super(BitVectorIntegerEncoding.create(exprManager, DEFAULT_WORD_SIZE),
        new DefaultBooleanEncoding(exprManager),
        new DefaultArrayEncoding(exprManager),
        new UnimplementedTupleEncoding<TupleExpression>());
  }
  
  protected InstOpt getInstOpt() {
    if(!Preferences.isSet(Preferences.OPTION_PARTIAL_INST))
      return InstOpt.ERROR;
    String opt = Preferences.getString(Preferences.OPTION_PARTIAL_INST);
    if(opt.equals("fld"))
      return InstOpt.FIELD;
    else if(opt.equals("elt"))
      return InstOpt.ELEMENT;
    else if(opt.equals("fld-of-elt"))
      return InstOpt.FIELD_OF_ELEMENT;
    else
      return InstOpt.ERROR;
  }

  public abstract Type getEltType() ;

  public abstract Expression getNil() ;
  
  public abstract Expression getEltExpr(Expression arg);
  
  public abstract void instGen(Iterable<? extends Expression> heapRegions) ;
  
  public abstract BooleanExpression assignReach(String field, Expression arg1, Expression arg2) ;
  
  public abstract void updateReach(String field, Expression arg1, Expression arg2) ;
  
  public abstract BooleanExpression isRoot(String field, Expression rootExpr) ;
  
  public abstract BooleanExpression reach(String field, Expression arg1, Expression arg2, Expression arg3) ;
  
}
