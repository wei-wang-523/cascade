package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import java.util.Arrays;
import java.util.List;

import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.util.Preferences;

public class PointerExpressionEncoding extends AbstractExpressionEncoding {
  
  private static int CellSize;	
	
  public static PointerExpressionEncoding create(
      ExpressionManager exprManager) throws ExpressionFactoryException
  { 
    int cellSize = 
    		Preferences.isSet(Preferences.OPTION_MULTI_CELL) ? 
    				DefaultSize
    				: Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
    						Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
    						: DefaultSize;

    int offCellSize = 
    		Preferences.isSet(Preferences.OPTION_MULTI_CELL) ? 
    				(int) (cAnalyzer.getSize(xtc.type.NumberT.U_LONG) * cellSize) 
    				: cellSize;
    
    int intCellSize = 
    		Preferences.isSet(Preferences.OPTION_MULTI_CELL) ? 
    				(int) (cAnalyzer.getSize(xtc.type.NumberT.INT) * cellSize) 
    				: cellSize;
    
    CellSize = cellSize;
    
    IntegerEncoding<?> integerEncoding = null;
    if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    	integerEncoding = new DefaultIntegerEncoding(exprManager);
    } else {
    	integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    }
    
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    PointerSyncEncoding pointerEncoding = PointerSyncEncoding.create(exprManager, offCellSize);
    return new PointerExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private PointerExpressionEncoding(
      IntegerEncoding<?> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerSyncEncoding pointerEncoding)
  {
    super(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  public PointerSyncEncoding getPointerEncoding() {
    return (PointerSyncEncoding) pointerEncoding;
  }
  
  @Override
  public Expression castToBoolean(Expression expr) {
    if(expr.isTuple())
      return getPointerEncoding().castToBoolean(expr.asTuple());
    else
      return super.castToBoolean(expr);
  }
  
  @Override
  public Expression castToInteger(Expression expr) {
    if(expr.isTuple())
      return expr;
    else
      return super.castToInteger(expr);
  }
  
  @Override
  public Expression decr(Expression expr) {
    if(expr.isTuple())
      return getPointerEncoding().decr(expr.asTuple());
    else
      return super.decr(expr);
  }
  
  @Override
  public Expression incr(Expression expr) {
    if(expr.isTuple())
      return getPointerEncoding().incr(expr.asTuple());
    else
      return super.incr(expr);
  }
  
  public Expression index(Expression expr, int index) {
    return getPointerEncoding().index(expr.asTuple(), index);
  }
  
  @Override
  public Expression lessThan(Expression lhs, Expression rhs) {
    if(lhs.isTuple() && rhs.isTuple())
      return getPointerEncoding().lessThan(lhs.asTuple(), rhs.asTuple());
    else
      return super.lessThan(lhs, rhs);
  }
  
  @Override
  public Expression lessThanOrEqual(Expression lhs, Expression rhs) {
    if(lhs.isTuple() && rhs.isTuple())
      return getPointerEncoding().lessThanOrEqual(lhs.asTuple(), rhs.asTuple());
    else
      return super.lessThanOrEqual(lhs, rhs);
  }
  
  @Override
  public Expression greaterThan(Expression lhs, Expression rhs) {
    if(lhs.isTuple() && rhs.isTuple())
      return getPointerEncoding().greaterThan(lhs.asTuple(), rhs.asTuple());
    else
      return super.greaterThan(lhs, rhs);
  }
  
  @Override
  public Expression greaterThanOrEqual(Expression lhs, Expression rhs) {
    if(lhs.isTuple() && rhs.isTuple())
      return getPointerEncoding().greaterThanOrEqual(lhs.asTuple(), rhs.asTuple());
    else
      return super.greaterThanOrEqual(lhs, rhs);
  }
  
  @Override
  public Expression minus(Expression lhs, Expression rhs) {
    if(lhs.isTuple())
      return getPointerEncoding().minus(lhs.asTuple(), rhs);
    else
      return super.minus(lhs, rhs);
  }
  
  @Override
  public Expression neq(Expression lhs, Expression rhs) {
    if(lhs.isTuple() || rhs.isTuple()) {
      PointerSyncEncoding ptrEncoding = getPointerEncoding();
      if(!lhs.isTuple()) {
        assert(rhs.isConstant());
        lhs = ptrEncoding.getNullPtr();
      }
      if(!rhs.isTuple()) {
        assert(rhs.isConstant());
        rhs = ptrEncoding.getNullPtr();
      }
      return ptrEncoding.neq(lhs.asTuple(), rhs.asTuple());
    } else
      return super.neq(lhs, rhs);
  }
  
  @Override
  public Expression eq(Expression lhs, Expression rhs) {
    if(lhs.isTuple() || rhs.isTuple()) {
      PointerSyncEncoding ptrEncoding = getPointerEncoding();
      if(!lhs.isTuple()) {
        assert(rhs.isConstant());
        lhs = ptrEncoding.getNullPtr();
      }
      if(!rhs.isTuple()) {
        assert(rhs.isConstant());
        rhs = ptrEncoding.getNullPtr();
      }
      return getPointerEncoding().eq(lhs.asTuple(), rhs.asTuple());
    } else
      return super.eq(lhs, rhs);
  }
  
  @Override
  public Expression plus(Iterable<? extends Expression> exprs) {
    List<? extends Expression> args = Lists.newArrayList(exprs);
    if(args.get(0).isTuple()) {
      Expression first = args.remove(0);
      return getPointerEncoding().plus(first.asTuple(), args);
    } else {
      return super.plus(exprs);
    }
  }
  
  @Override
  public Expression plus(Expression... args)
  {
    return plus(Arrays.asList(args));
  }
  
  @Override
  public Expression plus(Expression lhs, Expression rhs) {
    if(lhs.isTuple())
      return getPointerEncoding().plus(lhs.asTuple(), rhs);
    else
      return super.plus(lhs, rhs);
  }
  
  public Expression unknown() {
    return getPointerEncoding().unknown();
  }
  
  @Override
  public int getCellSize() {
    return CellSize;
  }
  
  public Expression update(TupleExpression expr, int index, Expression val) {
    return getPointerEncoding().update(expr, index, val);
  }
}
