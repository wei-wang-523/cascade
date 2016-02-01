/**
 * 
 */
package edu.nyu.cascade.c;

import java.util.List;
import xtc.type.*;
import xtc.tree.*;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.impl.VarInfoFactory;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;

class CExpressionMemCheckEncoder implements ExpressionEncoder {
  private static final String TYPE = xtc.Constants.TYPE;
  private static final String VAR_PREFIX = "addr_of_";
  
  @SuppressWarnings("unused")
  private class ExpressionVisitor extends Visitor {
    private final StateExpression currState;
    private final LvalVisitor lvalVisitor;
    
    public ExpressionVisitor(StateExpression pre) {
      currState = pre;
      lvalVisitor = new LvalVisitor(this);
    }
    
    private Pair<BooleanExpression, BooleanExpression> toBoolean(Node node, boolean negated) {
      return encodeBoolean(node,negated);
    }
    
		private Pair<Expression, BooleanExpression> toExpression(Node node) {
			return encodeExpression(node);
		}

    private Pair<BooleanExpression, BooleanExpression> encodeBoolean(Node node) {
      return encodeBoolean(node, false);
    }
    
    private Pair<BooleanExpression, BooleanExpression> encodeBoolean(Node node, boolean negated) {
    	@SuppressWarnings("unchecked")
			Pair<Expression, BooleanExpression> pair = (Pair<Expression, BooleanExpression>) dispatch(node);
    	BooleanExpression b = coerceToBoolean(pair.fst());
      return Pair.of(negated ? b.not() : b, pair.snd());
    }
    
    private Pair<Expression, BooleanExpression> encodeExpression(Node node) {
      @SuppressWarnings("unchecked")
			Pair<Expression, BooleanExpression> pair = (Pair<Expression, BooleanExpression>) dispatch(node);
      return pair;
    }

    private BooleanExpression coerceToBoolean(Expression e) {      
      return encoding.isBoolean(e) ? e.asBooleanExpression() : encoding.castToBoolean(e).asBooleanExpression();
    }
    
    private Expression coerceToInteger(Expression e) {       
    	return encoding.isInteger(e) ? e : encoding.castToInteger(e);
    }
    
    private Expression coerceToPointer(Expression e) {
    	return encoding.isPointer(e) ? e : encoding.castToPointer(e);
    }
    
    @Override
    public Pair<Expression, BooleanExpression> unableToVisit(Node node) {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as unknown: "
                  + node.getName());
      Expression unknown = encoding.unknown(CType.getType(node));
      BooleanExpression tt = encoding.tt().asBooleanExpression();
      return Pair.of(unknown, tt);
    }
    
    public Pair<Expression, BooleanExpression> visitConditionalExpression(GNode node) {
      Pair<BooleanExpression, BooleanExpression> pair0 = encodeBoolean(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      BooleanExpression condition = pair0.fst();
      Expression trueCase = pair1.fst();
      Expression falseCase = pair2.fst();
      
      BooleanExpression memSafe0 = pair0.snd();
      BooleanExpression memSafe1 = pair1.snd();
      BooleanExpression memSafe2 = pair2.snd();
      
    	Type targetType = CType.getType(node);
      if(targetType.isPointer()) {
      	trueCase = encoding.castToPointer(trueCase);
      	falseCase = encoding.castToPointer(falseCase);
      } else {
      	int size = (int) encoding.getCTypeAnalyzer().getWidth(targetType);
      	trueCase = encoding.castToInteger(trueCase, size, !CType.isUnsigned(CType.getType(node.getNode(1))));
      	falseCase = encoding.castToInteger(falseCase, size, !CType.isUnsigned(CType.getType(node.getNode(2))));
      }
      
      Expression expr = encoding.ifThenElse(condition, trueCase, falseCase);
      
      BooleanExpression memSafe = memSafe0.and(condition.ifThenElse(memSafe1, memSafe2));
      
      return Pair.of(expr, memSafe);
    }

    public Pair<Expression, BooleanExpression> visitAdditiveExpression(GNode node) {
      // FIXED: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
      
    	String additiveOp = node.getString(1);
    	if (!("+".equals(additiveOp) || "-".equals(additiveOp))) 
    		throw new ExpressionFactoryException("Invalid operation: " + additiveOp);
    	
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
    	Expression left = pair0.fst(), right = pair2.fst();
    	
      Type lhsType = CType.getType(node.getNode(0)).resolve();
      Type rhsType = CType.getType(node.getNode(2)).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
      
      if(isLhsPointer || isRhsPointer) {
        if ("+".equals(additiveOp))		return Pair.of(pointerPlus(left, right, lhsType, rhsType), memSafe);
        else													return Pair.of(pointerMinus(left, right, lhsType, rhsType), memSafe);
      } else {
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	if ("+".equals(additiveOp)) 	return Pair.of(encoding.plus(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	else													return Pair.of(encoding.minus(coerceToInteger(left), coerceToInteger(right)), memSafe);
      }
    }
    
    public Pair<Expression, BooleanExpression> visitShiftExpression(GNode node) {
    	String shiftOp = node.getString(1);
    	if (!("<<".equals(shiftOp) || ">>".equals(shiftOp)))
    		throw new ExpressionFactoryException("Invalid operation: " + shiftOp);
    	
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(2));
    	
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
      
      Expression left = pair0.fst(), right = pair2.fst();
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	
    	if ("<<".equals(shiftOp))
    		return Pair.of(encoding.lshift(coerceToInteger(left), coerceToInteger(right)), memSafe);
    	
    	if(CType.isUnsigned(CType.getType(node.getNode(0))))
    		return Pair.of(encoding.rshift(coerceToInteger(left), coerceToInteger(right)), memSafe);
    	else
    		return Pair.of(encoding.signedRshift(coerceToInteger(left), coerceToInteger(right)), memSafe);
    }

    public Pair<Expression, BooleanExpression> visitAddressExpression(GNode node) {
      return lvalVisitor.encodeExpression(node.getNode(0));
    }

    public Pair<Expression, BooleanExpression> visitAssignmentExpression(GNode node) {
      /*
       * Note we are interpreting the assignment here as an expression, not as a
       * statement. I.e., we just need to return the RHS value. For
       * operator-assignment expressions we will return the expression
       * representation the operation. E.g., for a += b we return a + b, etc.
       */

    	String assignOp = node.getString(1);
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
      
      Expression left = pair0.fst(), right = pair2.fst();
    	
      Type lhsType = CType.getType(node.getNode(0)).resolve();
      Type rhsType = CType.getType(node.getNode(2)).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
    	
      if ("=".equals(assignOp)) 	return Pair.of(right, memSafe);
      if ("+=".equals(assignOp))	{
      	if(isLhsPointer || isRhsPointer) {
      		return Pair.of(pointerPlus(left, right, lhsType, rhsType), memSafe);
      	} else {
        	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
        	left = pair.fst(); right = pair.snd();
        	return Pair.of(encoding.plus(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	}
      }
      if ("-=".equals(assignOp)) 	{
      	if(isLhsPointer || isRhsPointer) {
      		return Pair.of(pointerMinus(left, right, lhsType, rhsType), memSafe);
      	} else {
        	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
        	left = pair.fst(); right = pair.snd();
        	return Pair.of(encoding.minus(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	}
      }
      if ("*=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return Pair.of(encoding.times(coerceToInteger(left), coerceToInteger(right)), memSafe);
      }
      
    	boolean isUnsigned = CType.isUnsigned(lhsType) || CType.isUnsigned(rhsType);
    	
      if ("/=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return Pair.of(encoding.divide(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	else
      		return Pair.of(encoding.signedDivide(coerceToInteger(left), coerceToInteger(right)), memSafe);
      }
      if ("%=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return Pair.of(encoding.rem(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	else
      		return Pair.of(encoding.signedRem(coerceToInteger(left), coerceToInteger(right)), memSafe);
      }
      if ("|=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return Pair.of(encoding.bitwiseOr(left, right), memSafe);
      }
      if ("&=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return Pair.of(encoding.bitwiseAnd(left, right), memSafe);
      }
      if ("^=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return Pair.of(encoding.bitwiseXor(left,  right), memSafe);
      }
      
      throw new ExpressionFactoryException("Invalid operation: " + assignOp);
    }

    public Pair<Expression, BooleanExpression> visitBitwiseAndExpression(GNode node) {
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
      BooleanExpression memSafe =  pair0.snd().and(pair1.snd());
      Expression left = pair0.fst(), right = pair1.fst();
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return Pair.of(encoding.bitwiseAnd(left, right), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitBitwiseOrExpression(GNode node) {
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
      BooleanExpression memSafe =  pair0.snd().and(pair1.snd());
      Expression left = pair0.fst(), right = pair1.fst();
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return Pair.of(encoding.bitwiseOr(left, right), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitBitwiseXorExpression(GNode node) {
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
      BooleanExpression memSafe =  pair0.snd().and(pair1.snd());
      Expression left = pair0.fst(), right = pair1.fst();
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return Pair.of(encoding.bitwiseXor(left, right), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitBitwiseNegationExpression(GNode node) {
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
    	Expression src = pair0.fst();
    	BooleanExpression memSafe = pair0.snd();
    	
    	return Pair.of(encoding.bitwiseNegate(src), memSafe);
    }

    public Pair<Expression, BooleanExpression> visitCastExpression(GNode node) {
      Type targetType = CType.getType(node).resolve();
      Type srcType = CType.getType(node.getNode(1));
      
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
    	Expression src = pair1.fst();
    	BooleanExpression memSafe = pair1.snd();
    	
    	Expression castSrcExpr;
      if(targetType.isPointer()) {
      	castSrcExpr = encoding.castToPointer(src);
      } else {
      	int size = (int) encoding.getCTypeAnalyzer().getWidth(targetType);
      	castSrcExpr = encoding.castToInteger(src, size, !CType.isUnsigned(srcType));
      }
      return Pair.of(castSrcExpr, memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitCharacterConstant(GNode node) {
      Type srcType = CType.getType(node);
      int asciiValue = srcType.getConstant().bigIntValue().intValue();
      int num = Character.getNumericValue(asciiValue);
      Expression constExpr = encoding.characterConstant(num);
      return Pair.of(constExpr, encoding.tt().asBooleanExpression());
    }

    public Pair<Expression, BooleanExpression> visitEqualityExpression(GNode node) {
    	String eqOp = node.getString(1);
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(2));
      
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
      Expression left = pair0.fst(), right = pair2.fst();
    	
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      left = pair.fst(); right = pair.snd();
    	
    	if ("==".equals(eqOp)) return Pair.of(encoding.eq(left, right), memSafe);
      if ("!=".equals(eqOp)) return Pair.of(encoding.neq(left, right), memSafe);
      
      throw new ExpressionFactoryException("Invalid operation: " + eqOp);
    }

    public List<Pair<Expression, BooleanExpression>> visitExpressionList(GNode node) {
      List<Pair<Expression, BooleanExpression>> subExprList = Lists.newArrayListWithCapacity(node.size());
      for (Object elem : node) {
        Pair<Expression, BooleanExpression> subPair = encodeExpression(GNode.cast(elem));
        subExprList.add(subPair);
      }
      return subExprList;
    }

    public Pair<Expression, BooleanExpression> visitFunctionCall(GNode node) {
      Node funNode = node.getNode(0);
      Preconditions.checkArgument(funNode.hasName("PrimaryIdentifier"));
      
      String name = funNode.getString(0);
      Node argList = node.getNode(1);
      
      if( ReservedFunction.FUN_VALID_ACCESS.equals(name) ) {
        assert(argList.size() == 2 || argList.size() == 1);
        Node ptrNode = argList.getNode(0);
        
        if(argList.size() == 1) {
        	Pair<Expression, BooleanExpression> ptrPair = lvalVisitor.encodeExpression(ptrNode);
        	Expression ptr = ptrPair.fst();
        	BooleanExpression memSafe = ptrPair.snd();
        	
        	Expression validAccess = stateFactory.validAccess(currState, ptr, ptrNode);
          return Pair.of(validAccess, memSafe);
        } else {
        	Pair<Expression, BooleanExpression> ptrPair = lvalVisitor.encodeExpression(ptrNode);
        	Pair<Expression, BooleanExpression> rangePair = encodeExpression(argList.getNode(1));
        	
        	Expression ptr = ptrPair.fst(), range = rangePair.fst();
        	BooleanExpression memSafe = ptrPair.snd().and(rangePair.snd());        	
        	Expression validAccessRange = stateFactory.validAccessRange(currState, ptr, range, ptrNode);
          return Pair.of(validAccessRange, memSafe);
        }
      } 
      
      if( ReservedFunction.FUN_VALID_MALLOC.equals(name)) {
        assert(argList.size() == 2);
        Node ptrNode = argList.getNode(0);
        
      	Pair<Expression, BooleanExpression> regionPair = encodeExpression(ptrNode);
      	Pair<Expression, BooleanExpression> sizePair = encodeExpression(argList.getNode(1));
      	
      	Expression region = regionPair.fst(), size = sizePair.fst();
      	BooleanExpression memSafe = regionPair.snd().and(sizePair.snd());
      	
        Expression validMalloc = stateFactory.applyValidMalloc(currState, region, size, ptrNode);
        return Pair.of(validMalloc, memSafe);
      } 
      
      if( ReservedFunction.FUN_VALID_FREE.equals(name)) {
        Preconditions.checkArgument(argList.size() == 1);
        Node ptrNode = argList.getNode(0);
        
        Pair<Expression, BooleanExpression> regionPair = encodeExpression(ptrNode);
        Expression region = regionPair.fst();
        BooleanExpression memSafe = regionPair.snd();
        
        Expression validFree = stateFactory.applyValidFree(currState, region, ptrNode);
        return Pair.of(validFree, memSafe);
      } 

      if( ReservedFunction.FUN_IMPLIES.equals(name) ) {
        assert(argList.size() == 2);
        Pair<Expression, BooleanExpression> pair0 = encodeExpression(argList.getNode(0));
      	Pair<Expression, BooleanExpression> pair1 = encodeExpression(argList.getNode(1));
      	
      	Expression assump = pair0.fst(), assertion = pair1.fst();
      	BooleanExpression memSafe = pair0.snd().and(pair1.snd());
      	
        return Pair.of(encoding.implies(assump, assertion), memSafe);
      } 

      if( ReservedFunction.FUN_FORALL.equals(name) || ReservedFunction.FUN_EXISTS.equals(name)) {
        ImmutableList.Builder<Expression> argsBuilder = new ImmutableList.Builder<Expression>();
        int lastIdx = argList.size()-1;
        for(int idx = 0; idx < lastIdx; idx++) {
          GNode argNode = argList.getGeneric(idx);
          assert(argNode.hasName("PrimaryIdentifier"));
          IRVarInfo info = createCtrlVar(argNode);
          String tpProviderName = encoding.getExpressionManager()
          		.getTheoremProver().getProviderName();
          
          Expression boundVar;
          if(Preferences.PROVER_Z3.equals(tpProviderName)) {
          	boundVar = getBoundVarExpr(idx, info);
          } else {
          	boundVar = getBoundVarExpr(info);
          }
          info.setRValBinding(boundVar);
          argsBuilder.add(boundVar);
        }
        
        Pair<BooleanExpression, BooleanExpression> lastPair = encodeBoolean(argList.getGeneric(lastIdx));
        BooleanExpression body = lastPair.fst();
        BooleanExpression memSafe = lastPair.snd();
        
        Expression res;
        if( ReservedFunction.FUN_FORALL.equals(name) )
          res = encoding.forall(argsBuilder.build(), body);
        else
          res = encoding.exists(argsBuilder.build(), body);
        
        return Pair.of(res, memSafe);
      } 

      if(argList != null) visitExpressionList(GNode.cast(argList));
      
      IOUtils.debug()
      .pln(
          "APPROX: Treating un-inlined function call " + node + " as unknown" );
      	
      return Pair.of(
      		encoding.unknown(CType.getType(node)), encoding.tt().asBooleanExpression());
    }

    public Pair<Expression, BooleanExpression> visitIndirectionExpression(GNode node) {
      Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Expression op = pair0.fst();
      BooleanExpression memSafe0 = pair0.snd();
      
      Pair<Expression, BooleanExpression> derefPair = derefMemory(currState, 
      		op, node, CType.getType(node));
      BooleanExpression memSafe = memSafe0.and(derefPair.snd());
      return Pair.of(derefPair.fst(), memSafe);
    }

    public Pair<Expression, BooleanExpression> visitIntegerConstant(GNode node) {
      BooleanExpression memSafe = encoding.tt().asBooleanExpression();
      String numStr = node.getString(0);
      Type srcType = encoding.getCTypeAnalyzer().typeInteger(numStr);
      
      boolean isUnsigned = CType.isUnsigned(srcType);
      Expression value = encoding.integerConstant(
      		srcType.getConstant().bigIntValue());
      
      Type targetType = CType.getType(node);
      int size = (int) encoding.getCTypeAnalyzer().getWidth(targetType);
      
      Expression valuePrime = encoding.castToInteger(value, size, !isUnsigned);
      return Pair.of(valuePrime, memSafe);
    }

    public Pair<Expression, BooleanExpression> visitLogicalAndExpression(GNode node) {
      Pair<BooleanExpression, BooleanExpression> pair0 = encodeBoolean(node.getNode(0));
      Pair<BooleanExpression, BooleanExpression> pair1 = encodeBoolean(node.getNode(1));
      
      BooleanExpression memSafe0 = pair0.snd();
      BooleanExpression memSafe1 = pair1.snd();
      BooleanExpression left = pair0.fst(), right = pair1.fst();
      
      BooleanExpression memSafe = memSafe0.and(left.implies(memSafe1));
      return Pair.of(encoding.and(left, right), memSafe);
    }

    public Pair<BooleanExpression, BooleanExpression> visitLogicalNegationExpression(GNode node) {
      return encodeBoolean(node.getNode(0), true);
    }

    public Pair<Expression, BooleanExpression> visitLogicalOrExpression(GNode node) {
      Pair<BooleanExpression, BooleanExpression> pair0 = encodeBoolean(node.getNode(0));
      Pair<BooleanExpression, BooleanExpression> pair1 = encodeBoolean(node.getNode(1));
      
      BooleanExpression memSafe0 = pair0.snd(), memSafe1 = pair1.snd();
      BooleanExpression left = pair0.fst(), right = pair1.fst();
      
      BooleanExpression memSafe = memSafe0.and(left.not().implies(memSafe1));
      return Pair.of(encoding.or(left, right), memSafe);
    }

    public Pair<Expression, BooleanExpression> visitPreincrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Pair<Expression, BooleanExpression> visitPredecrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }
    
    public Pair<Expression, BooleanExpression> visitPostincrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Pair<Expression, BooleanExpression> visitPostdecrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Pair<Expression, BooleanExpression> visitPrimaryIdentifier(GNode node) {
    	IRVarInfo info = lookupVar(node);
    	Type type = info.getXtcType();
    	
    	if(type.isEnumerator()) {
    		int index = type.getConstant().bigIntValue().intValue();
      	return Pair.of(encoding.integerConstant(index), encoding.tt().asBooleanExpression());
    	}
    	
    	Expression lBinding = info.getLValBinding();
    	return derefMemory(currState, lBinding, node, type);
    }

    public Pair<Expression, BooleanExpression> visitRelationalExpression(GNode node) {
    	String relOp = node.getString(1);
    	if(!(">".equals(relOp) || ">=".equals(relOp) || "<".equals(relOp) || "<=".equals(relOp)))
    		throw new ExpressionFactoryException("Invalid operation: " + relOp);
    	
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
    	Expression left = pair0.fst(), right = pair2.fst();
    	
      Type lType = CType.getType(node.getNode(0)).resolve();
      Type rType = CType.getType(node.getNode(2)).resolve();
      
    	if(lType.isPointer()) {
    		assert rType.isPointer();
    		Expression res;
        if (">".equals(relOp))	
        	res = encoding.pointerGreaterThan(left, right);
        else if (">=".equals(relOp))
        	res = encoding.pointerGreaterThanOrEqual(left, right);
        else if ("<".equals(relOp))
        	res = encoding.pointerLessThan(left, right);
        else
        	res = encoding.pointerLessThanOrEqual(left, right);
        
        return Pair.of(res, memSafe);
    	}
    	
      boolean isUnsigned = CType.isUnsigned(lType) || CType.isUnsigned(rType);
      
      Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lType, rType);
      left = pair.fst(); right = pair.snd();
      
    	if(isUnsigned) {
    		Expression res;
        if (">".equals(relOp))				res = encoding.greaterThan(left, right);
        else if (">=".equals(relOp)) 	res = encoding.greaterThanOrEqual(left, right);
        else if ("<".equals(relOp)) 	res = encoding.lessThan(left, right);
        else													res = encoding.lessThanOrEqual(left, right);
        
        return Pair.of(res, memSafe);
    	} else {
    		Expression res;
        if (">".equals(relOp))				res = encoding.signedGreaterThan(left, right);
        else if (">=".equals(relOp)) 	res = encoding.signedGreaterThanOrEqual(left, right);
        else if ("<".equals(relOp)) 	res = encoding.signedLessThan(left, right);
        else													res = encoding.signedLessThanOrEqual(left, right);
        
        return Pair.of(res, memSafe);
    	}
    }

    public Pair<Expression, BooleanExpression> visitSimpleDeclarator(GNode node) {
      return visitPrimaryIdentifier(node);
    }
    
    public Pair<Expression, BooleanExpression> visitSubscriptExpression(GNode node) {
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = encodeExpression(node.getNode(1));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
      BooleanExpression memSafe =  pair0.snd().and(pair1.snd());
    	Expression lhsExpr = pair0.fst(), rhsExpr = pair1.fst();
      Expression loc = pointerPlus(lhsExpr, rhsExpr, lhsType, rhsType);
      
      Pair<Expression, BooleanExpression> pair2 = derefMemory(currState, loc, node, CType.getType(node));
      memSafe = memSafe.and(pair2.snd());
      return Pair.of(pair2.fst(), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitSizeofExpression(GNode node) {
    	Node typeNode = node.getNode(0);
    	
      if(typeNode.hasProperty(TYPE)) { // pointer type (STRUCT *)
        long size = encoding.getCTypeAnalyzer().getSize(CType.getType(typeNode));
        return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
      } 
      
      if(typeNode.hasName("PrimaryIdentifier")){
        GNode typedef = GNode.create("TypedefName", typeNode.get(0));
        typedef.setLocation(node.getLocation());
        GNode specifier = GNode.create("SpecifierQualifierList", typedef);
        specifier.setLocation(node.getLocation());
        GNode typename = GNode.create("TypeName", specifier);
        typename.setLocation(node.getLocation());
        return encodeExpression(typename);
      }
      
      return encodeExpression(typeNode);
    }
    
    public Pair<Expression, BooleanExpression> visitTypeName(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Pair<Expression, BooleanExpression> visitSpecifierQualifierList(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Pair<Expression, BooleanExpression> visitInt(GNode node) {
      //FIXME: Int() and Char() won't be visited.
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }    
    
    public Pair<Expression, BooleanExpression> visitChar(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitPointer(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitStructureTypeReference(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitUnionTypeReference(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitTypedefName(GNode node) {
      if(Preferences.isSet(Preferences.OPTION_BYTE_BASED)) {
        return encodeExpression(node.getNode(0));
      } 
      
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return Pair.of(encoding.integerConstant(size), encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitUnaryMinusExpression(GNode node) {
      Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Expression rhs = pair0.fst();
      BooleanExpression memSafe = pair0.snd();
      return Pair.of(encoding.uminus(rhs), memSafe); 
    }
    
    public Pair<Expression, BooleanExpression> visitMultiplicativeExpression(final GNode node) {      
    	String mulOp = node.getString(1);
    	if(!("*".equals(mulOp) || "/".equals(mulOp) || "%".equals(mulOp)))
    		throw new ExpressionFactoryException("Invalid operation: " + mulOp);
    	
    	Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair2 = encodeExpression(node.getNode(2));
      
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(2));
      
      BooleanExpression memSafe =  pair0.snd().and(pair2.snd());
      Expression left = pair0.fst(), right = pair2.fst();
    	
      Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      left = pair.fst(); right = pair.snd();
      
      if ("*".equals(mulOp))
        return Pair.of(
        		encoding.times(coerceToInteger(left), coerceToInteger(right)), memSafe);
      
      boolean isUnsigned = CType.isUnsigned(lhsType) || CType.isUnsigned(rhsType);
      
      if ("/".equals(mulOp))
      	if(isUnsigned)
      		return Pair.of(
      				encoding.divide(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	else
      		return Pair.of(
      				encoding.signedDivide(coerceToInteger(left), coerceToInteger(right)), memSafe);
      
      else
      	if(isUnsigned)
      		return Pair.of(
      				encoding.rem(coerceToInteger(left), coerceToInteger(right)), memSafe);
      	else
      		return Pair.of(
      				encoding.signedRem(coerceToInteger(left), coerceToInteger(right)), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitDirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      
      Pair<Expression, BooleanExpression> pair0 = lvalVisitor.encodeExpression(node.getNode(0));
      Expression baseLoc = pair0.fst();
      BooleanExpression memSafe = pair0.snd();
      
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(
      		coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      
      Pair<Expression, BooleanExpression> pair1 = derefMemory(currState, resLoc, node, type);
      Expression res = pair1.fst();
      memSafe = memSafe.and(pair1.snd());
      
      return Pair.of(res, memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitIndirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      
      Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Expression baseLoc = pair0.fst();
      BooleanExpression memSafe = pair0.snd();
      
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(
      		coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      
      Pair<Expression, BooleanExpression> pair1 = derefMemory(currState, resLoc, node, type);
      Expression res = pair1.fst();
      memSafe = memSafe.and(pair1.snd());
      
      return Pair.of(res, memSafe);
    }

		private Pair<Expression, BooleanExpression> derefMemory(StateExpression state, 
				Expression lvalExpr, Node lvalNode, Type type) {
			Preconditions.checkArgument(!type.resolve().isVoid());
			
			if(!CType.isScalar(type.resolve()))
				return Pair.of(lvalExpr, encoding.tt().asBooleanExpression());
			
		  Expression resExpr = stateFactory.deref(state, lvalExpr, lvalNode);
		  BooleanExpression memSafe = stateFactory.validAccess(state, lvalExpr, lvalNode);
		  return Pair.of(resExpr, memSafe);
		}
		
		private Expression getBoundVarExpr(IRVarInfo varInfo) {
			Preconditions.checkArgument(varInfo.hasProperty(Identifiers.CTRLVAR));
			String name = varInfo.getName();
			IRType type = varInfo.getIRType();
			Expression iExpr = encoding.boundVar(name, type, false);
	    return iExpr;
		}
		
		private Expression getBoundVarExpr(int index, IRVarInfo varInfo) {
			Preconditions.checkArgument(varInfo.hasProperty(Identifiers.CTRLVAR));
			String name = varInfo.getName();
			IRType type = varInfo.getIRType();
			Expression iExpr = encoding.boundExpression(name, index, type, false);
	    return iExpr;
		}
		
		private IRVarInfo createCtrlVar(GNode node) {
	  	Preconditions.checkNotNull(currScope);
	    String name = node.getString(0);
			IRVarInfo varInfo = VarInfoFactory.createVarInfoWithNode(
					currScope.getQualifiedName(), name, node);
	  	varInfo.setProperty(Identifiers.CTRLVAR, true);
	  	currScope.define(name, varInfo);
	  	return varInfo;
		}
		
  	/**
     * Return the symbol table binding for a variable.
     */
    private IRVarInfo lookupVar(GNode node) {
    	Preconditions.checkNotNull(currScope);
      String name = node.getString(0);
      assert(name != null);
      IRVarInfo varInfo = (IRVarInfo) currScope.lookup(name);
      return varInfo;
    }
  }
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
    private final StateExpression currState;
    private final ExpressionVisitor exprVisitor;
    
    private LvalVisitor(StateExpression pre) {
      this.exprVisitor = new ExpressionVisitor(pre);
      this.currState = pre;
    }

    private LvalVisitor(ExpressionVisitor exprVisitor) {
      this.exprVisitor = exprVisitor;
      this.currState = exprVisitor.currState;
    }
    
		private Expression coerceToInteger(Expression e) {       
			return encoding.isInteger(e) ? e : encoding.castToInteger(e);
		}

		private Expression coerceToPointer(Expression e) {
			return encoding.isPointer(e) ? e : encoding.castToPointer(e);
		}
		
    private Pair<Expression, BooleanExpression> encodeExpression(Node node) {
      @SuppressWarnings("unchecked")
			Pair<Expression, BooleanExpression> pair = (Pair<Expression, BooleanExpression>) dispatch(node);
      return pair;
    }

    public Pair<Expression, BooleanExpression> toLval(Node node) {
      return encodeExpression(node);
    }
    
    public Pair<Expression, BooleanExpression> visitIndirectionExpression(GNode node) {
      return exprVisitor.encodeExpression(node.getNode(0));
    }

    public Pair<Expression, BooleanExpression> visitPrimaryIdentifier(GNode node) {
    	IRVarInfo info = exprVisitor.lookupVar(node);
    	assert(!info.hasProperty(Identifiers.CTRLVAR));
    	assert(info.hasLValBinding());
    	return Pair.of(info.getLValBinding(), encoding.tt().asBooleanExpression());
    }

    public Pair<Expression, BooleanExpression> visitSimpleDeclarator(GNode node) {
    	IRVarInfo info = exprVisitor.lookupVar(node);
    	
    	if(info.getXtcType().getShape().isStatic() && info.hasLValBinding()) 
    		return Pair.of(info.getLValBinding(), encoding.tt().asBooleanExpression());
    	
    	if(Preferences.isSet(Preferences.OPTION_HOARE)) {
    		boolean isHoare = (Boolean) info.getProperty(Identifiers.HOARE_VAR);
    		if(isHoare) {
      		Expression rValue = encoding.variable(info.getName(), info.getIRType(), true);
      		info.setRValBinding(rValue);
    		}
    	}
    	
    	Expression lValue = getLvalBinding(info);
    	info.setLValBinding(lValue);
    	return Pair.of(lValue, encoding.tt().asBooleanExpression());
    }
    
    public Pair<Expression, BooleanExpression> visitAdditiveExpression(GNode node) {
    	return exprVisitor.visitAdditiveExpression(node);
    }
    
    public Pair<Expression, BooleanExpression> visitSubscriptExpression(GNode node) {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      
      Pair<Expression, BooleanExpression> pair0 = exprVisitor.encodeExpression(node.getNode(0));
      Pair<Expression, BooleanExpression> pair1 = exprVisitor.encodeExpression(node.getNode(1));
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
      Expression base = pair0.fst(), index = pair1.fst();
      BooleanExpression memSafe = pair0.snd().and(pair1.snd());
      
      return Pair.of(pointerPlus(base, index, lhsType, rhsType), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitCastExpression(GNode node) {
    	return exprVisitor.visitCastExpression(node);
    }
    
    public Pair<Expression, BooleanExpression> visitDirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      
      Pair<Expression, BooleanExpression> pair0 = encodeExpression(node.getNode(0));
      Expression baseLoc = pair0.fst();
      BooleanExpression memSafe = pair0.snd();
      
      return Pair.of(encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr)), memSafe);
    }
    
    public Pair<Expression, BooleanExpression> visitFunctionCall(GNode node) {
      return exprVisitor.visitFunctionCall(node);
    }
    
    public Pair<Expression, BooleanExpression> visitIndirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      
      Pair<Expression, BooleanExpression> pair0 = exprVisitor.encodeExpression(node.getNode(0));
      Expression baseLoc = pair0.fst();
      BooleanExpression memSafe = pair0.snd();
      
      return Pair.of(encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr)), memSafe);
    }

    public Pair<Expression, BooleanExpression> visitParameterDeclaration(GNode node) {
      return encodeExpression(node.getNode(1));
    }
    
    public Pair<Expression, BooleanExpression> visitPointerDeclarator(GNode node) {
      return encodeExpression(node.getNode(1));
    }
    
    public Pair<Expression, BooleanExpression> visitIntegerConstant(GNode node) {
    	return exprVisitor.encodeExpression(node);
    }
    
    /**
  	 * Returns an expression representing the lvalue of the given name. I.e.,
  	 * <code>lookupVar(x)</code> will return an expression representing
  	 * <code>&x</code>. The rvalue of <code>x</code> is
  	 * <code>exprFactory.deref(lookupVar(x))</code>.
  	 * */
  	private Expression getLvalBinding(IRVarInfo varInfo) {
  		// TODO: map expressions per-factory
  		String addrName = VAR_PREFIX + varInfo.getName();
  		return stateFactory.getDataFormatter().getFreshPtr(addrName, true);
  	}
  }
  
  @Override
  public BooleanExpression toBoolean(StateExpression pre, Node node) {
    return toBoolean(pre, node, false);
  }

  @Override
  public BooleanExpression toBoolean(StateExpression pre, Node node, boolean negated) {
    Pair<BooleanExpression, BooleanExpression> pair = new ExpressionVisitor(pre).toBoolean(node,negated);
    pre.setPreAssertion(Identifiers.VALID_DEREF, pair.snd());
    return pair.fst();
  }

  @Override
  public Expression toExpression(StateExpression pre, Node node) {
    Pair<Expression, BooleanExpression> pair = new ExpressionVisitor(pre).toExpression(node);
    pre.setPreAssertion(Identifiers.VALID_DEREF, pair.snd());
    return pair.fst();
  }

  @Override
  public Expression toLval(StateExpression pre, Node node) {
  	Pair<Expression, BooleanExpression> pair = new LvalVisitor(pre).toLval(node);
    pre.setPreAssertion(Identifiers.VALID_DEREF, pair.snd());
    return pair.fst();
  }

  @Override
  public BooleanExpression toBoolean(StateExpression pre, Node node, Scope scope) {
    return toBoolean(pre, node,false,scope);
  }

  @Override
  public BooleanExpression toBoolean(StateExpression pre, Node node, boolean negated,
      Scope scope) {
    currScope = scope;
  	return toBoolean(pre, node,negated);
  }

  @Override
  public Expression toExpression(StateExpression pre, Node node, Scope scope) {
    currScope = scope;
  	return toExpression(pre, node);
  }

  @Override
  public Expression toLval(StateExpression pre, Node node, Scope scope) {
  	currScope = scope;
  	return toLval(pre, node);
  }

  public static CExpressionMemCheckEncoder create(
      Mode mode) {
  	ExpressionEncoding encoding = mode.getEncoding();
  	StateFactory<?> stateFactory = mode.getStateFactory();
  	
    IOUtils.debug().pln(
        "Creating CExpressionEncoder with encoding: " + encoding);
    return new CExpressionMemCheckEncoder(encoding, stateFactory);
  }
  
  private final ExpressionEncoding encoding;
  private Scope currScope;
  private final StateFactory<?> stateFactory;

  private CExpressionMemCheckEncoder(ExpressionEncoding encoding,
      StateFactory<?> stateFactory) {
    this.encoding = encoding;
    this.stateFactory = stateFactory;
  }
  
  @Override
	public ExpressionEncoding getEncoding() {
	  return encoding;
	}

	@Override
	public StateFactory<?> getStateFactory() {
	  return stateFactory;
	}
	
	@Override
	public SymbolTable.Scope getCurrentScope() {
		return currScope;
	}

	/**
	 * Pointer plus: T* ptr;
	 * 		ptr + i = ptr + sizeof(T) * i
	 * @param lhsType, Type rhsType 
	 */
	private Expression pointerPlus(Expression lhs, Expression rhs, Type lhsType, Type rhsType) {
		lhsType = lhsType.resolve();
		rhsType = rhsType.resolve();
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		
		if(lhsType.isPointer()) {
			Type ptoType = lhsType.toPointer().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    
	    /* cast factor the the rhsType to perform size * offset */
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(rhs, factor);
			return encoding.pointerPlus(lhs, addon);
		}
		
		if(lhsType.isArray()) {
			Type ptoType = lhsType.toArray().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    
	    /* cast factor the the rhsType to perform size * offset */
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(rhs, factor);
			return encoding.pointerPlus(lhs, addon);
		}
		
		if(rhsType.isPointer()) {
			Type ptoType = rhsType.toPointer().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    
	    /* cast factor the the lhsType to perform size * offset */
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(lhs, factor);
			return encoding.pointerPlus(rhs, addon);
		}
		
		if(rhsType.isArray()) {
			Type ptoType = rhsType.toArray().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    
	    /* cast factor the the lhsType to perform size * offset */
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(lhs, factor);
			return encoding.pointerPlus(rhs, addon);
		}
		
		throw new ExpressionFactoryException("Invalid operands");
	}

	/**
	 * Pointer minus: T* ptr;
	 * 		ptr - i = ptr - sizeof(T) * i
	 */
	private Expression pointerMinus(Expression lhs, Expression rhs, Type lhsType, Type rhsType) {
		lhsType = lhsType.resolve();
		rhsType = rhsType.resolve();
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		
		if(lhsType.isPointer()) {
			Type ptoType = lhsType.toPointer().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(rhs, factor);
			return encoding.pointerMinus(lhs, addon);
		}
		
		if(lhsType.isArray()) {
			Type ptoType = lhsType.toArray().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(rhs, factor);
			return encoding.pointerMinus(lhs, addon);
		}
	
		if(rhsType.isPointer()) {
			Type ptoType = rhsType.toPointer().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(lhs, factor);
			return encoding.pointerMinus(rhs, addon);
		}
		
		if(rhsType.isArray()) {
			Type ptoType = rhsType.toArray().getType();
	    long size = cTypeAnalyzer.getSize(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(lhs, factor);
			return encoding.pointerMinus(rhs, addon);
		}
		
		throw new ExpressionFactoryException("Invalid operands");
	}
}
