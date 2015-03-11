/**
 * 
 */
package edu.nyu.cascade.c;

import java.util.List;

import xtc.type.*;
import xtc.type.Type.Tag;
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

class CExpressionEncoder implements ExpressionEncoder {
  private static final String VAR_PREFIX = "addr_of_";
  
  @SuppressWarnings("unused")
  private class ExpressionVisitor extends Visitor {
    private final StateExpression currState;
    private final LvalVisitor lvalVisitor;
    
    public ExpressionVisitor(StateExpression pre) {
      currState = pre;
      lvalVisitor = new LvalVisitor(this);
    }
    
    private BooleanExpression toBoolean(Node node, boolean negated) {
      return encodeBoolean(node,negated);
    }
    
		private Expression toExpression(Node node) {
			return encodeExpression(node);
		}

    private BooleanExpression encodeBoolean(Node node) {
      return encodeBoolean(node, false);
    }
    
    private BooleanExpression encodeBoolean(Node node, boolean negated) {
    	BooleanExpression b = coerceToBoolean((Expression) dispatch(node));
      return negated ? b.not() : b;
    }
    
    private Expression encodeExpression(Node node) {
      return ((Expression) dispatch(node));
    }

    private BooleanExpression coerceToBoolean(Expression e) {      
      return encoding.isBoolean(e) ? 
      		e.asBooleanExpression() : 
      			encoding.castToBoolean(e).asBooleanExpression();
    }
    
    private Expression coerceToInteger(Expression e) {       
    	return encoding.isInteger(e) ? e : encoding.castToInteger(e);
    }
    
    private Expression coerceToPointer(Expression e) {
    	return encoding.isPointer(e) ? e : encoding.castToPointer(e);
    }
    
    @Override
    public Expression unableToVisit(Node node) {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as unknown: "
                  + node.getName());
      return encoding.getIntegerEncoding().unknown();
    }
    
    public Expression visitConditionalExpression(GNode node) {      
      BooleanExpression condition = encodeBoolean(node.getNode(0));
      Expression trueCase = encodeExpression(node.getNode(1));
      Expression falseCase = encodeExpression(node.getNode(2));
      
    	Type targetType = CType.getType(node);
      if(targetType.isPointer()) {
      	trueCase = encoding.castToPointer(trueCase);
      	falseCase = encoding.castToPointer(falseCase);
      } else {
      	int size = (int) encoding.getCTypeAnalyzer().getWidth(targetType);
      	trueCase = encoding.castToInteger(trueCase, size, !CType.isUnsigned(CType.getType(node.getNode(1))));
      	falseCase = encoding.castToInteger(falseCase, size, !CType.isUnsigned(CType.getType(node.getNode(2))));
      }
      
      return condition.ifThenElse(trueCase, falseCase);
    }

    public Expression visitAdditiveExpression(GNode node) {
      // FIXED: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      
    	String additiveOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lhsType = CType.getType(node.getNode(0)).resolve();
      Type rhsType = CType.getType(node.getNode(2)).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
      
      if(isLhsPointer || isRhsPointer) {
        if ("+".equals(additiveOp))		return pointerPlus(left, right, lhsType, rhsType);
        if ("-".equals(additiveOp)) 	return pointerMinus(left, right, lhsType, rhsType);
        throw new ExpressionFactoryException("Invalid operation: " + additiveOp);
      }
      
      Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      left = pair.fst(); right = pair.snd();
      
      if ("+".equals(additiveOp)) return encoding.plus(coerceToInteger(left), coerceToInteger(right));
      if ("-".equals(additiveOp)) return encoding.minus(coerceToInteger(left), coerceToInteger(right));
      throw new ExpressionFactoryException("Invalid operation: " + additiveOp);
    }
    
    public Expression visitShiftExpression(GNode node) {
    	String shiftOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lhsType = CType.getType(node.getNode(0)).resolve();
      Type rhsType = CType.getType(node.getNode(2)).resolve();
    	
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	
    	if ("<<".equals(shiftOp))
        return encoding.lshift(coerceToInteger(left), coerceToInteger(right));

      if (">>".equals(shiftOp))
      	if(CType.isUnsigned(CType.getType(node.getNode(0))))
      		return encoding.rshift(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedRshift(coerceToInteger(left), coerceToInteger(right));
      
      throw new ExpressionFactoryException("Invalid operation: " + shiftOp);
    }

    public Expression visitAddressExpression(GNode node) {
      return lvalVisitor.encodeExpression(node.getNode(0));
    }

    public Expression visitAssignmentExpression(GNode node) {
      /*
       * Note we are interpreting the assignment here as an expression, not as a
       * statement. I.e., we just need to return the RHS value. For
       * operator-assignment expressions we will return the expression
       * representation the operation. E.g., for a += b we return a + b, etc.
       */

    	String assignOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lhsType = CType.getType(node.getNode(0)).resolve();
      Type rhsType = CType.getType(node.getNode(2)).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
    	
      if ("=".equals(assignOp)) 	return right;
      if ("+=".equals(assignOp))	{
      	if(isLhsPointer || isRhsPointer) {
      		return pointerPlus(left, right, lhsType, rhsType);
      	} else {
        	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
        	left = pair.fst(); right = pair.snd();
        	return encoding.plus(coerceToInteger(left), coerceToInteger(right));
      	}
      }
      if ("-=".equals(assignOp)) 	{
      	if(isLhsPointer || isRhsPointer) {
      		return pointerMinus(left, right, lhsType, rhsType);
      	} else {
        	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
        	left = pair.fst(); right = pair.snd();
        	return encoding.minus(coerceToInteger(left), coerceToInteger(right));
      	}
      }
      if ("*=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return encoding.times(coerceToInteger(left), coerceToInteger(right));
      }
      
    	boolean isUnsigned = CType.isUnsigned(lhsType) || CType.isUnsigned(rhsType);
    	
      if ("/=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return encoding.divide(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedDivide(coerceToInteger(left), coerceToInteger(right));
      }
      if ("%=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return encoding.rem(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedRem(coerceToInteger(left), coerceToInteger(right));
      }
      if ("|=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseOr(left, right);
      }
      if ("&=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseAnd(left, right);
      }
      if ("^=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseXor(left,  right);
      }
      
      throw new ExpressionFactoryException("Invalid operation: " + assignOp);
    }

    public Expression visitBitwiseAndExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseAnd(left, right);
    }
    
    public Expression visitBitwiseOrExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseOr(left, right);
    }
    
    public Expression visitBitwiseXorExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(1));
      
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseXor(left, right);
    }
    
    public Expression visitBitwiseNegationExpression(GNode node) {
    	Expression src = encodeExpression(node.getNode(0));
    	return encoding.bitwiseNegate(src);
    }

    public Expression visitCastExpression(GNode node) {
      Type targetType = CType.getType(node).resolve();
      Type srcType = CType.getType(node.getNode(1));
      
      Expression src = encodeExpression(node.getNode(1));
      if(targetType.isPointer()) return encoding.castToPointer(src);
      
      int size = (int) encoding.getCTypeAnalyzer().getWidth(targetType);
      return encoding.castToInteger(src, size, !CType.isUnsigned(srcType));
    }
    
    public Expression visitCharacterConstant(GNode node) {
      Type srcType = CType.getType(node);
      int asciiValue = srcType.getConstant().bigIntValue().intValue();
      int num = Character.getNumericValue(asciiValue);
      return encoding.characterConstant(num);
    }

    public Expression visitEqualityExpression(GNode node) {
    	String eqOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
    	Type lhsType = CType.getType(node.getNode(0));
    	Type rhsType = CType.getType(node.getNode(2));
    	
    	Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      left = pair.fst(); right = pair.snd();
    	
    	if ("==".equals(eqOp)) return encoding.eq(left, right);
      if ("!=".equals(eqOp)) return encoding.neq(left, right);
      
      throw new ExpressionFactoryException("Invalid operation: " + eqOp);
    }

    public List<Expression> visitExpressionList(GNode node) {
      List<Expression> subExprList = Lists.newArrayListWithCapacity(node.size());
      for (Object elem : node) {
        Expression subExpr = encodeExpression(GNode.cast(elem));
        subExprList.add(subExpr);
      }
      return subExprList;
    }

    public Expression visitFunctionCall(GNode node) {
      Node funNode = node.getNode(0);
      Preconditions.checkArgument(funNode.hasName("PrimaryIdentifier"));
      
      String name = funNode.getString(0);
      Node argList = node.getNode(1);
      
      if( ReservedFunction.FUN_VALID_ACCESS.equals(name) ) {
        assert(argList.size() == 2 || argList.size() == 1);
        Node ptrNode = argList.getNode(0);
        Expression ptr = lvalVisitor.encodeExpression(ptrNode);
        
        if(argList.size() == 1) {
          return stateFactory.validAccess(currState, ptr, ptrNode);
        } else {
        	Expression range = encodeExpression(argList.getNode(1));
          return stateFactory.validAccessRange(currState, ptr, range, ptrNode);
        }
      } 
      
      if( ReservedFunction.FUN_VALID_MALLOC.equals(name)) {
        Preconditions.checkArgument(argList.size() == 2);
        Node ptrNode = argList.getNode(0);
        Expression region = encodeExpression(ptrNode);
        
        Expression size = encodeExpression(argList.getNode(1));
        return stateFactory.applyValidMalloc(currState, region, size, ptrNode);
      } 
      
      if( ReservedFunction.FUN_VALID_FREE.equals(name)) {
        Preconditions.checkArgument(argList.size() == 1);
        Node ptrNode = argList.getNode(0);
        Expression region = encodeExpression(ptrNode);
        
        return stateFactory.applyValidFree(currState, region, ptrNode);
      } 

      if( ReservedFunction.FUN_IMPLIES.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2);
        Expression assump = encodeExpression(argList.getNode(0));
        Expression assertion = encodeExpression(argList.getNode(1));
        return encoding.implies(assump, assertion);
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
          argsBuilder.add(boundVar);
        }
        
        Expression body = encodeBoolean(argList.getGeneric(lastIdx));

        if( ReservedFunction.FUN_FORALL.equals(name) )
          return encoding.forall(argsBuilder.build(), body);
        else
          return encoding.exists(argsBuilder.build(), body);
      } 

      if(argList != null) visitExpressionList(GNode.cast(argList));
      
      IOUtils.debug()
      .pln(
          "APPROX: Treating un-inlined function call " + node + " as unknown" );
      	
      return encoding.unknown(CType.getType(node));
    }

    public Expression visitIndirectionExpression(GNode node) {
      Expression op = encodeExpression(node.getNode(0));
      return derefMemory(currState, op, node, CType.getType(node));
    }

    public Expression visitIntegerConstant(GNode node) {
      Type srcType = CType.getType(node);
      Expression value = encoding.integerConstant(
      		srcType.getConstant().bigIntValue());
      return value;
    }

    public Expression visitLogicalAndExpression(GNode node) {
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.and(left, right);
    }

    public Expression visitLogicalNegationExpression(GNode node) {
      return encodeBoolean(node.getNode(0), true);
    }

    public Expression visitLogicalOrExpression(GNode node) {
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.or(left, right);
    }

    public Expression visitPreincrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPredecrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }
    
    public Expression visitPostincrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPostdecrementExpression(GNode node) {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPrimaryIdentifier(GNode node) {
    	IRVarInfo info = lookupVar(node);
  		Type xtcType = info.getXtcType();
  		
    	if(xtcType.isEnumerator()) {
    		int index = xtcType.getConstant().bigIntValue().intValue();
      	return encoding.integerConstant(index);
    	}
    	
    	if(xtcType.resolve().isFunction()) {
    		return info.getLValBinding();
    	}
    	
    	assert info.hasLValBinding();
    	Expression lBinding = info.getLValBinding();
    	return derefMemory(currState, lBinding, node, xtcType);
    }

    public Expression visitRelationalExpression(GNode node) {
    	String relOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lType = CType.getType(node.getNode(0)).resolve();
      Type rType = CType.getType(node.getNode(2)).resolve();
      
    	if(lType.isPointer()) {
    		assert rType.isPointer();
        if (">".equals(relOp))	return encoding.pointerGreaterThan(left, right);
        if (">=".equals(relOp))	return encoding.pointerGreaterThanOrEqual(left, right);
        if ("<".equals(relOp))	return encoding.pointerLessThan(left, right);
        if ("<=".equals(relOp)) return encoding.pointerLessThanOrEqual(left, right);
        
        throw new ExpressionFactoryException("Invalid operation: " + relOp);
    	}
    	
      boolean isUnsigned = CType.isUnsigned(lType) || CType.isUnsigned(rType);
      
      Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lType, rType);
      left = pair.fst(); right = pair.snd();
      
    	if(isUnsigned) {
        if (">".equals(relOp))	return encoding.greaterThan(left, right);
        if (">=".equals(relOp)) return encoding.greaterThanOrEqual(left, right);
        if ("<".equals(relOp)) 	return encoding.lessThan(left, right);
        if ("<=".equals(relOp))	return encoding.lessThanOrEqual(left, right);
        
        throw new ExpressionFactoryException("Invalid operation: " + relOp);
    	} 
    	
    	if (">".equals(relOp)) 		return encoding.signedGreaterThan(left, right);
    	if (">=".equals(relOp)) 	return encoding.signedGreaterThanOrEqual(left, right);
    	if ("<".equals(relOp))		return encoding.signedLessThan(left, right);
    	if ("<=".equals(relOp))		return encoding.signedLessThanOrEqual(left, right);
    	
    	throw new ExpressionFactoryException("Invalid operation: " + relOp);
    }

    public Expression visitSimpleDeclarator(GNode node) {
      return visitPrimaryIdentifier(node);
    }

    public Expression visitStringConstant(GNode node) {
      //FIXME: make a string constant into integer variable? improper
      return encoding.variable(node.getString(0), IRType.getIRType(node), false);
    }
    
    public Expression visitSubscriptExpression(GNode node) {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Expression lhsExpr = encodeExpression(node.getNode(0));
      Expression rhsExpr = encodeExpression(node.getNode(1));
      
    	Type lhsType = CType.getType(node.getNode(0));
    	Type rhsType = CType.getType(node.getNode(1));
    	
      Expression loc = pointerPlus(lhsExpr, rhsExpr, lhsType, rhsType);
      return derefMemory(currState, loc, node, CType.getType(node));
    }
    
    public Expression visitSizeofExpression(GNode node) {
    	Node typeNode = node.getNode(0);
    	Type type = CType.getType(typeNode);
    	if(!CType.isVarLengthArray(type)) {
    		long size = encoding.getCTypeAnalyzer().getSize(type);
    		return encoding.integerConstant(size);
    	}
    	// array with variable length
    	Expression ptr = encodeExpression(typeNode);
    	return stateFactory.lookupSize(currState, ptr, typeNode);
    }
    
    public Expression visitTypeName(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitSpecifierQualifierList(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitInt(GNode node) {
      //FIXME: Int() and Char() won't be visited.
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }    
    
    public Expression visitChar(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitPointer(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitStructureTypeReference(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitUnionTypeReference(GNode node) {
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitTypedefName(GNode node) {
      if(Preferences.isSet(Preferences.OPTION_BYTE_BASED)) {
        return encodeExpression(node.getNode(0));
      } 
      
      long size = encoding.getCTypeAnalyzer().getSize(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitUnaryMinusExpression(GNode node) {
      Expression rhs = encodeExpression(node.getNode(0));
      return encoding.uminus(rhs);
    }
    
    public Expression visitUnaryPlusExpression(GNode node) {
      Expression rhs = encodeExpression(node.getNode(0));
      return encoding.uminus(rhs);
    }
    
    public Expression visitMultiplicativeExpression(final GNode node) {
      // TODO: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      
    	String mulOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lhsType = CType.getType(node.getNode(0));
      Type rhsType = CType.getType(node.getNode(2));
    	
      Pair<Expression, Expression> pair = encoding.arithTypeConversion(left, right, lhsType, rhsType);
      left = pair.fst(); right = pair.snd();
      
      if ("*".equals(mulOp))
        return encoding.times(coerceToInteger(left), coerceToInteger(right));
      
      boolean isUnsigned = CType.isUnsigned(lhsType) || CType.isUnsigned(rhsType);
      
      if ("/".equals(mulOp)) {
      	if(isUnsigned)
      		return encoding.divide(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedDivide(coerceToInteger(left), coerceToInteger(right));
      } 
      
      if ("%".equals(mulOp)) {
      	if(isUnsigned)
      		return encoding.rem(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedRem(coerceToInteger(left), coerceToInteger(right));
      }
      
      throw new ExpressionFactoryException("Invalid operation: " + mulOp);
    }
    
    public Expression visitDirectComponentSelection(GNode node) {
      String fieldName = node.getString(1);
      Type baseType = CType.getType(node.getNode(0)).resolve();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = lvalVisitor.encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
      Type type = CType.getType(node);
      return derefMemory(currState, resLoc, node, type);
    }
    
    public Expression visitIndirectComponentSelection(GNode node) {
      String fieldName = node.getString(1);
      Type baseType = CType.getType(node.getNode(0)).resolve().toPointer().getType();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(
      		coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      Type type = CType.getType(node);
      return derefMemory(currState, resLoc, node, type);
    }

		private Expression derefMemory(StateExpression state, Expression lvalExpr, Node node, Type type) {
			Preconditions.checkArgument(!Tag.VOID.equals(type.tag()));
			if(!CType.isScalar(type))	return lvalExpr;
			
		  stateFactory.setValidAccess(state, lvalExpr, node);
		  return stateFactory.deref(state, lvalExpr, node);
		}
		
		private Expression getBoundVarExpr(IRVarInfo varInfo) {
			assert(varInfo.hasProperty(Identifiers.CTRLVAR));
			String name = varInfo.getName();
			IRType type = varInfo.getIRType();
			Expression iExpr = encoding.boundVar(name, type, false);
	    return iExpr;
		}
		
		private Expression getBoundVarExpr(int index, IRVarInfo varInfo) {
			assert(varInfo.hasProperty(Identifiers.CTRLVAR));
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
		
    private Expression encodeExpression(Node node) {
      return ((Expression) dispatch(node));
    }

    public Expression toLval(Node node) {
      return encodeExpression(node);
    }
    
    public Expression visitIndirectionExpression(GNode node) {
      return exprVisitor.encodeExpression(node.getNode(0));
    }

    public Expression visitPrimaryIdentifier(GNode node) {
    	IRVarInfo info = exprVisitor.lookupVar(node);
    	assert(!info.hasProperty(Identifiers.CTRLVAR));
    	assert(info.hasLValBinding());
    	return info.getLValBinding();
    }

    public Expression visitSimpleDeclarator(GNode node) {
    	IRVarInfo info = exprVisitor.lookupVar(node);
    	
    	if(info.getXtcType().getShape().isStatic() && info.hasLValBinding()) 
    		return info.getLValBinding();
    	
    	Expression lValue = info.hasLogicLabel() ? 
    			encoding.variable(info.getName(), info.getIRType(), true) 
    			: getLvalBinding(info);
    	lValue.setHoareLogic(info.hasLogicLabel());
    	
    	info.setLValBinding(lValue);
    	return lValue;
    }
    
    public Expression visitAdditiveExpression(GNode node) {
    	return exprVisitor.visitAdditiveExpression(node);
    }
    
    public Expression visitSubscriptExpression(GNode node) {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Expression base = exprVisitor.encodeExpression(node.getNode(0));
      Expression index = exprVisitor.encodeExpression(node.getNode(1));
      return pointerPlus(base, index, CType.getType(node.getNode(0)), CType.getType(node.getNode(1)));
    }
    
    public Expression visitCastExpression(GNode node) {
    	return exprVisitor.visitCastExpression(node);
    }
    
    public Expression visitDirectComponentSelection(GNode node) {
      String fieldName = node.getString(1);
      Type baseType = CType.getType(node.getNode(0));
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression baseLoc = encodeExpression(node.getNode(0));
      return encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
    }
    
    public Expression visitFunctionCall(GNode node) {
      return exprVisitor.visitFunctionCall(node);
    }
    
    public Expression visitIndirectComponentSelection(GNode node) {
      String fieldName = node.getString(1);
      Type baseType = CType.getType(node.getNode(0)).resolve().toPointer().getType();
      long offset = encoding.getCTypeAnalyzer().getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression baseLoc = exprVisitor.encodeExpression(node.getNode(0));
      return encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
    }

    public Expression visitParameterDeclaration(GNode node) {
      return encodeExpression(node.getNode(1));
    }
    
    public Expression visitPointerDeclarator(GNode node) {
      return encodeExpression(node.getNode(1));
    }
    
    public Expression visitIntegerConstant(GNode node) {
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
    return new ExpressionVisitor(pre).toBoolean(node,negated);
  }

  @Override
  public Expression toExpression(StateExpression pre, Node node) {
    return new ExpressionVisitor(pre).toExpression(node);
  }

  @Override
  public Expression toLval(StateExpression pre, Node node) {
    return new LvalVisitor(pre).toLval(node);
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

  public static CExpressionEncoder create(
      Mode mode) {
  	ExpressionEncoding encoding = mode.getEncoding();
  	StateFactory<?> stateFactory = mode.getStateFactory();
  	
    IOUtils.debug().pln(
        "Creating CExpressionEncoder with encoding: " + encoding);
    return new CExpressionEncoder(encoding, stateFactory);
  }
  
  private final ExpressionEncoding encoding;
  private Scope currScope;
  private final StateFactory<?> stateFactory;

  private CExpressionEncoder(ExpressionEncoding encoding,
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
