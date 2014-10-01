/**
 * 
 */
package edu.nyu.cascade.c;

import java.math.BigInteger;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
import edu.nyu.cascade.ir.memory.model.MemoryModel;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;

class CExpressionEncoder implements ExpressionEncoder {
  private static final String TYPE = xtc.Constants.TYPE;
  private static final String VAR_PREFIX = "addr_of_";
  
  @SuppressWarnings("unused")
  private class ExpressionVisitor extends Visitor {
    private final StateExpression freshState;
    private final LvalVisitor lvalVisitor;
    
    public ExpressionVisitor() {
      freshState = stateFactory.freshState();
      lvalVisitor = new LvalVisitor(this);
    }
    
    private StateExpressionClosure toBoolean(Node node) {
      return toBoolean(node, false);
    }

    private StateExpressionClosure suspend(Expression expr) {
      return getMemoryModel().suspend(freshState, expr);
    }
    
    private StateExpressionClosure toBoolean(Node node, boolean negated) {
      return suspend(encodeBoolean(node,negated));
    }
    
		private StateExpressionClosure toExpression(Node node) {
			return suspend(encodeExpression(node));
		}

    private Expression encodeBoolean(Node node) {
      return encodeBoolean(node, false).setNode(GNode.cast(node));
    }
    
    private Expression encodeBoolean(Node node, boolean negated) {
      Expression b = coerceToBoolean((Expression) dispatch(node));
      return negated ? encoding.not(b) : b;
    }
    
    private Expression encodeExpression(Node node) {
      return ((Expression) dispatch(node)).setNode(GNode.cast(node));
    }

    private Expression coerceToBoolean(Expression e) {      
      return encoding.isBoolean(e) ? e : encoding.castToBoolean(e);
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
      Expression condition = encodeBoolean(node.getNode(0));
      Expression trueCase = encodeExpression(node.getNode(1));
      Expression falseCase = encodeExpression(node.getNode(2));
      return encoding.ifThenElse(condition, trueCase, falseCase);
    }

    public Expression visitAdditiveExpression(GNode node) {
      // FIXED: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
      
    	String additiveOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lhsType = CType.getType(left.getNode()).resolve();
      Type rhsType = CType.getType(right.getNode()).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
      
      if(isLhsPointer || isRhsPointer) {
        if ("+".equals(additiveOp))		return pointerPlus(right, left);
        if ("-".equals(additiveOp)) 	return pointerMinus(left, right);
        throw new ExpressionFactoryException("Invalid operation: " + additiveOp);
      }
      
      Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      left = pair.fst(); right = pair.snd();
      
      if ("+".equals(additiveOp)) return encoding.plus(coerceToInteger(left), coerceToInteger(right));
      if ("-".equals(additiveOp)) return encoding.minus(coerceToInteger(left), coerceToInteger(right));
      throw new ExpressionFactoryException("Invalid operation: " + additiveOp);
    }
    
    public Expression visitShiftExpression(GNode node) {
    	String shiftOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
    	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
    	left = pair.fst(); right = pair.snd();
    	
    	if ("<<".equals(shiftOp))
        return encoding.lshift(coerceToInteger(left), coerceToInteger(right));

      if (">>".equals(shiftOp)) {
      	if(CType.isUnsigned(CType.getType(left.getNode())))
      		return encoding.rshift(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedRshift(coerceToInteger(left), coerceToInteger(right));
      }
      
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
    	
      Type lhsType = CType.getType(left.getNode()).resolve();
      Type rhsType = CType.getType(right.getNode()).resolve();
      
  		boolean isLhsPointer = lhsType.isArray() || lhsType.isPointer();
  		boolean isRhsPointer = rhsType.isArray() || rhsType.isPointer();
    	
      if ("=".equals(assignOp)) 	return right;
      if ("+=".equals(assignOp))	{
      	if(isLhsPointer || isRhsPointer) {
      		return pointerPlus(left, right);
      	} else {
        	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
        	left = pair.fst(); right = pair.snd();
        	return encoding.plus(coerceToInteger(left), coerceToInteger(right));
      	}
      }
      if ("-=".equals(assignOp)) 	{
      	if(isLhsPointer || isRhsPointer) {
      		return pointerMinus(left, right);
      	} else {
        	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
        	left = pair.fst(); right = pair.snd();
        	return encoding.minus(coerceToInteger(left), coerceToInteger(right));
      	}
      }
      if ("*=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	return encoding.times(coerceToInteger(left), coerceToInteger(right));
      }
      
    	boolean isUnsigned = CType.isUnsigned(lhsType) || CType.isUnsigned(rhsType);
    	
      if ("/=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return encoding.divide(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedDivide(coerceToInteger(left), coerceToInteger(right));
      }
      if ("%=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	if(isUnsigned)
      		return encoding.rem(coerceToInteger(left), coerceToInteger(right));
      	else
      		return encoding.signedRem(coerceToInteger(left), coerceToInteger(right));
      }
      if ("|=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseOr(left, right);
      }
      if ("&=".equals(assignOp))	{
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseAnd(left, right);
      }
      if ("^=".equals(assignOp)) {
      	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      	left = pair.fst(); right = pair.snd();
      	return encoding.bitwiseXor(left,  right);
      }
      
      throw new ExpressionFactoryException("Invalid operation: " + assignOp);
    }

    public Expression visitBitwiseAndExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseAnd(left, right);
    }
    
    public Expression visitBitwiseOrExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseOr(left, right);
    }
    
    public Expression visitBitwiseXorExpression(GNode node) {
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(1));
    	Pair<Expression, Expression> pair = arithTypeConversion(left, right);
    	left = pair.fst(); right = pair.snd();
    	return encoding.bitwiseXor(left, right);
    }
    
    public Expression visitBitwiseNegationExpression(GNode node) {
    	Expression src = encodeExpression(node.getNode(0));
    	return encoding.bitwiseNegate(src);
    }

    public Expression visitCastExpression(GNode node) {
      Type targetType = CType.getType(node).resolve();
      Expression src = encodeExpression(node.getNode(1));
      return encoding.castExpression(src, targetType);
    }
    
    public Expression visitCharacterConstant(GNode node) {
      Type type = CType.getType(node);
      long constVal = type.getConstant().longValue();
      return encoding.characterConstant(constVal);
    }

    public Expression visitEqualityExpression(GNode node) {
    	String eqOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
    	Pair<Expression, Expression> pair = relationTypeConversion(left, right);
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
      MemoryModel<?> memModel = getMemoryModel();
      
      if( ReservedFunction.FUN_VALID.equals(name) ) {
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        assert(argList.size() == 2 || argList.size() == 1);
        
        if(argExprs.size() == 1)
          return memModel.validAccess(freshState, argExprs.get(0));
        else
          return memModel.validAccessRange(freshState, argExprs.get(0), argExprs.get(1));
      } 
      
      if( ReservedFunction.FUN_VALID_MALLOC.equals(name)) {
        Preconditions.checkArgument(argList.size() == 2);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        return memModel.validMalloc(freshState, argExprs.get(0), argExprs.get(1));
      } 
      
      if( ReservedFunction.FUN_VALID_FREE.equals(name)) {
        Preconditions.checkArgument(argList.size() == 1);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        return memModel.validFree(freshState, argExprs.get(0));
      } 

      if( ReservedFunction.FUN_IMPLIES.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        return encoding.implies(argExprs.get(0), argExprs.get(1));
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
      return derefMemory(freshState, op.setNode(node));
    }

    public Expression visitIntegerConstant(GNode node) {
      Type type = CType.getType(node).resolve();
      assert(type.isInteger());
      
      Expression res = null;
      String numStr = node.getString(0);
      Pair<String, Integer> pair = parseNumberStr(numStr);
      
      numStr = pair.fst();
      int base = pair.snd();
      
			Pattern pattern = Pattern.compile("[UuLl]+");
			Matcher matcher = pattern.matcher(numStr);
			if(matcher.find()) {
				int index = matcher.start();
				numStr = numStr.substring(0, index);
			}
      
      switch(type.toInteger().getKind()) {
			case S_INT:
			case INT: {
				int constVal = Integer.parseInt(numStr, base);
        return encoding.integerConstant(constVal);
			}
			case U_INT: {// java Integer cannot parse u_int (may overflow)
				long constVal = Long.parseLong(numStr, base);
				int intSize = (int) CType.getSizeofType(IntegerT.INT) * encoding.getWordSize();
				Expression constant = encoding.integerConstant(constVal);
				return encoding.castToInteger(constant, intSize);
			}
			case LONG: {
				long constVal = Long.parseLong(numStr, base);
        return encoding.integerConstant(constVal);
			}
			case U_LONG:
			case U_LONG_LONG:
			case LONG_LONG: {
				BigInteger constVal = new BigInteger(numStr, base);
        return encoding.integerConstant(constVal);
			}
			default:
				throw new ExpressionFactoryException("Unsupported type " + type);
      }
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
    	/* info could be either enumerator, ctrl variable or Hoare variable,
    	 * note that Hoare variable has both left and right bindings */
    	if(info.hasRValBinding()) return info.getRValBinding();
    	
    	assert(info.hasLValBinding());
    	Expression lBinding = info.getLValBinding();
    	return derefMemory(freshState, lBinding.setNode(node));
    }

    public Expression visitRelationalExpression(GNode node) {
    	String relOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lType = CType.getType(left.getNode()).resolve();
      Type rType = CType.getType(right.getNode()).resolve();
      
    	if(lType.isPointer()) {
    		assert rType.isPointer();
        if (">".equals(relOp))	return encoding.pointerGreaterThan(left, right);
        if (">=".equals(relOp))	return encoding.pointerGreaterThanOrEqual(left, right);
        if ("<".equals(relOp))	return encoding.pointerLessThan(left, right);
        if ("<=".equals(relOp)) return encoding.pointerLessThanOrEqual(left, right);
        
        throw new ExpressionFactoryException("Invalid operation: " + relOp);
    	}

      left.setNode(node.getGeneric(0)); right.setNode(node.getGeneric(2));
      boolean isUnsigned = CType.isUnsigned(CType.getType(left.getNode())) || 
      		CType.isUnsigned(CType.getType(right.getNode()));
      
      Pair<Expression, Expression> pair = relationTypeConversion(left, right);
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
    
    public Expression visitEnumerator(GNode node) {
    	IRVarInfo info = lookupVar(node);
    	Expression iExpr = encoding.variable(info.getName(), info.getIRType(), false);
    	info.setRValBinding(iExpr);
    	return iExpr;
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
      Expression loc = pointerPlus(lhsExpr, rhsExpr);
      return derefMemory(freshState, loc.setNode(node));
    }
    
    public Expression visitSizeofExpression(GNode node) {
    	Node typeNode = node.getNode(0);
    	
      if(typeNode.hasProperty(TYPE)) { // pointer type (STRUCT *)
        long size = CType.getSizeofType(CType.getType(typeNode));
        return encoding.integerConstant(size);
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
    
    public Expression visitTypeName(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitSpecifierQualifierList(GNode node) {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitInt(GNode node) {
      //FIXME: Int() and Char() won't be visited.
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }    
    
    public Expression visitChar(GNode node) {
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitPointer(GNode node) {
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitStructureTypeReference(GNode node) {
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitUnionTypeReference(GNode node) {
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitTypedefName(GNode node) {
      if(Preferences.isSet(Preferences.OPTION_BYTE_BASED)) {
        return encodeExpression(node.getNode(0));
      } 
      
      long size = CType.getSizeofType(CType.getType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitUnaryMinusExpression(GNode node) {
      Expression rhs = encodeExpression(node.getNode(0));
      return encoding.uminus(rhs); 
    }
    
    public Expression visitMultiplicativeExpression(final GNode node) {
      // TODO: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
      
    	String mulOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Pair<Expression, Expression> pair = arithTypeConversion(left, right);
      left = pair.fst(); right = pair.snd();
      
      if ("*".equals(mulOp))
        return encoding.times(coerceToInteger(left), coerceToInteger(right));
      
      boolean isUnsigned = CType.isUnsigned(CType.getType(left.getNode())) || 
      		CType.isUnsigned(CType.getType(right.getNode()));
      
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
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = CType.getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = lvalVisitor.encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
      return derefMemory(freshState, resLoc.setNode(node));
    }
    
    public Expression visitIndirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref =  type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = CType.getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.componentSelect(
      		coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      return derefMemory(freshState, resLoc.setNode(node));
    }
    
    private Pair<Expression, Expression> relationTypeConversion(Expression lhs, Expression rhs) {
    	Type lhsType = CType.getType(lhs.getNode()).resolve();
    	Type rhsType = CType.getType(rhs.getNode()).resolve();
    	
    	if(CType.isPointerOrDecay(lhsType)) {
    		assert(CType.isPointerOrDecay(rhsType));
    		return Pair.of(encoding.castToPointer(lhs), encoding.castToPointer(rhs));
    	}
    	
  		int leftSize = encoding.castToInteger(lhs).asBitVector().getSize();
  		int rightSize = encoding.castToInteger(rhs).asBitVector().getSize();
  		int size = Math.max(leftSize, rightSize);
    	
      Expression lhsPrime = encoding.castToInteger(lhs, size);
      Expression rhsPrime = encoding.castToInteger(rhs, size);
     
      GNode lhsNode = lhs.getNode(), rhsNode = rhs.getNode();
      lhsPrime.setNode(lhsNode); rhsPrime.setNode(rhsNode);
      
      return Pair.of(lhsPrime, rhsPrime);
    }
    
    private Pair<Expression, Expression> arithTypeConversion(Expression lhs, Expression rhs) {
  		int leftSize = encoding.castToInteger(lhs).asBitVector().getSize();
  		int rightSize = encoding.castToInteger(rhs).asBitVector().getSize(); 		
  		int intSize = (int) (CType.getSizeofType(IntegerT.INT) * encoding.getWordSize());
  		int size = Math.max(Math.max(leftSize, rightSize), intSize);
    	
      Expression lhsPrime = encoding.castToInteger(lhs, size);
      Expression rhsPrime = encoding.castToInteger(rhs, size);
     
      GNode lhsNode = lhs.getNode(), rhsNode = rhs.getNode();
      lhsPrime.setNode(lhsNode); rhsPrime.setNode(rhsNode);
      			
      return Pair.of(lhsPrime, rhsPrime);
    }
    
    private Expression arithTypeConversion(Expression lhs) {  
  		int leftSize = encoding.castToInteger(lhs).asBitVector().getSize();
  		int intSize = (int) CType.getSizeofType(IntegerT.INT) * encoding.getWordSize();
  		int size = Math.max(leftSize, intSize);
  		
  		Expression lhsPrime = encoding.castToInteger(lhs, size);
  		GNode lhsNode = lhs.getNode();
  		lhsPrime.setNode(lhsNode);
  		
      return lhsPrime;
    }
    
    private Pair<String, Integer> parseNumberStr(String numStr) {    	
      if(numStr.startsWith("0x")) 
        return Pair.of(numStr.substring(2), 16);
      
      if(numStr.startsWith("0b")) 
      	return Pair.of(numStr.substring(2), 2);
      
      if(numStr.startsWith("0h")) 
      	return Pair.of(numStr.substring(2), 8);
      
      return Pair.of(numStr, 10);
    }

		private Expression derefMemory(StateExpression memory, Expression lvalExpr) {		  
		  GNode srcNode = lvalExpr.getNode();
		  Type t = CType.getType(srcNode).resolve();
		  
		  Expression resExpr;
		  if(t.isArray() || t.isStruct() || t.isUnion())
		    resExpr = lvalExpr;
		  else
		    resExpr = getMemoryModel().deref(memory, lvalExpr); 
		  
		  return resExpr.setNode(srcNode);
		}
  }
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
    private final StateExpression freshState;
    private final ExpressionVisitor exprVisitor;
    
    private LvalVisitor() {
      this.exprVisitor = new ExpressionVisitor();
      this.freshState = exprVisitor.freshState;
    }

    private LvalVisitor(ExpressionVisitor exprVisitor) {
      this.exprVisitor = exprVisitor;
      this.freshState = exprVisitor.freshState;
    }
    
		private Expression coerceToInteger(Expression e) {       
			return encoding.isInteger(e) ? e : encoding.castToInteger(e);
		}

		private Expression coerceToPointer(Expression e) {
			return encoding.isPointer(e) ? e : encoding.castToPointer(e);
		}
		
    private Expression encodeExpression(Node node) {
      return ((Expression) dispatch(node)).setNode(GNode.cast(node));
    }

    public StateExpressionClosure toLval(Node node) {
      return getMemoryModel().suspend(freshState, encodeExpression(node));
    }
    
    public Expression visitIndirectionExpression(GNode node) {
      Expression op = exprVisitor.encodeExpression(node.getNode(0));
      Type type = CType.getType(node);
      IOUtils.debug().pln(
          "Indirection expression type: " + type.tag() + type.getName()
              + type.resolve().getName()).flush();
      return op;
    }

    public Expression visitPrimaryIdentifier(GNode node) {
    	IRVarInfo info = lookupVar(node);
    	assert(!info.hasProperty(Identifiers.CTRLVAR));
    	assert(info.hasLValBinding());
    	return info.getLValBinding();
    }

    public Expression visitSimpleDeclarator(GNode node) {
    	IRVarInfo info = lookupVar(node);
    	
    	if(Preferences.isSet(Preferences.OPTION_HOARE)) {
    		boolean isHoare = (Boolean) info.getProperty(Identifiers.HOARE_VAR);
    		if(isHoare) {
        	Expression lValue = getLvalBinding(info);
      		Expression rValue = encoding.variable(info.getName(), info.getIRType(), true);
      		info.setLValBinding(lValue);
      		info.setRValBinding(rValue);
      		return lValue;
    		}
    	}
    	
    	Expression lValue = getLvalBinding(info);
    	info.setLValBinding(lValue);
    	return lValue;
    }
    
    public Expression visitAdditiveExpression(GNode node) {
      return exprVisitor.encodeExpression(node);
    }
    
    public Expression visitSubscriptExpression(GNode node) {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Expression base = exprVisitor.encodeExpression(node.getNode(0));
      Expression index = exprVisitor.encodeExpression(node.getNode(1));
      return pointerPlus(base, index);
    }
    
    public Expression visitDirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = CType.getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression baseLoc = encodeExpression(node.getNode(0));
      return encoding.componentSelect(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
    }
    
    public Expression visitFunctionCall(GNode node) {
      return exprVisitor.visitFunctionCall(node);
    }
    
    public Expression visitIndirectComponentSelection(GNode node) {
      Type type = CType.getType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      long offset = CType.getOffset(baseType.toStructOrUnion(), fieldName);
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
  }
  
  @Override
  public StateExpressionClosure toBoolean(Node node) {
    return new ExpressionVisitor().toBoolean(node);
  }

  @Override
  public StateExpressionClosure toBoolean(Node node, boolean negated) {
    return new ExpressionVisitor().toBoolean(node,negated);
  }

  @Override
  public StateExpressionClosure toExpression(Node node) {
    return new ExpressionVisitor().toExpression(node);
  }

  @Override
  public StateExpressionClosure toLval(Node node) {
    return new LvalVisitor().toLval(node);
  }

  @Override
  public StateExpressionClosure toBoolean(Node node, Scope scope) {
    return toBoolean(node,false,scope);
  }

  @Override
  public StateExpressionClosure toBoolean(Node node, boolean negated,
      Scope scope) {
    currScope = scope;
  	return toBoolean(node,negated);
  }

  @Override
  public StateExpressionClosure toExpression(Node node, Scope scope) {
    currScope = scope;
  	return toExpression(node);
  }

  @Override
  public StateExpressionClosure toLval(Node node, Scope scope) {
  	currScope = scope;
  	return toLval(node);
  }

  public static CExpressionEncoder create(
      Mode mode) {
  	ExpressionEncoding encoding = mode.getEncoding();
  	MemoryModel<?> memoryModel = mode.getMemoryModel();
  	StateFactory<?> stateFactory = mode.getStateFactory();
  	
    IOUtils.debug().pln(
        "Creating CExpressionEncoder with encoding: " + encoding);
    return new CExpressionEncoder(encoding, memoryModel, stateFactory);
  }
  
  private final ExpressionEncoding encoding;
  private final MemoryModel<?> memoryModel;
  private Scope currScope;
  private final StateFactory<?> stateFactory;

  private CExpressionEncoder(ExpressionEncoding encoding,
  		MemoryModel<?> memoryModel, 
      StateFactory<?> stateFactory) {
    this.encoding = encoding;
    this.memoryModel = memoryModel;
    this.stateFactory = stateFactory;
  }
  
  @Override
	public ExpressionEncoding getEncoding() {
	  return encoding;
	}

	@Override
	public MemoryModel<?> getMemoryModel() {
	  return memoryModel;
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
	 * Returns an expression representing the lvalue of the given name. I.e.,
	 * <code>lookupVar(x)</code> will return an expression representing
	 * <code>&x</code>. The rvalue of <code>x</code> is
	 * <code>exprFactory.deref(lookupVar(x))</code>.
	 * */
	private Expression getLvalBinding(IRVarInfo varInfo) {
		// TODO: map expressions per-factory
		String addrName = VAR_PREFIX + varInfo.getName();
		return getMemoryModel().createLval(addrName);
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
  
  /**
   * Pointer plus: T* ptr;
   * 		ptr + i = ptr + sizeof(T) * i
   */
  private Expression pointerPlus(Expression lhs, Expression rhs) {
  	Type lhsType = CType.getType(lhs.getNode()).resolve();
  	Type rhsType = CType.getType(rhs.getNode()).resolve();
  	
  	if(lhsType.isPointer()) {
			Type ptoType = lhsType.toPointer().getType();
      long size = CType.getSizeofType(ptoType);
      
      /* cast factor the the rhsType to perform size * offset */
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(rhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerPlus(lhs, addon);
  	}
  	
  	if(lhsType.isArray()) {
			Type ptoType = lhsType.toArray().getType();
      long size = CType.getSizeofType(ptoType);
      
      /* cast factor the the rhsType to perform size * offset */
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(rhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerPlus(lhs, addon);
  	}
  	
  	if(rhsType.isPointer()) {
  		Type ptoType = rhsType.toPointer().getType();
      long size = CType.getSizeofType(ptoType);
      
      /* cast factor the the lhsType to perform size * offset */
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(lhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerPlus(rhs, addon);
  	}
		
		if(rhsType.isArray()) {
			Type ptoType = rhsType.toArray().getType();
      long size = CType.getSizeofType(ptoType);
      
      /* cast factor the the lhsType to perform size * offset */
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(lhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerPlus(rhs, addon);
		}
		
		throw new ExpressionFactoryException("Invalid operands");
  }
  
  /**
   * Pointer minus: T* ptr;
   * 		ptr - i = ptr - sizeof(T) * i
   */
  private Expression pointerMinus(Expression lhs, Expression rhs) {
  	Type lhsType = CType.getType(lhs.getNode()).resolve();
  	Type rhsType = CType.getType(rhs.getNode()).resolve();
  	
		if(lhsType.isPointer()) {
			Type ptoType = lhsType.toPointer().getType();
	    long size = CType.getSizeofType(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(
	    		encoding.castToOffset(rhs), 
	    		encoding.castToOffset(factor));
			return encoding.pointerMinus(lhs, addon);
		}
		
		if(lhsType.isArray()) {
			Type ptoType = lhsType.toArray().getType();
	    long size = CType.getSizeofType(ptoType);
	    Expression factor = encoding.integerConstant(size);
	    Expression addon = encoding.times(
	    		encoding.castToOffset(rhs), 
	    		encoding.castToOffset(factor));
			return encoding.pointerMinus(lhs, addon);
		}

		if(rhsType.isPointer()) {
			Type ptoType = rhsType.toPointer().getType();
      long size = CType.getSizeofType(ptoType);
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(lhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerMinus(rhs, addon);
		}
		
		if(rhsType.isArray()) {
			Type ptoType = rhsType.toArray().getType();
      long size = CType.getSizeofType(ptoType);
      Expression factor = encoding.integerConstant(size);
      Expression addon = encoding.times(
      		encoding.castToOffset(lhs), 
      		encoding.castToOffset(factor));
			return encoding.pointerMinus(rhs, addon);
		}
		
		throw new ExpressionFactoryException("Invalid operands");
  }
}
