/**
 * 
 */
package edu.nyu.cascade.c;

import static edu.nyu.cascade.util.RecursionStrategies.binaryNode;
import static edu.nyu.cascade.util.RecursionStrategies.binaryOp;

import java.io.File;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import xtc.type.*;
import xtc.tree.*;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ComputationException;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.bak.ReachMemoryModel;
import edu.nyu.cascade.ir.impl.VarInfo;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies.BinaryInfixRecursionStrategy;
import edu.nyu.cascade.util.RecursionStrategies.BinaryRecursionStrategy;
import edu.nyu.cascade.util.ReservedFunction;

class CExpressionEncoder implements ExpressionEncoder {
  private static final String TYPE = xtc.Constants.TYPE;
  
  @SuppressWarnings("unused")
  private class ExpressionVisitor extends Visitor {
    private final Expression memory;
    // New field lvalVisitor to keep code DRY.
    private final LvalVisitor lvalVisitor;
    
    public ExpressionVisitor() {
      memory = getMemoryModel().freshState();
      lvalVisitor = new LvalVisitor(this);
    }
    
    private ExpressionClosure toBoolean(Node node) {
      return toBoolean(node, false);
    }

    private ExpressionClosure suspend(Expression expr) {
      return getMemoryModel().suspend(memory, expr);
    }
    
    private ExpressionClosure toBoolean(Node node, boolean negated) {
      return suspend(encodeBoolean(node,negated));
    }
    
		private ExpressionClosure toExpression(Node node) {
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
    public Expression unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as unknown: "
                  + node.getName());

      try {
        return encoding.getIntegerEncoding().unknown();
      } catch (ExpressionFactoryException e) {
        throw new VisitingException("Expression Factory failure", e);
      }
    }
    
    public Expression visitConditionalExpression(GNode node) 
        throws VisitingException {
      Expression condition = encodeBoolean(node.getNode(0));
      Expression trueCase = encodeExpression(node.getNode(1));
      Expression falseCase = encodeExpression(node.getNode(2));
      return encoding.ifThenElse(condition, trueCase, falseCase);
    }

    public Expression visitAdditiveExpression(GNode node)
        throws VisitingException {
      // FIXED: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
    	String op = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lType = lookupType(left.getNode()).resolve();
      Type rType = lookupType(right.getNode()).resolve();
    	
      Function<Expression, Integer> getFactor = new Function<Expression, Integer>() {
				@Override
				public Integer apply(Expression pointer) {
					Type type = lookupType(pointer.getNode()).resolve();
					Preconditions.checkArgument(type.isPointer() || type.isArray());
					if(type.isPointer())
						return encoding.getSizeofType(type.toPointer().getType());
					else
						return encoding.getSizeofType(type.toArray().getType());
				}                	
      };
      
      Expression res = null;
      
      // multiplied by the size of the type of the pointer
      if(lType.isPointer() || lType.isArray()) {
      	int factor = getFactor.apply(left);
      	Expression factorExpr = encoding.integerConstant(factor);
        right = encoding.times(coerceToInteger(right), factorExpr);
        if ("+".equals(op)) {
          res = encoding.pointerPlus(left, right);
        } else if ("-".equals(op)) {
        	res = encoding.pointerMinus(left, right);
        } else {
          throw new ExpressionFactoryException("Invalid operation: " + op);
        }
      } else if(rType.isPointer() || rType.isArray()) {
      	int factor = getFactor.apply(right);
      	Expression factorExpr = encoding.integerConstant(factor);
        left = encoding.times(coerceToInteger(left), factorExpr);
        if ("+".equals(op)) {
        	res = encoding.pointerPlus(right, left);
        } else if ("-".equals(op)) {
        	res = encoding.pointerMinus(right, left);
        } else {
          throw new ExpressionFactoryException("Invalid operation: " + op);
        }
      } else {
        if ("+".equals(op)) {
        	res = encoding.plus(left, right);
        } else if ("-".equals(op)) {
        	res = encoding.minus(left, right);
        } else {
          throw new ExpressionFactoryException("Invalid operation: " + op);
        }
      }
      return res;
    }
    
    public Expression visitShiftExpression(GNode node) {
      Expression res = binaryOp(node, this,
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression left, String additiveOperator,
                Expression right) {
              try {
                if ("<<".equals(additiveOperator)) {
                  return encoding.lshift(coerceToInteger(left), coerceToInteger(right));
                } else if (">>".equals(additiveOperator)) {
                  return encoding.rshift(coerceToInteger(left), coerceToInteger(right));
                } else {
                  throw new ExpressionFactoryException("Invalid operation: " + additiveOperator);
                }
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          });
      return res;
    }

    public Expression visitAddressExpression(GNode node) {
      return lvalVisitor.encodeExpression(node.getNode(0));
    }

    public Expression visitAssignmentExpression(GNode node)
        throws ExpressionFactoryException {
      /*
       * Note we are interpreting the assignment here as an expression, not as a
       * statement. I.e., we just need to return the RHS value. For
       * operator-assignment expressions we will return the expression
       * representation the operation. E.g., for a += b we return a + b, etc.
       */

      return binaryOp(node, this,
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression left, String assignmentOperator,
                Expression right) {
              try {
                if ("=".equals(assignmentOperator)) {
                  return right;
                } else if ("+=".equals(assignmentOperator)) {
                  return encoding.plus(left, coerceToInteger(right));
                } else if ("-=".equals(assignmentOperator)) {
                  return encoding.minus(left, coerceToInteger(right));
                } else {
                  throw new UnsupportedOperationException(assignmentOperator);
                }
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          });
    }

    public Expression visitBitwiseAndExpression(GNode node)
        throws ExpressionFactoryException {
      return binaryNode(node, this, new BinaryRecursionStrategy<Expression, Expression>() {
        @Override
        public Expression apply(Expression left, Expression right) {
          try {
            return encoding.bitwiseAnd(coerceToInteger(left), coerceToInteger(right));
          } catch (ExpressionFactoryException e) {
            throw new ComputationException(e);
          }
        }
      });
    }

    public Expression visitCastExpression(GNode node) {
      Type targetType = lookupType(node).resolve();
      Expression src = encodeExpression(node.getNode(1));
      return encoding.castExpression(src, targetType);
    }
    
    public Expression visitCharacterConstant(GNode node)
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      long constVal = type.getConstant().longValue();
//      Expression res = encoding.castConstant(constVal, type);
      return encoding.integerConstant(constVal);
    }

    public Expression visitEqualityExpression(GNode node)
        throws ExpressionFactoryException {
      return binaryOp(node, this,
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression left, String eqOp, Expression right) {
              try {
                Expression b;
                if ("==".equals(eqOp)) {
                  b = encoding.eq(left, right);
                } else if ("!=".equals(eqOp)) {
                  b = encoding.neq(left, right);
                } else {
                  throw new ExpressionFactoryException("Invalid operation: " + eqOp.toString());
                }
                return b;
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          });
    }

    public List<Expression> visitExpressionList(GNode node) {
      List<Expression> subExprList = Lists.newArrayListWithCapacity(node.size());
      for (Object elem : node) {
        Expression subExpr = encodeExpression(GNode.cast(elem));
        subExprList.add(subExpr);
      }
      return subExprList;
    }

    public Expression visitFunctionCall(GNode node) throws ExpressionFactoryException {
      Node funNode = node.getNode(0);
      Preconditions.checkArgument(funNode.hasName("PrimaryIdentifier"));
      Expression res = null;
      
      String name = funNode.getString(0);
      Node argList = node.getNode(1);
      MemoryModel memModel = getMemoryModel();        
      
      if( ReservedFunction.FUN_VALID.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2 || argList.size() == 1);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        if(argExprs.size() == 1)
          res = memModel.valid(memory, argExprs.get(0));
        else
          res = memModel.valid(memory, argExprs.get(0), argExprs.get(1));
      } else if( ReservedFunction.FUN_VALID_MALLOC.equals(name)) {
        Preconditions.checkArgument(argList.size() == 2);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        res = memModel.valid_malloc(memory, argExprs.get(0), argExprs.get(1));
      } else if( ReservedFunction.FUN_VALID_FREE.equals(name)) {
        Preconditions.checkArgument(argList.size() == 1);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        res = memModel.valid_free(memory, argExprs.get(0));
      } else if( ReservedFunction.FUN_ALLOCATED.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2);
        Expression argExpr0 = lvalVisitor.encodeExpression(argList.getNode(0));
        Expression argExpr1 = encodeExpression(argList.getNode(1));
        res = memModel.allocated(memory, argExpr0, argExpr1);
      } else if( ReservedFunction.FUN_IMPLIES.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2);
        List<Expression> argExprs = visitExpressionList(GNode.cast(argList));
        res = encoding.implies(argExprs.get(0), argExprs.get(1));
      } else if( ReservedFunction.FUN_FORALL.equals(name) || ReservedFunction.FUN_EXISTS.equals(name)) {
        List<Expression> args = visitExpressionList(GNode.cast(argList));
        int lastIdx = argList.size()-1;
        Expression body = args.remove(lastIdx);
        ImmutableList.Builder<Expression> argVarsBuilder = new ImmutableList.Builder<Expression>();
        for(int idx = 0; idx < lastIdx; idx++) {
          GNode argNode = argList.getGeneric(idx);
          assert(argNode.hasName("PrimaryIdentifier"));
          String argName = argNode.getString(0);
          Type type = lookupType(argNode).resolve();
          if(type.isPointer()) {
          	argVarsBuilder.add(encoding.getPointerEncoding().variable(argName, true));
          } else if(type.isInteger()) {
          	int size = encoding.getSizeofType(type);
          	argVarsBuilder.add(encoding.getIntegerEncoding().variable(argName, 
          			encoding.getExpressionManager().bitVectorType(size * encoding.getWordSize()), true));
          } else if(type.isBoolean()) {
          	argVarsBuilder.add(encoding.getBooleanEncoding().variable(argName, true));
          }
        }
        body = body.subst(args, argVarsBuilder.build());

        if( ReservedFunction.FUN_FORALL.equals(name) )  
          res = encoding.forall(argVarsBuilder.build(), body);
        else  
          res = encoding.exists(argVarsBuilder.build(), body);         
      } else if( ReservedFunction.FUN_REACH.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 3);
        String fieldName = argList.getNode(0).getString(0);
        Expression fromExpr = encodeExpression(argList.getNode(1));
        Expression toExpr = encodeExpression(argList.getNode(2));
        if(memModel instanceof ReachMemoryModel) {
          res = ((ReachMemoryModel) memModel).reach(fieldName, fromExpr, toExpr, toExpr);
        } else {
          res = encoding.ff();         
        }
      } else if( ReservedFunction.FUN_CREATE_ACYCLIC_LIST.equals(name) || 
          ReservedFunction.FUN_CREATE_CYCLIC_LIST.equals(name) ||
          ReservedFunction.FUN_CREATE_ACYCLIC_DLIST.equals(name) ||
          ReservedFunction.FUN_CREATE_CYCLIC_DLIST.equals(name)) {
        Preconditions.checkArgument(argList.size() == 2);
        Node ptrNode = argList.getNode(0);
        Expression ptrExpr = lvalVisitor.encodeExpression(ptrNode);
        Expression length = encodeExpression(argList.getNode(1));
        Type type = lookupType(ptrNode).toPointer().getType().resolve();
        int size = encoding.getSizeofType(type);
        Map<String, Integer> offMap = getOffsetMap(type);
        
        if(memModel instanceof ReachMemoryModel) {
        	ReachMemoryModel reachMemModel = ((ReachMemoryModel) memModel);
          if(ReservedFunction.FUN_CREATE_ACYCLIC_LIST.equals(name))
            res = reachMemModel.create_list(memory,
                ptrExpr, length, size, offMap, true, true);
          else if(ReservedFunction.FUN_CREATE_CYCLIC_LIST.equals(name))
            res = reachMemModel.create_list(memory,
                ptrExpr, length, size, offMap, false, true);
          else if(ReservedFunction.FUN_CREATE_ACYCLIC_DLIST.equals(name))
            res = reachMemModel.create_list(memory,
                ptrExpr, length, size, offMap, true, false);
          else
            res = reachMemModel.create_list(memory,
                ptrExpr, length, size, offMap, false, false);
        } else {
          res = encoding.tt();
        }
      } else if( ReservedFunction.FUN_ISROOT.equals(name) ) {
        Preconditions.checkArgument(argList.size() == 2);
        String fieldname = argList.getNode(0).getString(0);
        Expression ptrExpr = encodeExpression(argList.getNode(1));
        if(memModel instanceof ReachMemoryModel) {
          res = ((ReachMemoryModel) memModel).isRoot(fieldname, ptrExpr);
        } else {
          throw new ExpressionFactoryException("Invalid memory model.");
        }
      } else {
      	if(argList != null) visitExpressionList(GNode.cast(argList));
      	
        Type type = lookupType(node).resolve();
        if(type.isPointer())
        	res = encoding.getPointerEncoding().unknown();
        else if(type.isBoolean())
        	res = encoding.getBooleanEncoding().unknown();
        else { // type.isInteger()
        	int size = encoding.getSizeofType(type);
        	res = encoding.getIntegerEncoding().unknown(
        			encoding.getExpressionManager().bitVectorType(size * encoding.getWordSize()));
        }
      }

      return res;
    }

    public Expression visitIndirectionExpression(GNode node)
        throws ExpressionFactoryException {
      Expression op = encodeExpression(node.getNode(0));
      Type ptrToType = lookupType(node).resolve();
      return derefMemory(memory, op.setNode(node));
    }

    public Expression visitIntegerConstant(GNode node)
        throws ExpressionFactoryException {
      Type type = lookupType(node).resolve();     
      assert(type.isInteger());
      
//      int constVal = 0;
//      if(type.hasConstant()) {
//        // Parse string character
//        constVal = ((BigInteger) type.getConstant().getValue()).intValue();
//      }
      
      Expression res = null;     
      String numStr = node.getString(0);
      switch(type.toInteger().getKind()) {
			case U_INT: 
				numStr = numStr.substring(0, numStr.lastIndexOf('U'));
			case S_INT:
			case INT: {
				int constVal = 0;        
        if(numStr.startsWith("0x")) 
          constVal = Integer.parseInt(numStr.substring(2), 16);
        else if(numStr.startsWith("0b")) 
          constVal = Integer.parseInt(numStr.substring(2), 2);
        else if(numStr.startsWith("0h")) 
          constVal = Integer.parseInt(numStr.substring(2), 8);
        else 
          constVal = Integer.parseInt(numStr);
        res = encoding.integerConstant(constVal);
				break;
			}
			case U_LONG: 
				numStr = numStr.substring(0, numStr.lastIndexOf('U'));
			case LONG: {
				long constVal = 0;
        if(numStr.startsWith("0x")) 
          constVal = Long.parseLong(numStr.substring(2), 16);
        else if(numStr.startsWith("0b")) 
          constVal = Long.parseLong(numStr.substring(2), 2);
        else if(numStr.startsWith("0h")) 
          constVal = Long.parseLong(numStr.substring(2), 8);
        else 
          constVal = Long.parseLong(numStr);
        res = encoding.integerConstant(constVal);
				break;
			}
			case U_LONG_LONG:
				numStr = numStr.substring(0, numStr.lastIndexOf('U'));
			case LONG_LONG: {
				BigInteger constVal = null;
        if(numStr.startsWith("0x")) 
          constVal = new BigInteger(numStr.substring(2), 16);
        else if(numStr.startsWith("0b")) 
          constVal = new BigInteger(numStr.substring(2), 2);
        else if(numStr.startsWith("0h")) 
          constVal = new BigInteger(numStr.substring(2), 8);
        else 
          constVal = new BigInteger(numStr);
        res = encoding.integerConstant(constVal);
				break;
      }
			case LONG_DOUBLE:
			case LONG_DOUBLE_COMPLEX:
			case DOUBLE:
			case DOUBLE_COMPLEX:
			case FLOAT:
			case FLOAT_COMPLEX:
			default:
				throw new IllegalArgumentException("Unsupported data type " + type.toInteger().getKind());
      }        
      return res;
    }

    public Expression visitLogicalAndExpression(GNode node)
        throws ExpressionFactoryException {
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.and(left, right);
    }

    public Expression visitLogicalNegationExpression(GNode node)
        throws ExpressionFactoryException {
      return encodeBoolean(node.getNode(0), true);
    }

    public Expression visitLogicalOrExpression(GNode node)
        throws ExpressionFactoryException {
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.or(left, right);
    }

    public Expression visitPreincrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPredecrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }
    
    public Expression visitPostincrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPostdecrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      return encodeExpression(opNode);
    }

    public Expression visitPrimaryIdentifier(GNode node)
        throws ExpressionFactoryException {
      Expression binding = getLvalBinding(memory, node);
      return derefMemory(memory, binding);
    }

    public Expression visitRelationalExpression(GNode node)
        throws ExpressionFactoryException {
    	String relOp = node.getString(1);
    	Expression left = encodeExpression(node.getNode(0));
    	Expression right = encodeExpression(node.getNode(2));
    	
      Type lType = lookupType(left.getNode()).resolve();
      Type rType = lookupType(right.getNode()).resolve();
      
    	Expression b;
      
    	if(lType.isPointer()) {
    		Preconditions.checkArgument(rType.isPointer());
        if (">".equals(relOp)) {
          b = encoding.pointerGreaterThan(left, right);
        } else if (">=".equals(relOp)) {
        	b = encoding.pointerGreaterThanOrEqual(left, right);
        } else if ("<".equals(relOp)) {
        	b = encoding.pointerLessThan(left, right);
        } else if ("<=".equals(relOp)) {
          b = encoding.pointerLessThanOrEqual(left, right);
        } else {
        	throw new ExpressionFactoryException("Invalid operation: " + relOp);
        }
    	} else {
    		if(Preferences.isSet(Preferences.OPTION_UNSIGNED_OPERATION)) {
          if (">".equals(relOp)) {
            b = encoding.greaterThan(left, right);
          } else if (">=".equals(relOp)) {
          	b = encoding.greaterThanOrEqual(left, right);
          } else if ("<".equals(relOp)) {
          	b = encoding.lessThan(left, right);
          } else if ("<=".equals(relOp)) {
            b = encoding.lessThanOrEqual(left, right);
          } else {
          	throw new ExpressionFactoryException("Invalid operation: " + relOp);
          }
      	} else {
        	if (">".equals(relOp)) {
        		b = encoding.signedGreaterThan(left, right);
        	} else if (">=".equals(relOp)) {
        		b = encoding.signedGreaterThanOrEqual(left, right);
        	} else if ("<".equals(relOp)) {
        		b = encoding.signedLessThan(left, right);
        	} else if ("<=".equals(relOp)) {
        		b = encoding.signedLessThanOrEqual(left, right);
        	} else {
        		throw new ExpressionFactoryException("Invalid operation: " + relOp);
        	}
      	}
      }
      return b;
    }

    public Expression visitSimpleDeclarator(GNode node)
        throws ExpressionFactoryException {
      return visitPrimaryIdentifier(node);
    }

    public Expression visitStringConstant(GNode node)
        throws ExpressionFactoryException {
      //FIXME: make a string constant into integer variable? improper
      return encoding.variable(node.getString(0), IRIntegerType
          .getInstance(), false);
    }
    
    public Expression visitSubscriptExpression(GNode node)
        throws ExpressionFactoryException {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Node baseNode = node.getNode(0);
      Expression index = encodeExpression(node.getNode(1));
      Expression loc = getSubscriptExpression(baseNode, index).setNode(node);
      return derefMemory(memory, loc);
    }
    
    public Expression visitSizeofExpression(GNode node)
        throws ExpressionFactoryException {
        Node typeNode = node.getNode(0);
        Expression res = null;
        if(typeNode.hasProperty(TYPE)) { // pointer type (STRUCT *)
          int size = encoding.getSizeofType(lookupType(typeNode));
          res = encoding.integerConstant(size);
        } else if(typeNode.hasName("PrimaryIdentifier")){
          GNode typedef = GNode.create("TypedefName", typeNode.get(0));
          typedef.setLocation(node.getLocation());
          GNode specifier = GNode.create("SpecifierQualifierList", typedef);
          specifier.setLocation(node.getLocation());
          GNode typename = GNode.create("TypeName", specifier);
          typename.setLocation(node.getLocation());
          res = encodeExpression(typename);
        } else {
          res = encodeExpression(typeNode);
        }
        return res;
//      }
    }
    
    public Expression visitTypeName(GNode node)
        throws ExpressionFactoryException {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitSpecifierQualifierList(GNode node)
        throws ExpressionFactoryException {
      return encodeExpression(node.getNode(0));
    }
    
    public Expression visitInt(GNode node)
        throws ExpressionFactoryException {
      //FIXME: Int() and Char() won't be visited.
      int size = encoding.getSizeofType(lookupType(node));
      return encoding.integerConstant(size);
    }    
    
    public Expression visitChar(GNode node)
        throws ExpressionFactoryException {
      int size = encoding.getSizeofType(lookupType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitPointer(GNode node)
        throws ExpressionFactoryException {
      int size = encoding.getSizeofType(lookupType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitStructureTypeReference(GNode node) 
        throws ExpressionFactoryException {
      int size = encoding.getSizeofType(lookupType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitUnionTypeReference(GNode node)
        throws ExpressionFactoryException {
      int size = encoding.getSizeofType(lookupType(node));
      return encoding.integerConstant(size);
    }
    
    public Expression visitTypedefName(GNode node) 
        throws ExpressionFactoryException {
      if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) {
        return encodeExpression(node.getNode(0));
      } else {
        Type type = lookupType(node);
        int size = encoding.getSizeofType(type);
        return encoding.integerConstant(size);
      }
    }
    
    public Expression visitUnaryMinusExpression(GNode node) 
        throws ExpressionFactoryException {
      Expression rhs = encodeExpression(node.getNode(0));
      return encoding.uminus(rhs); 
    }
    
    public Expression visitMultiplicativeExpression(GNode node) 
        throws ExpressionFactoryException {
      // TODO: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
      return binaryOp(node, this, 
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
        @Override
        public Expression apply(Expression left, String multOperator, 
            Expression right) {
          try {
            if ("*".equals(multOperator)) {
              return encoding.times(coerceToInteger(left), coerceToInteger(right));
              } else if ("/".equals(multOperator)) {
                if(!Preferences.isSet(Preferences.OPTION_UNSIGNED_OPERATION))
                  return encoding.signedDivide(coerceToInteger(left), coerceToInteger(right));
                else
                  return encoding.divide(coerceToInteger(left), coerceToInteger(right));
                } else if ("%".equals(multOperator)) {
                  if(!Preferences.isSet(Preferences.OPTION_UNSIGNED_OPERATION))
                    return encoding.signedRem(coerceToInteger(left), coerceToInteger(right));
                  else
                    return encoding.rem(coerceToInteger(left), coerceToInteger(right));
                  } else {
                    throw new ExpressionFactoryException("Invalid operation: " + multOperator);
                  }
            } catch (ExpressionFactoryException e) {
              throw new ComputationException(e);
              }
          }
        });
      }
    
    public Expression visitDirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      int offset = getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = lvalVisitor.encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      return derefMemory(memory, resLoc.setNode(node));
    }
    
    public Expression visitIndirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref =  type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();   
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      int offset = getOffset(baseType.toStructOrUnion(), fieldName);
      Expression baseLoc = encodeExpression(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.pointerPlus(coerceToPointer(baseLoc), coerceToInteger(offsetExpr));
      return derefMemory(memory, resLoc.setNode(node));
    }

		private Expression derefMemory(Expression memory, Expression lvalExpr) {
		  /* lvalExpr's node with no type info, get it for BurstallMemoryModel analysis. */
		  Expression resExpr = null;
		  
		  GNode srcNode = lvalExpr.getNode();
		  Type t = lookupType(srcNode).resolve();
		  if(t.isArray() || t.isStruct() || t.isUnion())
		    resExpr = lvalExpr;
		  else
		    resExpr = getMemoryModel().deref(memory, lvalExpr);   
		  return resExpr.setNode(srcNode);
		}

		private Expression getSubscriptExpression(Node node, Expression idx) {
		  Type type = lookupType(node).resolve();
		  assert(type.isArray() || type.isPointer());
		
		  if(!(node.hasName("SubscriptExpression"))) {
		    if(type.isPointer()) {
		      Expression base = encodeExpression(node);
		      Type ptoType = type.toPointer().getType();
		      Expression factor = encoding.integerConstant(encoding.getSizeofType(ptoType));
		      Expression newIdx = encoding.times(idx, factor);
		      return encoding.pointerPlus(base, newIdx);
		    } else {
		      Expression base = lvalVisitor.encodeExpression(node);
		      Type cellType = type.toArray().getType();
		      Expression factor = encoding.integerConstant(encoding.getSizeofType(cellType));
		      Expression newIdx = encoding.times(idx, factor);
		      return encoding.pointerPlus(base, newIdx);
		    }
		  }
		  
		  if(type.isArray()) {
		    Node nestedBaseNode = node.getNode(0);
		    Node nestedIdxNode = node.getNode(1);
		    Expression nestIdx = encodeExpression(nestedIdxNode);
//		    Expression factor = encoding.integerConstant((int)((ArrayT) type).getLength());
//		    Expression newIdx = encoding.plus(encoding.times(nestIdx, factor), idx);
//		    return getSubscriptExpression(nestedBaseNode, newIdx);
		    Expression nestIdxWithType = getSubscriptExpression(nestedBaseNode, nestIdx);
		    Type cellType = type.toArray().getType();
	    	Expression factor = encoding.integerConstant(encoding.getSizeofType(cellType));
	    	Expression idxWithType = encoding.times(idx, factor);
	    	return encoding.pointerPlus(nestIdxWithType, idxWithType);
		  } else {
		    Expression base = encodeExpression(node);
		    Type ptoType = type.toPointer().getType();
		    Expression factor = encoding.integerConstant(encoding.getSizeofType(ptoType));
		    Expression newIdx = encoding.times(idx, factor);
		    return encoding.pointerPlus(base, newIdx);
		  }   
		}
  }
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
    private final Expression memory;
    private final ExpressionVisitor exprVisitor;
    
    private LvalVisitor() {
      this.exprVisitor = new ExpressionVisitor();
      this.memory = exprVisitor.memory;
    }

    private LvalVisitor(ExpressionVisitor exprVisitor) {
      this.exprVisitor = exprVisitor;
      this.memory = exprVisitor.memory;
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

    public ExpressionClosure toLval(Node node) {
      return getMemoryModel().suspend(memory, encodeExpression(node));
    }
    
    public Expression visitIndirectionExpression(GNode node)
        throws ExpressionFactoryException {
      Expression op = exprVisitor.encodeExpression(node.getNode(0));
      Type type = lookupType(node);
      IOUtils.debug().pln(
          "Indirection expression type: " + type.tag() + type.getName()
              + type.resolve().getName()).flush();
      return op;
    }

    public Expression visitPrimaryIdentifier(GNode node)
        throws ExpressionFactoryException {
      return getLvalBinding(memory, node);
    }

    public Expression visitSimpleDeclarator(GNode node)
        throws ExpressionFactoryException {
      return visitPrimaryIdentifier(node);
    }
    
    public Expression visitAdditiveExpression(GNode node) 
        throws ExpressionFactoryException {
      return exprVisitor.encodeExpression(node);
    }
    
    public Expression visitSubscriptExpression(GNode node) 
        throws ExpressionFactoryException {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Node baseNode = node.getNode(0);
      Node idxNode = node.getNode(1);
      Expression index = exprVisitor.encodeExpression(idxNode);
      return getSubscriptExpression(baseNode, index);
    }
    
    public Expression visitDirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      int offset = getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      // r.balance = addr_of_r + offset(balance), not m[addr_of_r] + offset(balance)
      Expression baseLoc = encodeExpression(node.getNode(0));
      return encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
    }
    
    public Expression visitFunctionCall(GNode node) throws ExpressionFactoryException {
      return exprVisitor.visitFunctionCall(node);
    }
    
    public Expression visitIndirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();
      assert(baseType.isStruct() || baseType.isUnion());
      String fieldName = ref.getField();
      int offset = getOffset(baseType.toStructOrUnion(), fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression baseLoc = exprVisitor.encodeExpression(node.getNode(0));
      return encoding.pointerPlus(coerceToPointer(baseLoc), 
      		coerceToInteger(offsetExpr));
    }

    public Expression visitParameterDeclaration(GNode node) 
        throws ExpressionFactoryException {
      return encodeExpression(node.getNode(1));
    }
    
    public Expression visitPointerDeclarator(GNode node) 
        throws ExpressionFactoryException {
      return encodeExpression(node.getNode(1));
    }

		private Expression getSubscriptExpression(Node node, Expression idx) {
		  Type type = lookupType(node).resolve();
		  assert(type.isArray() || type.isPointer());
		
		  if(!(node.hasName("SubscriptExpression"))) {
		    if(type.isPointer()) {
		      Expression base = exprVisitor.encodeExpression(node);
		      Type ptoType = type.toPointer().getType();
		      Expression factor = encoding.integerConstant(encoding.getSizeofType(ptoType));
		      Expression newIdx = encoding.times(idx, factor);
		      return encoding.pointerPlus(base, newIdx);
		    } else {
		      Expression base = encodeExpression(node);
		      Type cellType = type.toArray().getType();
		      Expression factor = encoding.integerConstant(encoding.getSizeofType(cellType));
		      Expression newIdx = encoding.times(idx, factor);
		      return encoding.pointerPlus(base, newIdx);
		    }
		  }
		  
		  if(type.isArray()) {
		    Node nestedBaseNode = node.getNode(0);
		    Node nestedIdxNode = node.getNode(1);
		    Expression nestIdx = exprVisitor.encodeExpression(nestedIdxNode);
//		    Expression factor = encoding.integerConstant((int)((ArrayT) type).getLength());
//		    Expression newIdx = encoding.plus(encoding.times(nestIdx, factor), idx);
//		    return getSubscriptExpression(nestedBaseNode, newIdx);
		    Expression nestIdxWithType = getSubscriptExpression(nestedBaseNode, nestIdx);
		    Type cellType = type.toArray().getType();
		    Expression factor = encoding.integerConstant(encoding.getSizeofType(cellType));
	    	Expression idxWithType = encoding.times(idx, factor);
		    return encoding.pointerPlus(nestIdxWithType, idxWithType);	    
		  } else {
		    Expression base = exprVisitor.encodeExpression(node);
		    Type ptoType = type.toPointer().getType();
		    Expression factor = encoding.integerConstant(encoding.getSizeofType(ptoType));
		    Expression newIdx = encoding.times(idx, factor);
		    return encoding.pointerPlus(base, newIdx);
		  }  
		}
  }
  
  
  @Override
  public void setScope(Scope scope) {
    this.scope = scope;
  }
  
  @Override
  public ExpressionClosure toBoolean(Node node) {
    return new ExpressionVisitor().toBoolean(node);
  }

  @Override
  public ExpressionClosure toBoolean(Node node, boolean negated) {
    return new ExpressionVisitor().toBoolean(node,negated);
  }

  @Override
  public ExpressionClosure toExpression(Node node) {
    return new ExpressionVisitor().toExpression(node);
  }

  @Override
  public ExpressionClosure toLval(Node node) {
    return new LvalVisitor().toLval(node);
  }

  @Override
  public ExpressionClosure toBoolean(Node node, Scope scope) {
    return toBoolean(node,false,scope);
  }

  @Override
  public ExpressionClosure toBoolean(Node node, boolean negated,
      Scope scope) {
    Scope oldScope = this.scope;
    setScope(scope);
    ExpressionClosure closure = toBoolean(node,negated);
    setScope(oldScope);
    return closure;
  }

  @Override
  public ExpressionClosure toExpression(Node node, Scope scope) {
    Scope oldScope = this.scope;
    setScope(scope);
    ExpressionClosure closure = toExpression(node);
    setScope(oldScope);
    return closure;
  }

  @Override
  public ExpressionClosure toLval(Node node, Scope scope) {
    Scope oldScope = this.scope;
    setScope(scope);
    ExpressionClosure closure = toLval(node);
    setScope(oldScope);
    return closure;
  }

  public static CExpressionEncoder create(
      ExpressionEncoding encoding, MemoryModel memoryModel,
      Map<File, ? extends SymbolTable> symbolTables) {
    IOUtils.debug().pln(
        "Creating CExpressionEncoder with encoding: " + encoding);
    return new CExpressionEncoder(encoding, memoryModel,
        symbolTables);
  }
  
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  private final Map<File, ? extends SymbolTable> symbolTables;
  private Scope scope;

  private static final String VAR_EXPR_MAP = "_Expression_Interpreter_Var_Expr_Map";
  private static final String VAR_PREFIX = "addr_of_";
  
  private C cAnalyzer;

  private CExpressionEncoder(ExpressionEncoding encoding,
      MemoryModel memoryModel,
      Map<File, ? extends SymbolTable> symbolTables) {
    this.encoding = encoding;
    this.memoryModel = memoryModel;
    this.symbolTables = symbolTables;
    scope = null;
    cAnalyzer = encoding.getCAnalyzer();
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public MemoryModel getMemoryModel() {
    return memoryModel;
  }

  @Override
	public Scope getCurrentScope() {
		return scope;
	}

	/**
	 * Returns an expression representing the lvalue of the given name. I.e.,
	 * <code>lookupVar(x)</code> will return an expression representing
	 * <code>&x</code>. The rvalue of <code>x</code> is
	 * <code>exprFactory.deref(lookupVar(x))</code>.
	 * */
	private Expression getLvalBinding(Expression memory, GNode node) throws ExpressionFactoryException {
	  IRVarInfo varInfo = lookupVar(node);
	  Expression iExpr = null;
	  if (varInfo.hasProperty(VAR_EXPR_MAP)) {
	    // TODO: map expressions per-factory
	    iExpr = (Expression) varInfo.getProperty(VAR_EXPR_MAP);     
	  } else {
	  	String name = VAR_PREFIX + varInfo.getName();
	    iExpr = getMemoryModel().createLval(memory, name, varInfo, node);
	    varInfo.setProperty(CExpressionEncoder.VAR_EXPR_MAP, iExpr);     
	  }
	  return iExpr.setNode(node);
	}

	/**
   * Return the symbol table binding for a variable.
   */
  private IRVarInfo lookupVar(GNode node) throws ExpressionFactoryException {
    String name = node.getString(0);
    File file = new File(node.getLocation().file);
    SymbolTable symbolTable = symbolTables.get(file);
    if (symbolTable == null) {
      throw new ExpressionFactoryException("Symbol table not found for file: "
          + file);
    }
    
    IRVarInfo varInfo = null;
    if(!scope.isDefined(name)) {
    	// quantified variable, no need to add in symbol table
    	varInfo = new VarInfo(symbolTable.getScope(CType.getScopeName(node)), 
      		name, IRIntegerType.getInstance(), node);
    	symbolTable.define(name, varInfo);
    } else {
      symbolTable.setScope(scope);
      varInfo = symbolTable.lookup(name);
      if (varInfo == null)
        throw new ExpressionFactoryException("Variable not found: " + name);
    }
    
    return varInfo;
  }
  

  
  private Map<String, Integer> getOffsetMap(Type t) {
    Preconditions.checkArgument(t.isStruct());
    Map<String, Integer> resMap = Maps.newHashMap();
    for(VariableT mem: t.toStruct().getMembers()) {
      if(!(mem.getType().isPointer() 
          && ((PointerT) mem.getType()).getType().equals(t))) 
        continue;
      String name = mem.getName();
      int off = getOffset(t.toStructOrUnion(), name);
      resMap.put(name, off);
    }
    return resMap;
  }
  
  private int getOffset(StructOrUnionT t, String name) {
    if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)){
      return (int) cAnalyzer.getOffset(t.toStructOrUnion(), name);
    }
    
    StructOrUnionT struct = t.toStructOrUnion();
    if(struct.isUnion()) return 0;
    
    Iterator<VariableT> itr = struct.getMembers().iterator();
    int offset = 0;
    while(itr.hasNext()) {
      VariableT elem = (VariableT) itr.next();
      String elemName = elem.getName();
      if(elemName.equals(name)) {
        return offset;
      }
      int elemTypeSize = encoding.getSizeofType(elem.getType());
      offset += elemTypeSize;
    }
    return -1;
  }

//  private Type unwrapped(Type type) {
//    while(type.isAnnotated() || type.isAlias() || type.isVariable()) {
//      type = type.resolve();
//      type = type.deannotate();
//    }
//    return type;
//  }
  
  private Type lookupType(Node node) {
    if(node.hasProperty(TYPE)) {
      Type type = CType.getType(node);
      if(!type.equals(ErrorT.TYPE)) {
        return type;
      }
    }
    throw new IllegalArgumentException("Unknown type for node " + node);
  }
}
