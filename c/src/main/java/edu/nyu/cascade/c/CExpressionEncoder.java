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
import xtc.Constants;
import xtc.type.AnnotatedT;
import xtc.type.BooleanT;
import xtc.type.DynamicReference;
import xtc.type.FieldReference;
import xtc.type.IndirectReference;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.Reference;
import xtc.type.StructOrUnionT;
import xtc.type.StructT;
import xtc.type.Type;
import xtc.type.ArrayT;
import xtc.type.VariableT;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.ComputationException;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.ReachMemoryModel;
import edu.nyu.cascade.ir.impl.VarInfo;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.RecursionStrategies.BinaryInfixRecursionStrategy;
import edu.nyu.cascade.util.RecursionStrategies.BinaryRecursionStrategy;

class CExpressionEncoder implements ExpressionEncoder {
  private static final String FUN_VALID = "valid";
  private static final String FUN_VALID_MALLOC = "valid_malloc";
  private static final String FUN_IMPLIES = "implies";
  private static final String FUN_FORALL = "forall";
  private static final String FUN_EXISTS = "exists";
  private static final String FUN_REACH = "reach";
  private static final String FUN_ALLOCATED = "allocated";
  private static final String FUN_ISROOT = "is_root";
  private static final String FUN_CREATE_ACYCLIC_LIST = "create_acyclic_list";
  private static final String FUN_CREATE_CYCLIC_LIST = "create_cyclic_list";
  private static final String FUN_CREATE_ACYCLIC_DLIST = "create_acyclic_dlist";
  private static final String FUN_CREATE_CYCLIC_DLIST = "create_cyclic_dlist";
  
  @SuppressWarnings("unused")
  private class ExpressionVisitor extends Visitor {
    private final Expression memory;
    // New field lvalVisitor to keep code DRY.
    private final LvalVisitor lvalVisitor;
    
    public ExpressionVisitor() {
      memory = getMemoryModel().freshState();
      lvalVisitor = new LvalVisitor(this);
    }
    
    public ExpressionClosure toBoolean(Node node) {
      return toBoolean(node, false);
    }

    ExpressionClosure suspend(Expression expr) {
      return getMemoryModel().suspend(memory, expr);
    }
    
    public ExpressionClosure toBoolean(Node node, boolean negated) {
      return suspend(encodeBoolean(node,negated));
    }

    public ExpressionClosure toInteger(Node node) {
      return suspend(encodeInteger(node));
    }

    Expression encodeBoolean(Node node) { return encodeBoolean(node, false).setNode((GNode) node); }
    
    Expression encodeBoolean(Node node, boolean negated) {
      Expression b = coerceToBoolean((Expression) dispatch(node));
      return negated ? encoding.not(b) : b;
    }

    Expression encodeInteger(Node node) {
      return coerceToInteger((Expression) dispatch(node)).setNode((GNode) node);
    }

    Expression coerceToBoolean(Expression e) {      
      return encoding.isBoolean(e) ? e : encoding.castToBoolean(e);
    }
    
    Expression coerceToInteger(Expression e) {       
        return encoding.isInteger(e) ? e : encoding.castToInteger(e);
    }
    
    @Override
    public Expression unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as unknown: "
                  + node.getName());

      try {
        return encoding.unknown();
      } catch (ExpressionFactoryException e) {
        throw new VisitingException("Expression Factory failure", e);
      }
    }
    
    public Expression visitConditionalExpression(GNode node) 
        throws VisitingException {
      Expression condition = encodeBoolean(node.getNode(0));
      Expression trueCase = (Expression) dispatch(node.getNode(1));
      Expression falseCase = (Expression) dispatch(node.getNode(2));
      return getExpressionManager().ifThenElse(condition, trueCase, falseCase);
    }

    public Expression visitAdditiveExpression(GNode node)
        throws VisitingException {
      // FIXED: handle varying pointer sizes
      /* [chris 12/3/2010] Note that this ignores pointer arithmetic, so any 
       * non-char* arithmetic will be wrong
       */
      IOUtils.debug().pln("APPROX: Possible pointer arithmetic treated as char*");
      Expression res = binaryOp(node, this,
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression left, String additiveOperator,
                Expression right) {
              try {
                Type leftType = lookupType(left.getNode());
                Type rightType = lookupType(right.getNode());
                
                // multiplied by the size of the type of the pointer
                if(leftType.isPointer() && rightType.isPointer())
                  throw new IllegalArgumentException("No arithmetic operation between pointers.");
                
                if(leftType.isPointer()) {
                  PointerT pointerT = leftType.toPointer();
                  Type type = pointerT.getType();
                  right = encoding.times(coerceToInteger(right), encoding.integerConstant(sizeofType(type)));
                } 
                if(rightType.isPointer()) {
                  PointerT pointerT = rightType.toPointer();
                  Type type = pointerT.getType();
                  left = encoding.times(coerceToInteger(left), encoding.integerConstant(sizeofType(type)));
                }
                
                if ("+".equals(additiveOperator)) {
                  return encoding.plus(coerceToInteger(left), coerceToInteger(right));
                } else if ("-".equals(additiveOperator)) {
                  return encoding.minus(coerceToInteger(left), coerceToInteger(right));
                } else {
                  throw new ExpressionFactoryException("Invalid operation: " + additiveOperator);
                }
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          });
      return res.setNode(node);
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
      return res.setNode(node);
    }

    public Expression visitAddressExpression(GNode node) {
      Expression content = (Expression) dispatch(node.getNode(0));
      Expression address = getMemoryModel().addressOf(content); 
      return address.setNode(node);
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
                  return encoding.plus(coerceToInteger(left), coerceToInteger(right));
                } else if ("-=".equals(assignmentOperator)) {
                  return encoding.minus(coerceToInteger(left), coerceToInteger(right));
                } else {
                  throw new UnsupportedOperationException(assignmentOperator);
                }
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          }).setNode(node);
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
      }).setNode(node);
    }

    public Expression visitCastExpression(GNode node) {
      /* TODO: Deal with conversions */
      IOUtils.debug().pln("Treating cast as no-op.");
      Type targetType = lookupType(node.getNode(0));
      typeTable.put(node.getNode(1).toString(), targetType);
      Expression res = (Expression) dispatch(node.getNode(1));
      return res.setNode(node);
    }
    
    public Expression visitCharacterConstant(GNode node)
        throws ExpressionFactoryException {
      Type type = (Type) node.getProperty(xtc.Constants.TYPE);
      int constVal = type.getConstant().bigIntValue().intValue();
      Expression res = encoding.integerConstant(constVal);
      return res.setNode(node);
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
                  b = encoding.eq(coerceToInteger(left), coerceToInteger(right));
                } else if ("!=".equals(eqOp)) {
                  b = encoding.neq(coerceToInteger(left), coerceToInteger(right));
                } else {
                  throw new ExpressionFactoryException("Invalid operation: " + eqOp.toString());
                }
                return b;
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          }).setNode(node);
    }

    public List<Expression> visitExpressionList(GNode node) {
      List<Expression> subExprList = Lists.newArrayListWithCapacity(node.size());
      for (Object elem : node) {
        Expression subExpr = (Expression) dispatch((Node) elem);
        subExprList.add(subExpr);
      }
      return subExprList;
    }

    @SuppressWarnings("unchecked")
    public Expression visitFunctionCall(GNode node) throws ExpressionFactoryException {
      Node funNode = node.getNode(0);
      Expression res;
      if ("PrimaryIdentifier".equals(funNode.getName())) {
        String name = funNode.getString(0);
        Node argList = node.getNode(1);
        
        if( FUN_VALID.equals(name) ) {
          Preconditions.checkArgument(argList.size() == 1);
          List<Expression> argExprs = (List<Expression>) dispatch(argList);
          res = encoding.ofBoolean(getMemoryModel().valid(memory, argExprs.get(0)));
        } else if( FUN_VALID_MALLOC.equals(name)) {
          Preconditions.checkArgument(argList.size() == 1);
          List<Expression> argExprs = (List<Expression>) dispatch(argList);
          res = encoding.neq(argExprs.get(0), encoding.zero());
        } else if( FUN_ALLOCATED.equals(name) ) {
          Preconditions.checkArgument(argList.size() == 2);
          Expression argExpr0 = (Expression) lvalVisitor.dispatch(argList.getNode(0));
          Expression argExpr1 = (Expression) dispatch(argList.getNode(1));
          res = encoding.ofBoolean(getMemoryModel().allocated(memory, argExpr0, argExpr1));
        } else if( FUN_IMPLIES.equals(name) ) {
          Preconditions.checkArgument(argList.size() == 2);
          List<Expression> argExprs = (List<Expression>) dispatch(argList);
          res = getExpressionManager().implies(argExprs.get(0), argExprs.get(1));
        } else if( FUN_FORALL.equals(name) || FUN_EXISTS.equals(name)) {
          ExpressionManager exprManager = getExpressionManager();
          List<VariableExpression> argVars = Lists.newArrayList();
          int size = argList.size();
          for(int i=0; i<size-1; i++) {
            GNode argNode = argList.getGeneric(i);
            String argName = argNode.getName().equals("PrimaryIdentifier") ? argNode.getString(0) :
                argNode.getNode(argNode.size()-1).getString(0);
            assert(lookupType(argNode).isInteger());
            int cellSize = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
            VariableExpression argVar = exprManager.variable(argName, exprManager.bitVectorType(cellSize), false);
            argVars.add(argVar);
          }
          List<Expression> args = (List<Expression>) dispatch(argList);
          Expression body = args.remove(size-1).subst(args, argVars);
          if( FUN_FORALL.equals(name) )  
            res = exprManager.forall(argVars, body);
          else  
            res = exprManager.exists(argVars, body);         
        } else if( FUN_REACH.equals(name) ) {
          Preconditions.checkArgument(argList.size() == 3);
          String fieldName = argList.getNode(0).getString(0);
          Expression fromExpr = (Expression) dispatch(argList.getNode(1));
          Expression toExpr = (Expression) dispatch(argList.getNode(2));
          MemoryModel mm = getMemoryModel();
          if(mm instanceof ReachMemoryModel) {
            res = ((ReachMemoryModel) mm).reach(fieldName, fromExpr, toExpr, toExpr);
          } else {
            res = getExpressionManager().ff();         
          }
        } else if( FUN_CREATE_ACYCLIC_LIST.equals(name) || 
            FUN_CREATE_CYCLIC_LIST.equals(name) ||
            FUN_CREATE_ACYCLIC_DLIST.equals(name) ||
            FUN_CREATE_CYCLIC_DLIST.equals(name)) {
          Preconditions.checkArgument(argList.size() == 2);
          Node ptrNode = argList.getNode(0);
          Expression ptrExpr = (Expression) lvalVisitor.dispatch(ptrNode);
          Expression length = (Expression) dispatch(argList.getNode(1));
          Type type = lookupType(ptrNode).toPointer().getType().resolve();
          int size = sizeofType(type);
          Map<String, Integer> fldOff = getFieldOffset(type);
          
          MemoryModel mm = getMemoryModel();
          if(mm instanceof ReachMemoryModel) {
            if(FUN_CREATE_ACYCLIC_LIST.equals(name))
              res = ((ReachMemoryModel) mm).create_list(memory,
                  ptrExpr, length, size, fldOff, true, true);
            else if(FUN_CREATE_CYCLIC_LIST.equals(name))
              res = ((ReachMemoryModel) mm).create_list(memory,
                  ptrExpr, length, size, fldOff, false, true);
            else if(FUN_CREATE_ACYCLIC_DLIST.equals(name))
              res = ((ReachMemoryModel) mm).create_list(memory,
                  ptrExpr, length, size, fldOff, true, false);
            else
              res = ((ReachMemoryModel) mm).create_list(memory,
                  ptrExpr, length, size, fldOff, false, false);
          } else {
            res = getExpressionManager().tt();
          }
        } else if( FUN_ISROOT.equals(name) ) {
          Preconditions.checkArgument(argList.size() == 2);
          String fieldname = argList.getNode(0).getString(0);
          Expression ptrExpr = (Expression) dispatch(argList.getNode(1));
          MemoryModel mm = getMemoryModel();
          if(mm instanceof ReachMemoryModel) {
            res = ((ReachMemoryModel) mm).isRoot(fieldname, ptrExpr);
          } else {
            throw new ExpressionFactoryException("Invalid memory model.");
          }
        }else {
          List<Expression> argExprs = (List<Expression>) dispatch(argList);
          res = encoding.functionCall(name, argExprs);
        }
      } else {
        IOUtils.debug().pln(
            "APPROX: Treating unexpected function call as unknown: "
                + node.getName());
        res = encoding.unknown();
      }
      return res.setNode(node);
    }

    public Expression visitIndirectionExpression(GNode node)
        throws ExpressionFactoryException {
      lookupType(node);
      Expression op = (Expression) dispatch(node.getNode(0));
      Expression res = getMemoryModel().deref(memory, op.setNode(node));
      return res.setNode(node);
    }

    public Expression visitIntegerConstant(GNode node)
        throws ExpressionFactoryException {
      Type type = unwrapped(lookupType(node));     
      assert(type.isInteger());
      
      Expression res;
      if(type.hasConstant()) {
        // Parse string character
        BigInteger constVal = (BigInteger) type.getConstant().getValue();
        res = encoding.integerConstant(constVal.intValue());
      } else {
        String numStr = node.getString(0);
        // for unsigned integer
        if(numStr.lastIndexOf('U') >= 0) 
          numStr = numStr.substring(0, numStr.lastIndexOf('U'));
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
      }
      return res.setNode(node);
    }

    public Expression visitLogicalAndExpression(GNode node)
        throws ExpressionFactoryException {
      /*
       * IBooleanExpression left = ExpressionFactory.exprToBoolean(exprManager,
       * (Expression) dispatch(node.getNode(0))); IBooleanExpression right =
       * ExpressionFactory.exprToBoolean(exprManager, (Expression)
       * dispatch(node.getNode(1)));
       */
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.and(left, right).setNode(node);
    }

    public Expression visitLogicalNegationExpression(GNode node)
        throws ExpressionFactoryException {
      return encodeBoolean(node.getNode(0), true).setNode(node);
    }

    public Expression visitLogicalOrExpression(GNode node)
        throws ExpressionFactoryException {
      Expression left = encodeBoolean(node.getNode(0));
      Expression right = encodeBoolean(node.getNode(1));
      return encoding.or(left, right).setNode(node);
    }

    public Expression visitPreincrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      Expression res = (Expression) dispatch(opNode);
      return res.setNode(node);
    }

    public Expression visitPredecrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      Expression res = (Expression) dispatch(opNode);
      return res.setNode(node);
    }
    
    public Expression visitPostincrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      Expression res = (Expression) dispatch(opNode);
      return res.setNode(node);
    }

    public Expression visitPostdecrementExpression(GNode node)
        throws ExpressionFactoryException {
      Node opNode = node.getNode(0);
      Expression res = (Expression) dispatch(opNode);
      return res.setNode(node);
    }

    public Expression visitPrimaryIdentifier(GNode node)
        throws ExpressionFactoryException {
      Expression binding = getLvalBinding(node);
      Expression res = derefMemory(memory, binding);
      return res.setNode(node);
    }

    public Expression visitRelationalExpression(GNode node)
        throws ExpressionFactoryException {
      return binaryOp(node, this,
          new BinaryInfixRecursionStrategy<Expression, Expression>() {
            @Override
            public Expression apply(Expression left, String relOp, Expression right) {
              try {
                Expression b;
                if (">".equals(relOp)) {
                  if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
                    b = encoding.signedLessThan(coerceToInteger(right), coerceToInteger(left));
                  else
                    b = encoding.lessThan(coerceToInteger(right), coerceToInteger(left));
                } else if (">=".equals(relOp)) {
                  if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
                    b = encoding.signedLessThanOrEqual(coerceToInteger(right), coerceToInteger(left));
                  else
                    b = encoding.lessThanOrEqual(coerceToInteger(right), coerceToInteger(left));
                } else if ("<".equals(relOp)) {
                  if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
                    b = encoding.signedLessThan(coerceToInteger(left), coerceToInteger(right));
                  else
                    b = encoding.lessThan(coerceToInteger(left), coerceToInteger(right));
                } else if ("<=".equals(relOp)) {
                  if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
                    b = encoding.signedLessThanOrEqual(coerceToInteger(left), coerceToInteger(right));
                  else
                    b = encoding.lessThanOrEqual(coerceToInteger(left), coerceToInteger(right));
                } else {
                  throw new ExpressionFactoryException("Invalid operation: " + relOp);
                }
                return b;
              } catch (ExpressionFactoryException e) {
                throw new ComputationException(e);
              }
            }
          }).setNode(node);
    }

    public Expression visitSimpleDeclarator(GNode node)
        throws ExpressionFactoryException {
      return visitPrimaryIdentifier(node).setNode(node);
    }

    public Expression visitStringConstant(GNode node)
        throws ExpressionFactoryException {
      //FIXME: make a string constant into integer variable? improper
      return encoding.variable(node.getString(0), IRIntegerType
          .getInstance(), false).setNode(node);
    }
    
    private Expression getSubscriptExpression(Node node, Expression idx) {
      Type type = unwrapped(lookupType(node));
      assert(type.isArray() || type.isPointer());

      if(!("SubscriptExpression".equals(node.getName()))) {
        Expression base = (Expression) dispatch(node);
        return encoding.plus(base, idx);
      }
      
      if(type.isArray()) {
        Node nestedBaseNode = node.getNode(0);
        Node nestedIdxNode = node.getNode(1);
        Expression nestIdx = (Expression) dispatch(nestedIdxNode);
        Expression factor = encoding.integerConstant((int)((ArrayT) type).getLength());
        Expression newIdx = encoding.plus(encoding.times(nestIdx, factor), idx);
        return getSubscriptExpression(nestedBaseNode, newIdx);    
      } else {
        Expression baseExpr = (Expression) dispatch(node);
        return encoding.plus(baseExpr, idx);
      }   
    }

    public Expression visitSubscriptExpression(GNode node)
        throws ExpressionFactoryException {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Node baseNode = node.getNode(0);
      Expression index = (Expression) dispatch (node.getNode(1));
      Expression loc = getSubscriptExpression(baseNode, index).setNode(node);
      return derefMemory(memory, loc).setNode(node);
    }
    
    public Expression visitSizeofExpression(GNode node)
        throws ExpressionFactoryException {
      Node typeNode = node.getNode(0);
      Expression res;
      if(typeNode.hasProperty(xtc.Constants.TYPE)) { // pointer type (STRUCT *)
        int size = sizeofType(lookupType(typeNode));
        return encoding.integerConstant(size).setNode(node);
      } else if(typeNode.getName().equals("PrimaryIdentifier")){
        GNode typedef = GNode.create("TypedefName", typeNode.get(0));
        typedef.setLocation(node.getLocation());
        GNode specifier = GNode.create("SpecifierQualifierList", typedef);
        specifier.setLocation(node.getLocation());
        GNode typename = GNode.create("TypeName", specifier);
        typename.setLocation(node.getLocation());
        res = (Expression)dispatch(typename);
      } else {
        res = (Expression)dispatch(typeNode);
      }
      return res.setNode(node);
    }
    
    public Expression visitTypeName(GNode node)
        throws ExpressionFactoryException {
      Expression res = (Expression)dispatch(node.getNode(0));
      return res.setNode(node);
    }
    
    public Expression visitSpecifierQualifierList(GNode node)
        throws ExpressionFactoryException {
      Expression res = (Expression)dispatch(node.getNode(0));
      return res.setNode(node);
    }
    
    public Expression visitInt(GNode node)
        throws ExpressionFactoryException {
      return encoding.integerConstant(1).setNode(node);
    }    
    
    public Expression visitChar(GNode node)
        throws ExpressionFactoryException {
      return encoding.integerConstant(1).setNode(node);
    }
    
    public Expression visitPointer(GNode node)
        throws ExpressionFactoryException {
      return encoding.integerConstant(1).setNode(node);
    }
    
    public Expression visitStructureTypeReference(GNode node) 
        throws ExpressionFactoryException {
      int size = sizeofType(lookupType(node));
      return encoding.integerConstant(size).setNode(node);
    }
    
    public Expression visitUnionTypeReference(GNode node)
        throws ExpressionFactoryException {
      int size = sizeofType(lookupType(node));
      return encoding.integerConstant(size).setNode(node);
    }
    
    public Expression visitTypedefName(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      int size = sizeofType(type);
      return encoding.integerConstant(size).setNode(node);
    }
    
    public Expression visitUnaryMinusExpression(GNode node) 
        throws ExpressionFactoryException {
      Expression rhs = (Expression)dispatch(node.getNode(0));
      
      return encoding.minus(encoding.zero(), rhs).setNode(node); 
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
                if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
                  return encoding.signedDivide(coerceToInteger(left), coerceToInteger(right));
                else
                  return encoding.divide(coerceToInteger(left), coerceToInteger(right));
                } else if ("%".equals(multOperator)) {
                  if(Preferences.isSet(Preferences.OPTION_SIGNED_OPERATION))
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
        }).setNode(node);
      }
    
    public Expression visitDirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();   
      String fieldName = ref.getField();
      int offset = getOffsetOfField(baseType, fieldName);
      if(offset == -1) 
        throw new ExpressionFactoryException("Invalid offset: " + fieldName);
      Expression baseLoc = (Expression) lvalVisitor.dispatch(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.plus(baseLoc, offsetExpr);
      Expression res = derefMemory(memory, resLoc.setNode(node));
      return res.setNode(node);
    }
    
    public Expression visitIndirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref =  type.getShape();
      assert(ref.hasBase() && ref.hasField());
      Type baseType = ref.getBase().getType();   
      String fieldName = ref.getField();
      int offset = getOffsetOfField(baseType, fieldName);
      if(offset == -1) 
        throw new ExpressionFactoryException("Invalid offset: " + fieldName);
      
      Expression baseLoc = (Expression)dispatch(node.getNode(0));
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression resLoc = encoding.plus(baseLoc, offsetExpr);
      Expression res = derefMemory(memory, resLoc.setNode(node));
      return res.setNode(node);
    }
  }
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
    private final Expression memory;
    // New field exprVisitor to keep code DRY.
    private final ExpressionVisitor exprVisitor;
    
    LvalVisitor() {
      this.exprVisitor = new ExpressionVisitor();
      this.memory = exprVisitor.memory;
    }

    LvalVisitor(ExpressionVisitor exprVisitor) {
      this.exprVisitor = exprVisitor;
      this.memory = exprVisitor.memory;
    }

    public ExpressionClosure toLval(Node node) {
      /** For Declarator expr, its source node without type info. 
       *  Find it for BurstallMemoryModel to analyze. 
       */
      if(!node.hasProperty(xtc.Constants.TYPE))
        node.setProperty(xtc.Constants.TYPE, lookupType(node));
      return getMemoryModel().suspend(memory, (Expression)dispatch(node));
    }
    
    public Expression visitIndirectionExpression(GNode node)
        throws ExpressionFactoryException {
      Expression op = (Expression) exprVisitor.dispatch(node.getNode(0));
      xtc.type.Type type = (xtc.type.Type) node.getProperty(Constants.TYPE);
      IOUtils.debug().pln(
          "Indirection expression type: " + type.tag() + type.getName()
              + type.resolve().getName()).flush();
      return op.setNode(node);
    }

    public Expression visitPrimaryIdentifier(GNode node)
        throws ExpressionFactoryException {
      return getLvalBinding(node).setNode(node);
    }

    public Expression visitSimpleDeclarator(GNode node)
        throws ExpressionFactoryException {
      return visitPrimaryIdentifier(node);
    }
    
    public Expression visitAdditiveExpression(GNode node) 
        throws ExpressionFactoryException {
      return (Expression) exprVisitor.dispatch(node);
    }
    
    private Expression getSubscriptExpression(Node node, Expression idx) {
      Type type = unwrapped(lookupType(node));
      assert(type.isArray() || type.isPointer());

      if(!("SubscriptExpression".equals(node.getName()))) {
        Expression base = (Expression) exprVisitor.dispatch(node);
        return encoding.plus(base, idx);
      }
      
      if(type.isArray()) {
        Node nestedBaseNode = node.getNode(0);
        Node nestedIdxNode = node.getNode(1);
        Expression nestIdx = (Expression) exprVisitor.dispatch(nestedIdxNode);
        Expression factor = encoding.integerConstant((int)((ArrayT) type).getLength());
        Expression newIdx = encoding.plus(encoding.times(nestIdx, factor), idx);
        return getSubscriptExpression(nestedBaseNode, newIdx);    
      } else {
        Expression base = (Expression) exprVisitor.dispatch(node); 
        return encoding.plus(base, idx);
      }  
    }
    
    public Expression visitSubscriptExpression(GNode node) 
        throws ExpressionFactoryException {
      IOUtils.debug().pln(
          "APPROX: Treating pointer as char*");
      Node baseNode = node.getNode(0);
      Node idxNode = node.getNode(1);
      Expression index = (Expression) exprVisitor.dispatch(idxNode);
      return getSubscriptExpression(baseNode, index).setNode(node);
    }
    
    public Expression visitDirectComponentSelection(GNode node) 
        throws ExpressionFactoryException {
      Type type = lookupType(node);
      assert(type.hasShape());
      Reference ref = type.getShape();
      Type baseType = ref.getBase().getType();   
      String fieldName = ref.getField();
      int offset = getOffsetOfField(baseType, fieldName);
      if(offset == -1) 
        throw new ExpressionFactoryException("Invalid offset: " + fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      // r.balance = addr_of_r + offset(balance), not m[addr_of_r] + offset(balance)
      Expression baseLoc = (Expression) dispatch(node.getNode(0));
      return encoding.plus(baseLoc, offsetExpr).setNode(node);
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
      String fieldName = ref.getField();
      int offset = getOffsetOfField(baseType, fieldName);
      if(offset == -1) 
        throw new ExpressionFactoryException("Invalid offset: " + fieldName);
      Expression offsetExpr = encoding.integerConstant(offset);
      Expression basePtr = (Expression) dispatch(node.getNode(0));
      Expression baseLoc = derefMemory(memory, basePtr);
      return encoding.plus(baseLoc, offsetExpr).setNode(node);
    }

    public Expression visitParameterDeclaration(GNode node) 
        throws ExpressionFactoryException {
      Expression res = (Expression) dispatch(node.getNode(1));
      return res.setNode(node);
    }
    
    public Expression visitPointerDeclarator(GNode node) 
        throws ExpressionFactoryException {
      Expression res = (Expression) dispatch(node.getNode(1));
      return res.setNode(node);
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
  public ExpressionClosure toInteger(Node node) {
    return new ExpressionVisitor().toInteger(node);
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
  public ExpressionClosure toInteger(Node node, Scope scope) {
    Scope oldScope = this.scope;
    setScope(scope);
    ExpressionClosure closure = toInteger(node);
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
  private Map<String, Type> typeTable;

  private Scope scope;

  private static final String VAR_EXPR_MAP = "_Expression_Interpreter_Var_Expr_Map";
  private static final String VAR_PREFIX = "addr_of_";

  private CExpressionEncoder(ExpressionEncoding encoding,
      MemoryModel memoryModel,
      Map<File, ? extends SymbolTable> symbolTables) {
    this.encoding = encoding;
    this.memoryModel = memoryModel;
    this.symbolTables = symbolTables;
    typeTable = Maps.newHashMap();
    scope = null;
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return getEncoding().getExpressionManager();
  }

  /**
   * Returns an expression representing the lvalue of the given name. I.e.,
   * <code>lookupVar(x)</code> will return an expression representing
   * <code>&x</code>. The rvalue of <code>x</code> is
   * <code>exprFactory.deref(lookupVar(x))</code>.
   * */
  private Expression getLvalBinding(GNode node) throws ExpressionFactoryException {
    IRVarInfo varInfo = lookupVar(node);
    Expression iExpr = null;
    if (varInfo.hasProperty(VAR_EXPR_MAP)) {
      // TODO: map expressions per-factory
      iExpr = (Expression) varInfo.getProperty(VAR_EXPR_MAP);     
    } else {
      iExpr = getMemoryModel().createLval(VAR_PREFIX + node.getString(0));
      varInfo.setProperty(CExpressionEncoder.VAR_EXPR_MAP, iExpr);     
    }
    return iExpr.setNode(node);
  }

  @Override
  public MemoryModel getMemoryModel() {
    return memoryModel;
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
    symbolTable.setScope(scope);
    if (!symbolTable.isDefined(name))   addVar(node);
    IRVarInfo varInfo = symbolTable.lookup(name);
    if (varInfo == null) {
      throw new ExpressionFactoryException("Variable not found: " + name);
    } else {
      return varInfo;
    }
  }
  
  private void addVar(GNode node) throws ExpressionFactoryException {
    String name = node.getString(0);
    File file = new File(node.getLocation().file);
    SymbolTable symbolTable = symbolTables.get(file);
    if (symbolTable == null) {
      throw new ExpressionFactoryException("Symbol table not found for file: "
          + file);
    }
    symbolTable.setScope(scope);
    
    if(!symbolTable.isDefined(name)) {    
      IRType itype = IRIntegerType.getInstance();    
      IRVarInfo varInfo = new VarInfo(scope, name, itype, node);
      symbolTable.define(name, varInfo);
    }
  }
  
  public Expression derefMemory(Expression memory, Expression lvalExpr) {
    /* lvalExpr's node with no type info, get it for BurstallMemoryModel analysis. */
    Expression resExpr = null;
    
    GNode srcNode = lvalExpr.getNode();
    Type t = unwrapped(lookupType(srcNode));
    if(t.isArray() || t.isStruct() || t.isUnion())
      resExpr = lvalExpr;
    else
      resExpr = getMemoryModel().deref(memory, lvalExpr);   
    return resExpr.setNode(srcNode);
  }
  
  private int sizeofType(Type t) {
    int res = 0;
    t = unwrapped(t);
    
    if (t.isInteger()) 
      res = 1;
    else if (t.isPointer())
      res = 1;
    else if (t.isStruct() || t.isUnion()) {
      StructOrUnionT struct = t.toStructOrUnion();
      if(t.isStruct()) {
        for(VariableT elem : struct.getMembers()) {
          res += sizeofType(elem.getType());
        }
      } else { // t.isUnion()
        for(VariableT elem : struct.getMembers()) {
          res = Math.max(res, sizeofType(elem.getType()));
        }
      }
    }
    else if(t.isArray()) {
      ArrayT array = t.toArray();
      res = (int) (array.getLength()) * sizeofType(array.getType());
    } 
    else {
      throw new IllegalArgumentException("Unknown type.");
    }
    return res;
  }
  
  private Type getTypeOfField(Node baseNode, String name) {
    Type baseType = unwrapped(lookupType(baseNode));
    Type structType = baseType;
    if(baseType.isPointer()) 
      structType = unwrapped(baseType.toPointer().getType());
    assert(structType.isStruct() || structType.isUnion());
    
    Type fieldType = null;
    for(VariableT elem : structType.toStructOrUnion().getMembers()) {
      if(name.equals(elem.getName())) {
        fieldType = elem;
        break;
      }
    }
    
    assert(fieldType != null);
    AnnotatedT resType = new AnnotatedT(fieldType);
    
    DynamicReference dynaRef = null;
    if("PrimaryIdentifier".equals(baseNode.getName())) {
      String baseName = baseNode.getString(0);
      dynaRef = new DynamicReference(baseName, baseType);
    } else {
      dynaRef = new DynamicReference(baseType);
    }
    
    FieldReference fldRef = null;
    if(baseType.isPointer()) {
      IndirectReference indRef = new IndirectReference(dynaRef);
      fldRef = new FieldReference(indRef, name);
    } else {
      fldRef = new FieldReference(dynaRef, name);
    }
    
    resType.shape(fldRef);
    return resType;
  }
  
  private Map<String, Integer> getFieldOffset(Type t) {
    Preconditions.checkArgument(t.isStruct());
    StructT struct = (StructT) t;
    Map<String, Integer> resMap = Maps.newHashMap();
    for(VariableT mem: struct.getMembers()) {
      if(!(mem.getType().isPointer() 
          && ((PointerT) mem.getType()).getType().equals(t))) continue;
      String name = mem.getName();
      int off = getOffsetOfField(t, name);
      resMap.put(name, off);
    }   
    return resMap;
  }
  
  private int getOffsetOfField(Type t, String name) {
    if(t.isPointer()) 
      t = (t.toPointer()).getType().resolve();
    if(!(t.isStruct() || t.isUnion()))
      throw new ExpressionFactoryException("Invalid type: " + t.toString());
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
      int elemTypeSize = sizeofType(elem.getType());
      offset += elemTypeSize;
    }
    return -1;
  }

  private Type unwrapped(Type type) {
    while(type.isAnnotated() || type.isAlias() || type.isVariable()) {
      type = type.resolve();
      type = type.deannotate();
    }
    return type;
  }
  
  private Type lookupType(Node node) throws ExpressionFactoryException {
    Type type = (Type) node.getProperty(xtc.Constants.TYPE);
    /* For the node in the control file that newly appeared in the 
     * quantified formula.
     */
    if(type == xtc.type.ErrorT.TYPE) {
      type = typeTable.get(node.toString());
    }
    /* For the node in the control file that cannot get type annotation,
     * which doesn't go to cfg builder to get type annotation
     */
    if(type == null) {
      File file = new File(node.getLocation().file);
      SymbolTable symbolTable = symbolTables.get(file);      
      if (symbolTable == null) 
        IOUtils.err().println("APPROX: Symbol table not found for file: " + file);
      else {
        symbolTable.setScope(scope);
        String name = node.getName();
        if("PrimaryIdentifier".equals(name) || "SimpleDeclarator".equals(name)) {
          type = symbolTable.lookupType(node.getString(0));
          if(type == null) { // newly defined variable, type info stored in IRVarInfo
             if(symbolTable.lookup(node.getString(0)).getType().equals(
                 edu.nyu.cascade.ir.type.IRIntegerType.getInstance())) {
               type = xtc.type.IntegerT.INT;
             } else {
               throw new ExpressionFactoryException("Type not found: " + node.toString());
             }
          }
        } else if("SubscriptExpression".equals(name)) {
          Type childType = unwrapped(lookupType(node.getNode(0)));
          if(childType.isPointer())  type = childType.toPointer().getType();
          if(childType.isArray())    type = childType.toArray().getType();     
        } else if("AddressExpression".equals(name)) {
          type = new PointerT(lookupType(node.getNode(0)));
        } else if("IndirectionExpression".equals(name)) {
          Type childType = unwrapped(lookupType(node.getNode(0)));
          if(childType.isPointer())  type = childType.toPointer().getType();
        } else if("AdditiveExpression".equals(name)) {
          Type childType_a = unwrapped(lookupType(node.getNode(0)));
          Type childType_b = unwrapped(lookupType(node.getNode(2)));
          if(childType_a.isPointer() || childType_b.isPointer())
            type = childType_a.isPointer() ? childType_a : childType_b;
          else if(childType_a.isFloat() || childType_b.isFloat())
            type = childType_a.isFloat() ? childType_a : childType_b;
          else
            type = NumberT.INT;
        } else if("BitwiseAndExpression".equals(name)) {
          type = new xtc.type.BooleanT();
        } else if("CastExpression".equals(name)) {
          type = lookupType(node.getNode(0));
        } else if("CharacterConstant".equals(name)) {
          type = NumberT.CHAR;
        } else if("DirectComponentSelection".equals(name) 
            || "IndirectComponentSelection".equals(name)) {
          type = getTypeOfField(node.getNode(0), node.getString(1));
        } else if("EqualityExpression".equals(name) 
            || "RelationalExpression".equals(name)
            || name.startsWith("Logical")) {
          type = new BooleanT();
        } else if("MultiplicativeExpression".equals(name)) {
          Type childType_a = unwrapped(lookupType(node.getNode(0)));
          Type childType_b = unwrapped(lookupType(node.getNode(2)));
          if(childType_a.isFloat() || childType_b.isFloat())
            type = childType_a.isFloat() ? childType_a : childType_b;
          else
            type = NumberT.INT;
        } else if("PostdecrementExpression".equals(name) 
            || "PostincrementExpression".equals(name)
            || "PredecrementExpression".equals(name)
            || "PreincrementExpression".equals(name)) {
          type = lookupType(node.getNode(0));
        } else if("SizeofExpression".equals(name)) {
          type = NumberT.INT;
        } else if("StringConstant".equals(name)) {
          type = new ArrayT(NumberT.CHAR);
        } else if("StructureTypeReference".equals(name)) {
          Scope currentScope = symbolTable.getCurrentScope();
          symbolTable.setScope(symbolTable.rootScope());
          String structName = node.getString(1);
          /* If name is not like "tag(...)", add tag(...) around it. 
           * In symbolTable, this kind variables are all in this form.
           */
          if(!structName.startsWith("tag(")) structName = "tag(" + structName +")";
            type = symbolTable.lookupType(structName);
          symbolTable.setScope(currentScope);
        } else if("TypedefName".equals(name)) {
          Scope currentScope = symbolTable.getCurrentScope();
          symbolTable.setScope(symbolTable.rootScope());
          String structName = node.getString(0);
          type = symbolTable.lookupType(structName);
          symbolTable.setScope(currentScope);
        } else if("UnaryMinusExpression".equals(name)) {
          type = NumberT.INT;
        } else if("IntegerConstant".equals(name)) {
          type = NumberT.INT;
        }
      }
    }
    
    if (type == null)
      throw new ExpressionFactoryException("Type not found: " + node.toString());
    
    node.setProperty(xtc.Constants.TYPE, type);
    return type;
  }
}
