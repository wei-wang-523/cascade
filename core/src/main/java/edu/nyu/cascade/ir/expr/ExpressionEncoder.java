package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

/**
 * A semantic encoder for expressions, using underlying representation Expr and
 * state Mem. Applying the encoder yields an ExpressionClosure object, which can
 * be evaluated to an Expression given a Mem state input.
 * 
 * @param <Expr>
 *          the underlying representation of the expression
 * @param 
 *          the representation of program state in the expression
 */

public interface ExpressionEncoder {
  ExpressionEncoding getEncoding();
  MemoryModel getMemoryModel();
  SymbolTable.Scope getCurrentScope();
  
  ExpressionClosure toBoolean(Node node);
  ExpressionClosure toBoolean(Node node, Scope scope);
  ExpressionClosure toBoolean(Node node, boolean negated);
  ExpressionClosure toBoolean(Node node, boolean negated, Scope scope);
//  ExpressionClosure toInteger(Node node);
//  ExpressionClosure toInteger(Node node, Scope scope);
  ExpressionClosure toExpression(Node node);
  ExpressionClosure toExpression(Node node, Scope scope);
  ExpressionClosure toLval(Node node);
  ExpressionClosure toLval(Node node, Scope scope);
  
  void setScope(Scope scope);
}
