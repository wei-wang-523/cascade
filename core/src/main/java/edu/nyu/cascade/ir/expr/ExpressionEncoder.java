package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.ir.memory.model.MemoryModel;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
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
  MemoryModel<?> getMemoryModel();
	StateFactory<?> getStateFactory();
	SymbolTable.Scope getCurrentScope();
  
  StateExpressionClosure toBoolean(Node node);
  StateExpressionClosure toBoolean(Node node, Scope scope);
  StateExpressionClosure toBoolean(Node node, boolean negated);
  StateExpressionClosure toBoolean(Node node, boolean negated, Scope scope);
//  ExpressionClosure toInteger(Node node);
//  ExpressionClosure toInteger(Node node, Scope scope);
  StateExpressionClosure toExpression(Node node);
  StateExpressionClosure toExpression(Node node, Scope scope);
  StateExpressionClosure toLval(Node node);
  StateExpressionClosure toLval(Node node, Scope scope);
}
