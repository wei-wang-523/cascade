package edu.nyu.cascade.c.pass.addrtaken;

import java.util.Collection;
import java.util.Set;

import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRVarInfo;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Visitor;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRPass;

/***
 * This pass helps find which functions are address taken in a module. Functions
 * are considered to be address taken if they are either stored, or passed as
 * arguments to functions.
 *
 */

public class AddressTakenAnalysis implements IRPass {
	private final Set<Function> addressTakenFunctions = Sets.newHashSet();
	private final SymbolTable SymbolTable;
	private final ValueManager ValueManager;
	private final ExprVisitor ExprVisitor;

	private AddressTakenAnalysis(SymbolTable symbolTable) {
		SymbolTable = symbolTable;
		ValueManager = new ValueManager(symbolTable);
		ExprVisitor = new ExprVisitor();
	}

	public static AddressTakenAnalysis create(SymbolTable symbolTable) {
		return new AddressTakenAnalysis(symbolTable);
	}

	private class ExprVisitor extends Visitor {
		void encode(Node node) {
			dispatch(node);
		}

		@SuppressWarnings("unused")
		public void visitSimpleDeclarator(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitLogicalNegationExpression(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitUnaryPlusExpression(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitIntegerConstant(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitFloatingConstant(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitStringConstant(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitCharacterConstant(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitAssignmentExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitConditionalExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitBitwiseAndExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitBitwiseOrExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitLogicAndExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitLogicOrExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitBitwiseXorExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitAddressExpression(GNode node) {
			Type type = CType.getType(node.getNode(0));
			if (!type.resolve().isFunction())
				return;

			Node idNode = CAnalyzer.getIdentifier(node.getGeneric(0));
			if (idNode == null)
				return;
			assert idNode.hasName("PrimaryIdentifier") : "Invalid identifier.";
			String idName = idNode.getString(0);
			IRVarInfo idInfo = SymbolTable.lookup(idName);
			Function func = (Function) ValueManager.getOrCreate(idInfo);
			addressTakenFunctions.add(func);
		}

		@SuppressWarnings("unused")
		public void visitPrimaryIdentifier(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitIndirectionComponentSelection(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitDirectComponentSelection(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitCastExpression(GNode node) {
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitIndirectionExpression(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitUnaryMinusExpression(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitIndirectComponentSelection(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitSubscriptExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(1));
		}

		@SuppressWarnings("unused")
		public void visitSizeofExpression(GNode node) {
			encode(node.getGeneric(0));
		}

		@SuppressWarnings("unused")
		public void visitTypeName(GNode node) {
		}

		@SuppressWarnings("unused")
		public void visitAdditiveExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitMultiplicativeExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitShiftExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitRelationalExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}

		@SuppressWarnings("unused")
		public void visitEqualityExpression(GNode node) {
			encode(node.getGeneric(0));
			encode(node.getGeneric(2));
		}
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {
		visit(globalCFG);
		for (IRControlFlowGraph CFG : CFGs)
			visit(CFG);
	}

	@Override
	public void reset() {
		addressTakenFunctions.clear();
	}

	public boolean hasAddressTaken(Function func) {
		return addressTakenFunctions.contains(func);
	}

	private void visit(IRControlFlowGraph CFG) {
		Scope oldScope = SymbolTable.getCurrentScope();

		SymbolTable.enterScope(CFG);

		for (IRBasicBlock BB : CFG.getBlocks()) {
			for (IRStatement Stmt : BB.getStatements()) {
				for (IRExpression Expr : Stmt.getOperands()) {
					ExprVisitor.encode(Expr.getSourceNode());
				}
			}
		}

		SymbolTable.setScope(oldScope);
	}

	public ValueManager getValueManager() {
		return ValueManager;
	}
}
