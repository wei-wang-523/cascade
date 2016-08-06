package edu.nyu.cascade.c.pass.alias;

import java.util.Collection;
import java.util.Iterator;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.pass.IRPass;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Visitor;
import xtc.type.Type;

/**
 * This pass is to collect left values from the given program (represented as a
 * global CFG and multiple function CFGs).
 * 
 * @author weiwang
 *
 */

public final class LeftValueCollectingPassImpl implements IRPass {
	private Collection<Pair<Node, String>> leftValues = Sets.newHashSet();

	@Override
	public void analysis(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {
		runOnModule(globalCFG, CFGs);
	}

	@Override
	public void reset() {
		leftValues.clear();
	}

	public Collection<Pair<Node, String>> getLeftValues() {
		return leftValues;
	}

	private boolean runOnModule(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {

		PointerVisitor pointerBuilder = new PointerVisitor();

		// First step, build the globals graph
		pointerBuilder.visit(globalCFG);

		// build the graph for each function CFG
		for (IRControlFlowGraph CFG : CFGs) {
			pointerBuilder.visit(CFG);
		}

		return false;
	}

	class PointerVisitor {
		private LvalVisitor lvalVisitor = new LvalVisitor();
		private RvalVisitor rvalVisitor = new RvalVisitor();

		private void init(Node N) {
			String NScope = CType.getScopeName(N);
			leftValues.add(Pair.of(N, NScope));
		}

		private class LvalVisitor extends Visitor {
			void encode(Node node) {
				dispatch(node);
				if (node.hasName("PrimaryIdentifier")) {
					return;
				}
				if (CType.isScalar(CType.getType(node))) {
					init(node);
				}
			}

			@Override
			public Object unableToVisit(Node node) {
				IOUtils.err().println("APPROX: Treating unexpected node type as NULL: "
						+ node.getName());
				return null;
			}

			@SuppressWarnings("unused")
			public void visitSimpleDeclarator(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitPrimaryIdentifier(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitIndirectionExpression(GNode node) {
				rvalVisitor.encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitIndirectComponentSelection(GNode node) {
				rvalVisitor.encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitDirectComponentSelection(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitSubscriptExpression(GNode node) {
				encode(node.getNode(0));
				rvalVisitor.encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitAddressExpression(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitCastExpression(GNode node) {
				encode(node.getNode(1));
			}
		}

		private class RvalVisitor extends Visitor {
			void encode(Node node) {
				dispatch(node);
			}

			@Override
			public Object unableToVisit(Node node) {
				IOUtils.err().println("APPROX: Treating unexpected node type as NULL: "
						+ node.getName());
				return null;
			}

			@SuppressWarnings("unused")
			public void visitPrimaryIdentifier(GNode node) {
				Type Ty = CType.getType(node);
				if (Ty.isEnumerator())
					return;
				if (Ty.isError())
					return;
				lvalVisitor.encode(node);
			}

			@SuppressWarnings("unused")
			public void visitIntegerConstant(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitFloatingConstant(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitCharacterConstant(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitEqualityExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitShiftExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitTypeName(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitSizeofExpression(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitUnaryMinusExpression(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitUnaryPlusExpression(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitIndirectComponentSelection(GNode node) {
				lvalVisitor.encode(node);
			}

			@SuppressWarnings("unused")
			public void visitDirectComponentSelection(GNode node) {
				lvalVisitor.encode(node);
			}

			@SuppressWarnings("unused")
			public void visitSubscriptExpression(GNode node) {
				lvalVisitor.encode(node);
			}

			@SuppressWarnings("unused")
			public void visitConditionalExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitRelationalExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitMultiplicativeExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitCastExpression(GNode node) {
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitIndirectionExpression(GNode node) {
				lvalVisitor.encode(node);
			}

			@SuppressWarnings("unused")
			public void visitAddressExpression(GNode node) {
				lvalVisitor.encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitAdditiveExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}

			@SuppressWarnings("unused")
			public void visitBitwiseAndExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitBitwiseOrExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitBitwiseXorExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitLogicalNegationExpression(GNode node) {
				encode(node.getNode(0));
			}

			@SuppressWarnings("unused")
			public void visitStringConstant(GNode node) {
			}

			@SuppressWarnings("unused")
			public void visitLogicAndExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitLogicalOrExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
			}

			@SuppressWarnings("unused")
			public void visitAssignmentExpression(GNode node) {
				lvalVisitor.encode(node.getNode(0));
				encode(node.getNode(2));
			}
		}

		private void visit(IRStatement stmt) {
			switch (stmt.getType()) {
			case DECLARE:
			case DECLARE_ARRAY: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				lvalVisitor.encode(lhs);
				break;
			}
			case INIT:
			case ASSIGN: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				Node rhs = stmt.getOperand(1).getSourceNode();
				lvalVisitor.encode(lhs);
				rvalVisitor.encode(rhs);
				break;
			}
			case FREE: {
				Node opNode = stmt.getOperand(0).getSourceNode();
				lvalVisitor.encode(opNode);
				break;
			}
			case ASSUME:
			case ASSERT: {
				Node opNode = stmt.getOperand(0).getSourceNode();
				rvalVisitor.encode(opNode);
				break;
			}
			case RETURN: {
				if (stmt.getOperands() != null && !stmt.getOperands().isEmpty()) {
					Node ret = stmt.getOperand(0).getSourceNode();
					lvalVisitor.encode(ret);
				}
				break;
			}
			case ALLOCA:
			case CALLOC:
			case MALLOC: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				Node size = stmt.getOperand(1).getSourceNode();
				lvalVisitor.encode(lhs);
				rvalVisitor.encode(size);
				break;
			}
			case CALL: {
				// Set up the return value...
				Type retTy = CType.getType(stmt.getSourceNode());

				if (!retTy.resolve().isVoid()) {
					Node retNode = stmt.getOperand(1).getSourceNode();
					lvalVisitor.encode(retNode);
				}

				Node funcNode = stmt.getOperand(0).getSourceNode();
				String funcName = CAnalyzer.toFunctionName(funcNode);
				if (ReservedFunction.MEMCOPY.equals(funcName)) {
					Node lhs = stmt.getOperand(2).getSourceNode();
					Node rhs = stmt.getOperand(3).getSourceNode();
					lvalVisitor.encode(lhs);
					lvalVisitor.encode(rhs);
					return;
				}

				Type funcTy = CType.getType(funcNode);
				Node funcId = CAnalyzer.getIdentifier((GNode) funcNode);
				if (funcId == null || !CType.getType(funcId).resolve().isFunction()) {
					lvalVisitor.encode(funcNode);
				}

				// Get the type of function. Normalize the function to call
				// as a function pointer via pointerizing the function type
				funcTy = CType.getInstance().pointerize(funcTy);
				funcTy = funcTy.toPointer().getType();

				// Calculate the arguments vector...
				// Add all fixed pointer arguments, then merge the rest together
				Iterator<IRExpression> ArgItr = stmt.getOperands().iterator();
				ArgItr.next();
				if (!funcTy.resolve().toFunction().getResult().isVoid())
					ArgItr.next();

				while (ArgItr.hasNext()) {
					Node ArgNode = ArgItr.next().getSourceNode();
					rvalVisitor.encode(ArgNode);
				}

				break;
			}
			default:
				break;
			}
		}

		private void visit(IRControlFlowGraph CFG) {
			Collection<IRBasicBlock> BBs = Lists.reverse(CFG.topologicalSeq(CFG
					.getEntry()));
			for (IRBasicBlock BB : BBs) {
				for (IRStatement stmt : BB.getStatements())
					visit(stmt);

				for (IREdge<?> outgoing : CFG.getOutgoingEdges(BB)) {
					if (null != outgoing.getGuard()) {
						Node opNode = outgoing.getGuard().getSourceNode();
						rvalVisitor.encode(opNode);
					}
				}
			}
		}
	}

}
