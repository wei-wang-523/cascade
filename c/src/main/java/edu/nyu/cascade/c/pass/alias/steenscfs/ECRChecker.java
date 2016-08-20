/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.List;
import java.util.Map;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.Type;
import xtc.type.VoidT;
import xtc.type.Type.Tag;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Range;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

class ECRChecker extends Visitor {

	private final UnionFindECR uf;
	private final SymbolTable symbolTable;
	private final CType cTypeAnalyzer = CType.getInstance();
	private final ECREncoder ecrEncoder;
	private final LvalVisitor lvalVisitor = new LvalVisitor();
	private final RvalVisitor rvalVisitor = new RvalVisitor();

	/**
	 * Store all the ECRs created for declared variables with their references
	 * names (variable names) and scope names
	 */
	private final Map<Pair<String, String>, ECR> ecrMap;

	/**
	 * Store all the ECRs for operation node
	 */
	private final Map<Pair<GNode, String>, ECR> opECRMap;

	@SuppressWarnings("unused")
	private class LvalVisitor extends Visitor {

		private ECR encodeECR(Node node) {
			return (ECR) dispatch(node);
		}

		@Override
		public ECR unableToVisit(Node node) throws VisitingException {
			IOUtils.err().println("APPROX: Treating unexpected node type as NULL: "
					+ node.getName());
			return ECR.createBottom();
		}

		public ECR visitAdditiveExpression(GNode node) {
			return rvalVisitor.encodeECR(node);
		}

		public ECR visitSimpleDeclarator(GNode node) {
			Preconditions.checkArgument(CType.hasScope(node));
			String id = node.getString(0);
			IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
			String scopeName = varInfo.getScopeName();
			return lookup(id, scopeName);
		}

		public ECR visitEnumerator(GNode node) {
			String id = node.getString(0);
			IRVarInfo info = symbolTable.lookup(id);
			String scopeName = info.getScopeName();
			return lookup(id, scopeName);
		}

		public ECR visitIndirectionExpression(GNode node) {
			return rvalVisitor.encodeECR(node.getNode(0));
		}

		public ECR visitIndirectComponentSelection(GNode node) {
			Node baseNode = node.getNode(0);
			ECR baseECR = rvalVisitor.encodeECR(baseNode);
			Type baseType = CType.getType(baseNode).resolve().toPointer().getType();
			Type fieldType = CType.getType(node);
			String fieldName = node.getString(1);
			long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
			return getComponent(baseECR, offset, fieldType);
		}

		public ECR visitDirectComponentSelection(GNode node) {
			Node baseNode = node.getNode(0);
			ECR baseECR = encodeECR(baseNode);
			Type baseType = CType.getType(baseNode);
			Type fieldType = CType.getType(node);
			String fieldName = node.getString(1);
			long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
			return getComponent(baseECR, offset, fieldType);
		}

		public ECR visitPrimaryIdentifier(GNode node) {
			Preconditions.checkArgument(CType.hasScope(node));
			String id = node.getString(0);
			IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
			String scopeName = varInfo.getScopeName();

			return lookup(id, scopeName);
		}

		public ECR visitSubscriptExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitIntegerConstant(GNode node) {
			return getConstant();
		}
	}

	@SuppressWarnings("unused")
	private class RvalVisitor extends Visitor {

		private ECR encodeECR(Node node) {
			return (ECR) dispatch(node);
		}

		@Override
		public ECR unableToVisit(Node node) throws VisitingException {
			IOUtils.err().println("APPROX: Treating unexpected node type as NULL: "
					+ node.getName());
			return ECR.createBottom();
		}

		public ECR visitSimpleDeclarator(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitAdditiveExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitShiftExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitSubscriptExpression(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitFunctionCall(GNode node) {
			Node funcNode = node.getNode(0);
			String funcName = funcNode.getString(0);

			Type returnType;
			if (ReservedFunction.isReserved(funcName)) {
				Sig signature = ReservedFunction.getSignature(funcName);
				returnType = signature.getReturnType();
			} else {
				returnType = CType.getType(node);
			}

			Size size = Size.createForType(returnType);
			BlankType type = ValueType.blank(size, Parent.getBottom());
			return uf.createECR(type);
		}

		public ECR visitAddressExpression(GNode node) {
			return lvalVisitor.encodeECR(node.getNode(0));
		}

		public ECR visitAssignmentExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitBitwiseAndExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitBitwiseOrExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitBitwiseXorExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitBitwiseNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitCastExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitCharacterConstant(GNode node) {
			return getConstant();
		}

		public ECR visitEqualityExpression(GNode node) {
			return getConstant();
		}

		public List<ECR> visitExpressionList(GNode node) {
			List<ECR> subECRList = Lists.newArrayListWithCapacity(node.size());
			for (Object elem : node) {
				ECR subECR = encodeECR(GNode.cast(elem));
				subECRList.add(subECR);
			}
			return subECRList;
		}

		public ECR visitIndirectionExpression(GNode node) {
			ECR addrECR = encodeECR(node.getNode(0));
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitIntegerConstant(GNode node) {
			return getConstant();
		}

		public ECR visitFloatingConstant(GNode node) {
			return getConstant();
		}

		public ECR visitEnumerator(GNode node) {
			return lvalVisitor.visitEnumerator(node);
		}

		public ECR visitLogicalAndExpression(GNode node) {
			return getConstant();
		}

		public ECR visitLogicalNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitLogicalOrExpression(GNode node) {
			return getConstant();
		}

		public ECR visitPreincrementExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitPredecrementExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitPostincrementExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitPostdecrementExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitPrimaryIdentifier(GNode node) {
			String id = node.getString(0);
			Scope scope = symbolTable.getScope(node);
			if (!scope.isDefined(id))
				return getConstant();

			IRVarInfo info = (IRVarInfo) scope.lookup(id);
			Type type = info.getXtcType();
			if (type.isEnumerator())
				return getConstant();

			ECR varECR = lvalVisitor.encodeECR(node);
			return deref(varECR, type);
		}

		public ECR visitRelationalExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return getConstant();
		}

		public ECR visitStringConstant(GNode node) {
			return getConstant();
		}

		public ECR visitSizeofExpression(GNode node) {
			return getConstant();
		}

		public ECR visitUnaryMinusExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitUnaryPlusExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitMultiplicativeExpression(GNode node) {
			return lookupOpECR(node);
		}

		public ECR visitDirectComponentSelection(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitIndirectComponentSelection(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}
	}

	private ECRChecker(UnionFindECR uf, SymbolTable symbolTable,
			ECREncoder ecrEncoder) {
		this.uf = uf;
		this.symbolTable = symbolTable;
		this.ecrMap = ecrEncoder.getECRMap();
		this.opECRMap = ecrEncoder.getOpECRMap();
		this.ecrEncoder = ecrEncoder;
	}

	static ECRChecker create(UnionFindECR uf, SymbolTable symbolTable,
			ECREncoder ecrEncoder) {
		return new ECRChecker(uf, symbolTable, ecrEncoder);
	}

	ECR toRval(Node node) {
		return rvalVisitor.encodeECR(node);
	}

	ECR toLval(Node node) {
		return lvalVisitor.encodeECR(node);
	}

	ECR getFunctionECR(String functionName) {
		return lookup(functionName, CScopeAnalyzer.getRootScopeName());
	}

	/**
	 * Create region ECR for the expression <code>region</code>
	 * 
	 * @param region
	 * @param ptrNode
	 * @return
	 */
	void createRegionVar(Expression region, Node ptrNode) {
		String name = region.asVariable().getName();
		String scopeName = CType.getScopeName(ptrNode);
		ECR ptrECR = rvalVisitor.encodeECR(ptrNode);
		ECR regionECR = uf.findRoot(uf.getLoc(ptrECR));

		VarImpl regionVar = new VarImpl(name, VoidT.TYPE, scopeName, regionECR);
		uf.add(regionVar);
	}

	void addStackVar(Expression lval, Node lvalNode) {
		createVar(lval, lvalNode);

		Type type = CType.getType(lvalNode).resolve();
		if (type.isArray() || type.isUnion() || type.isStruct())
			createRegionVar(lval, lvalNode);
	}

	private void createVar(Expression lval, Node lvalNode) {
		String name = lval.asVariable().getName();
		String scopeName = CType.getScopeName(lvalNode);
		Type type = CType.getType(lvalNode).resolve();
		if (type.isFunction())
			type = CType.getInstance().pointerize(type);

		ECR lvalECR = rvalVisitor.encodeECR(lvalNode);
		VarImpl var = new VarImpl(name, type, scopeName, lvalECR);
		uf.add(var);
	}

	private ECR getComponent(ECR srcECR, long offset, Type fieldType) {
		ValueType locType = uf.getType(uf.getLoc(srcECR));
		assert (locType.isSimple() || locType.isStruct());

		if (locType.isSimple()) {
			return srcECR;
		} else {
			long size = CType.getInstance().getSize(fieldType);
			Range<Long> range = Range.closedOpen(offset, offset + size);
			return locType.asStruct().getFieldMap().get(range);
		}
	}

	private ECR deref(ECR ecr, Type type) {
		Preconditions.checkArgument(!Tag.VOID.equals(type.tag()));
		if (!(CType.isScalar(type) || type.resolve().isFunction()))
			return ecr;

		return uf.getLoc(ecr);
	}

	private ECR getConstant() {
		return ECR.createBottom();
	}

	private ECR lookupOpECR(GNode opNode) {
		Pair<GNode, String> key = Pair.of(opNode, CType.getScopeName(opNode));
		if (opECRMap.containsKey(key)) {
			return opECRMap.get(key);
		} else {
			// Call ecrEncoder only for the nodes generated for function inline.
			// Only for var_arg initialization.
			return ecrEncoder.toRval(opNode);
		}
	}

	private ECR lookup(String id, String scopeName) {
		Preconditions.checkArgument(ecrMap.containsKey(Pair.of(id, scopeName)));
		return ecrMap.get(Pair.of(id, scopeName));
	}
}
