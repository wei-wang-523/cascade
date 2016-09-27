/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.List;
import java.util.Map;
import xtc.tree.GNode;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.NumberT;
import xtc.type.Type;
import xtc.type.VoidT;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

public class ECREncoder extends Visitor {

	private final UnionFindECR uf;
	private final SymbolTable symbolTable;
	private final CType cTypeAnalyzer = CType.getInstance();
	private final LvalVisitor lvalVisitor = new LvalVisitor();
	private final RvalVisitor rvalVisitor = new RvalVisitor();

	/**
	 * Store all the ECRs created for declared variables with their references
	 * names (variable names) and scope names
	 */
	private final Map<Pair<String, String>, ECR> ecrMap = Maps.newHashMap();
	private final Map<Pair<GNode, Location>, ECR> opECRMap = Maps.newHashMap();

	@SuppressWarnings("unused")
	private class LvalVisitor extends Visitor {

		private ECR encodeECR(Node node) {
			return (ECR) dispatch(node);
		}

		@Override
		public ECR unableToVisit(Node node) throws VisitingException {
			IOUtils.err().println(
					"APPROX: Treating unexpected node type as NULL: " + node.getName());
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

			Pair<String, String> key = Pair.of(id, scopeName);
			if (ecrMap.containsKey(key))
				return ecrMap.get(key);

			Type type = varInfo.getXtcType();
			ECR addrECR = uf.createPointerECR(type);
			uf.getType(uf.getLoc(addrECR)).setSource();
			ecrMap.put(key, addrECR);

			if (type.resolve().isFunction()) {
				ECR varECR = deref(addrECR, type);
				ECR lamECR = uf.getLoc(varECR);
				VarImpl funcVar = new VarImpl(id, type, scopeName, lamECR);
				uf.add(funcVar);
			}

			return addrECR;
		}

		public ECR visitEnumerator(GNode node) {
			String id = node.getString(0);
			IRVarInfo info = symbolTable.lookup(id);
			String scopeName = info.getScopeName();

			Pair<String, String> key = Pair.of(id, scopeName);
			if (ecrMap.containsKey(key))
				return ecrMap.get(key);

			ECR varECR = uf.createECR(info.getXtcType());
			ecrMap.put(key, varECR);

			return varECR;
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
			ECR fieldECR = getComponent(baseECR, baseType, offset, fieldType);
			opECRMap.put(Pair.of(node, node.getLocation()), fieldECR);
			return fieldECR;
		}

		public ECR visitDirectComponentSelection(GNode node) {
			Node baseNode = node.getNode(0);
			ECR baseECR = encodeECR(baseNode);
			Type baseType = CType.getType(baseNode);
			Type fieldType = CType.getType(node);
			String fieldName = node.getString(1);
			long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
			ECR fieldECR = getComponent(baseECR, baseType, offset, fieldType);
			opECRMap.put(Pair.of(node, node.getLocation()), fieldECR);
			return fieldECR;
		}

		public ECR visitPrimaryIdentifier(GNode node) {
			Preconditions.checkArgument(CType.hasScope(node));
			String id = node.getString(0);
			IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
			String scopeName = varInfo.getScopeName();

			Pair<String, String> key = Pair.of(id, scopeName);
			if (ecrMap.containsKey(key))
				return ecrMap.get(key);

			ECR addrECR = uf.createPointerECR(varInfo.getXtcType());
			ecrMap.put(key, addrECR);
			return addrECR;
		}

		public ECR visitSubscriptExpression(GNode node) {
			Node baseNode = node.getNode(0);
			Node idxNode = node.getNode(1);
			ECR baseECR = rvalVisitor.encodeECR(baseNode);
			ECR idxECR = rvalVisitor.encodeECR(idxNode);
			Type baseType = CType.getInstance().pointerize(CType.getType(baseNode));
			Type idxType = CType.getInstance().pointerize(CType.getType(idxNode));
			ECR srcECR = baseType.isPointer() ? baseECR : idxECR;
			return getOpECR(node, srcECR, baseType);
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
			IOUtils.err().println(
					"APPROX: Treating unexpected node type as NULL: " + node.getName());
			return ECR.createBottom();
		}

		public ECR visitSimpleDeclarator(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitConditionalExpression(GNode node) {
			Node lhsNode = node.getNode(1);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			uf.ccjoin(Size.getBot(), rhsECR, lhsECR);
			return lhsECR;
		}

		public ECR visitAdditiveExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);

			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR, CType.getType(node));
		}

		public ECR visitShiftExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR, VoidT.TYPE);
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
			return uf.createECR(returnType);
		}

		public ECR visitAddressExpression(GNode node) {
			return lvalVisitor.encodeECR(node.getNode(0));
		}

		public ECR visitAssignmentExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			uf.ccjoin(Size.getBot(), rhsECR, lhsECR);
			return lhsECR;
		}

		public ECR visitBitwiseAndExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR, VoidT.TYPE);
		}

		public ECR visitBitwiseOrExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR, VoidT.TYPE);
		}

		public ECR visitBitwiseXorExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR, VoidT.TYPE);
		}

		public ECR visitBitwiseNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitCastExpression(GNode node) {
			Pair<GNode, Location> key = Pair.of(node, node.getLocation());
			if (opECRMap.containsKey(key))
				return opECRMap.get(key);

			ECR srcECR = encodeECR(node.getNode(1));
			Type srcType = CType.getType(node.getNode(1));
			Type targetType = CType.getType(node);
			ECR castECR = pointerCast(srcECR, srcType, targetType);
			opECRMap.put(key, castECR);
			return castECR;
		}

		public ECR visitCharacterConstant(GNode node) {
			return getConstant();
		}

		public ECR visitEqualityExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			uf.ccjoin(Size.getBot(), rhsECR, lhsECR);
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
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return uf.createECR(NumberT.INT);
		}

		public ECR visitLogicalNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitLogicalOrExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return uf.createECR(NumberT.INT);
		}

		public ECR visitPreincrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base, CType.getType(node));
		}

		public ECR visitPredecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base, CType.getType(node));
		}

		public ECR visitPostincrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base, CType.getType(node));
		}

		public ECR visitPostdecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base, CType.getType(node));
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
			encodeECR(node.getNode(0));
			return getConstant();
		}

		public ECR visitUnaryMinusExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitUnaryPlusExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitMultiplicativeExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return getOpECR(node, lhsECR, rhsECR);
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

	private ECREncoder(UnionFindECR uf, SymbolTable symbolTable) {
		this.uf = uf;
		this.symbolTable = symbolTable;
	}

	static ECREncoder create(UnionFindECR uf, SymbolTable symbolTable) {
		return new ECREncoder(uf, symbolTable);
	}

	ECR toRval(Node node) {
		return rvalVisitor.encodeECR(node);
	}

	ECR toLval(Node node) {
		return lvalVisitor.encodeECR(node);
	}

	Map<Pair<String, String>, ECR> getECRMap() {
		return ecrMap;
	}

	Map<Pair<GNode, Location>, ECR> getOpECRMap() {
		return opECRMap;
	}

	/**
	 * Get the lambda ECR created for <code>functionName</code>
	 * 
	 * @param functionName
	 * @return
	 */
	ECR getFunctionECR(String functionName) {
		return ecrMap.get(Pair.of(functionName, CScopeAnalyzer.getRootScopeName()));
	}

	private ECR deref(ECR ecr, Type type) {
		if (!(CType.isScalar(type) || type.resolve().isFunction()))
			return ecr;

		ECR locECR = uf.getLoc(ecr);
		if (type.resolve().isFunction())
			return locECR;

		Size rangeSize = Size.createForType(type);
		uf.expand(locECR, rangeSize);
		return locECR;
	}

	private ECR getComponent(ECR srcECR, Type baseType, long offset,
			Type field_type) {
		Type field_cell_type = CType.getCellType(field_type);

		ECR loc = uf.getLoc(srcECR);
		ValueType locType = uf.getType(loc);

		assert !locType.isSimple();
		
		long size = CType.getInstance().getSize(field_type);
		Range<Long> range = Range.closedOpen(offset, offset + size);

		ECR structECR;
		if (locType.isStruct() && locType.getSize().getValue() == CType
				.getInstance().getSize(baseType)) {
			structECR = loc;
		} else {
			structECR = uf.createECR(baseType);
			uf.join(loc, structECR);
		}

		ValueType structType = uf.getType(structECR);
		ECR fieldECR;
		if (structType.asStruct().getFieldMap().containsKey(range)) {
			fieldECR = structType.asStruct().getFieldMap().get(range);
		} else {
			fieldECR = uf.createPointerECR(field_cell_type);
			ECR field_loc_ecr = uf.getLoc(fieldECR);
			ValueType field_loc_type = uf.getType(field_loc_ecr);
			field_loc_type.setParent(Parent.create(structECR));
			uf.setType(field_loc_ecr, field_loc_type);
			structType.asStruct().getFieldMap().put(range, fieldECR);
			uf.setType(structECR, structType);
		}
		return fieldECR;
	}

	private ECR getConstant() {
		return ECR.createBottom();
	}

	private ECR getOpECR(GNode node, ECR sourceECR, Type type) {
		Pair<GNode, Location> key = Pair.of(node, node.getLocation());
		if (opECRMap.containsKey(key))
			return opECRMap.get(key);

		type = CType.getInstance().pointerize(type);
		ECR resECR = type.isPointer()
				? uf.createPointerECR(type.toPointer().getType()) : ECR.createBottom();
		opECRMap.put(key, resECR);
		uf.ccjoin(Size.getBot(), sourceECR, resECR);
		uf.addCollapseECR(resECR);
		return resECR;
	}

	private ECR getOpECR(GNode node, ECR leftECR, ECR rightECR) {
		Pair<GNode, Location> key = Pair.of(node, node.getLocation());
		if (opECRMap.containsKey(key))
			return opECRMap.get(key);

		Type type = CType.getInstance().pointerize(CType.getType(node));
		ECR resECR = type.isPointer() ? uf.createPointerECR(type)
				: ECR.createBottom();
		opECRMap.put(key, resECR);
		uf.ccjoin(Size.getBot(), leftECR, resECR);
		uf.ccjoin(Size.getBot(), rightECR, resECR);
		uf.addCollapseECR(resECR);
		return resECR;
	}

	private ECR pointerCast(ECR srcECR, Type srcType, Type targetType) {
		if (uf.getType(srcECR).isBottom())
			return srcECR;
		targetType = CType.getInstance().pointerize(targetType);
		if (!targetType.isPointer())
			return srcECR;
		ECR resECR = uf.createPointerECR(targetType.toPointer().getType());
		uf.pointerCast(srcECR, resECR);
		return resECR;
	}
}