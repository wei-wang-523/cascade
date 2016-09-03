/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
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
			ECR addrECR = createPointerECR(type);
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

			ECR varECR = createECR(info.getXtcType());
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

			Pair<String, String> key = Pair.of(id, scopeName);
			if (ecrMap.containsKey(key))
				return ecrMap.get(key);

			ECR addrECR = createPointerECR(varInfo.getXtcType());
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
			return getOpECR(node, srcECR);
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

			if (Preferences.isSet(Preferences.OPTION_CFS_POINTER_ARITH)) {
				Type type = CType.getType(node);
				// TODO: add pointer-arith pending
				if (type.resolve().isPointer()) {
					// TODO: swap lhs and rhs if lhs is constant and rhs is pointer
					if (lhsType.resolve().isPointer() && rhsType.hasConstant()) {
						ECR resECR = createPointerECR(type);
						opECRMap.put(Pair.of(node, node.getLocation()), resECR);

						long val = rhsType.getConstant().longValue();
						boolean positive = "+".equals(node.getString(1));
						long shift = positive ? val : -val;
						long size = cTypeAnalyzer
								.getSize(type.resolve().toPointer().getType());

						ECR lhsLocECR = uf.getLoc(lhsECR);
						ECR resLocECR = uf.getLoc(resECR);
						uf.ptrAri(resLocECR, size, lhsLocECR, shift);
						return resECR;
					}
				}
			}

			return getOpECR(node, srcECR);
		}

		public ECR visitShiftExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR);
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
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return getOpECR(node, lhsECR);
		}

		public ECR visitBitwiseAndExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR);
		}

		public ECR visitBitwiseOrExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR);
		}

		public ECR visitBitwiseXorExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(node, srcECR);
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
			return createECR(NumberT.INT);
		}

		public ECR visitLogicalNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitLogicalOrExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return createECR(NumberT.INT);
		}

		public ECR visitPreincrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base);
		}

		public ECR visitPredecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base);
		}

		public ECR visitPostincrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base);
		}

		public ECR visitPostdecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(node, base);
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
		Size locSize = uf.getType(locECR).getSize();
		if (locSize.isBottom())
			uf.expand(locECR, rangeSize);
		return locECR;
	}

	private ECR getComponent(ECR srcECR, long offset, Type fieldType) {
		ECR loc = uf.getLoc(srcECR);
		ValueType locType = uf.getType(loc);

		if (fieldType.resolve().isArray())
			fieldType = CType.getArrayCellType(fieldType);

		if (locType.getSize().isTop()) {
			uf.ensureSimple(loc);
			locType = uf.getType(loc);
		}

		if (locType.isSimple()) {
			uf.expand(loc, Size.createForType(fieldType));
			return srcECR;
		}

		ValueType structType = ValueType.struct(locType.getSize(),
				locType.getParent());

		locType = uf.unify(locType, structType); // Ensure locType is struct type
		// The type set to loc might not be locType. Since loc could be with bottom
		// type and associated with ccjoin or cjoin pending, the type change could
		// trigger the pending resolving process and would change the type set to
		// loc (could be ref)
		uf.setType(loc, locType);

		if (uf.getType(loc).isSimple()) {
			uf.expand(loc, Size.createForType(fieldType));
			return srcECR;
		}

		long size = CType.getInstance().getSize(fieldType);
		Range<Long> range = Range.closedOpen(offset, offset + size);
		ECR ecr = createFieldECR(range, fieldType, loc);
		return locType.asStruct().addFieldECR(range, ecr);
	}

	private ECR getConstant() {
		return ECR.createBottom();
	}

	ECR createECR(Type type) {
		type = type.resolve();
		Size size;
		if (type.isInternal()) {
			size = Size.getTop();
		} else if (CType.isScalar(type)) {
			size = Size.createForType(type);
		} else { // Composite type
			size = Size.getBot();
		}

		return uf.createECR(ValueType.blank(size, Parent.getBottom()));
	}

	private ECR createPointerECR(Type type) {
		ECR varECR = createECR(type);
		if (type.isInternal()) {
			return varECR;
		} else {
			SimpleType addrType = ValueType.simple(varECR,
					Size.createForType(PointerT.TO_VOID), Parent.getBottom());
			return uf.createECR(addrType);
		}
	}

	private ECR getOpECR(GNode node, ECR sourceECR) {
		Pair<GNode, Location> key = Pair.of(node, node.getLocation());
		if (opECRMap.containsKey(key))
			return opECRMap.get(key);

		ECR resECR = ECR.createBottom();
		opECRMap.put(key, resECR);

		uf.ccjoin(Size.getBot(), sourceECR, resECR);

		// Parent is stored at the points-to loc of
		uf.addCollapseECR(uf.getLoc(resECR));
		return resECR;
	}
	
	private ECR getOpECR(GNode node, ECR leftECR, ECR rightECR) {
		Pair<GNode, Location> key = Pair.of(node, node.getLocation());
		if (opECRMap.containsKey(key))
			return opECRMap.get(key);

		ECR resECR = ECR.createBottom();
		opECRMap.put(key, resECR);

		uf.ccjoin(Size.getBot(), leftECR, resECR);
		uf.ccjoin(Size.getBot(), rightECR, resECR);

		// Parent is stored at the points-to loc of
		uf.addCollapseECR(uf.getLoc(resECR));
		return resECR;
	}

	/**
	 * Create a field ECR with <code>xtcType</code>, <code>scopeName</code>, and
	 * <code>parent</code>. If <code>xtcType</code> is scalar, this method creates
	 * a single field ECR, otherwise, two ECRs will be created, one for the field
	 * and the other for the region it points to. For the field ECR, whose address
	 * ECR will be the same as the address attached with the ECR of
	 * <code>parent</code>.
	 * 
	 * @param range
	 * @param type
	 * @param srcECR
	 * @return
	 */
	private ECR createFieldECR(Range<Long> range, Type type, ECR srcECR) {
		type = type.resolve();
		Parent parent = Parent.create(uf.findRoot(srcECR));
		Size size = CType.isScalar(type) ? Size.createForType(type) : Size.getBot();
		ECR fieldECR = uf.createECR(ValueType.blank(size, parent));

		SimpleType addrType = ValueType.simple(fieldECR,
				Size.createForType(new PointerT(type)), Parent.getBottom());

		return uf.createECR(addrType);
	}

	private ECR pointerCast(ECR e, Type srcType, Type targetType) {
		if (!targetType.resolve().isPointer())
			return e;
		if (uf.getType(e).isBottom())
			return e;

		final ECR locECR = uf.getLoc(e);
		Type ptr2Type = targetType.resolve().toPointer().getType();
		long freshPtr2Size = cTypeAnalyzer.getSize(ptr2Type);

		if (Preferences.isSet(Preferences.OPTION_CFS_POINTER_ARITH)) {
			long srcPtr2Size = srcType.resolve().isPointer()
					? cTypeAnalyzer.getSize(srcType.resolve().toPointer().getType()) : 0;
			if (uf.containsPtrAritJoin(locECR, srcPtr2Size)) {
				// Create a fresh reference ECR to replace the one
				// created for pointer arithmetic operations.
				// Sample code: (typeof(*msg) *)((char *)__mptr -
				// (size_t)&((typeof(*msg) *)0)->list)
				ECR freshECR = createPointerECR(targetType);
				ECR freshLocECR = uf.getLoc(freshECR);
				uf.replacePtrAriJoin(freshLocECR, freshPtr2Size, locECR, srcPtr2Size);
				return freshECR;
			}
		}

		uf.expand(locECR, Size.createForType(ptr2Type));

		ValueType locType = uf.getType(locECR);
		for (ECR parent : locType.getParent().getECRs()) {
			ValueType parentType = uf.getType(parent);
			if (!parentType.isStruct())
				continue;

			Map<Range<Long>, ECR> fieldMap = parentType.asStruct().getFieldMap();
			Entry<Range<Long>, ECR> entry = Iterables.find(fieldMap.entrySet(),
					new Predicate<Entry<Range<Long>, ECR>>() {
						@Override
						public boolean apply(Entry<Range<Long>, ECR> entry) {
							return uf.getLoc(entry.getValue()).equals(locECR);
						}
					});

			Range<Long> range = entry.getKey();
			long offset = range.lowerEndpoint();
			Range<Long> newRange = Range.closedOpen(offset, offset + freshPtr2Size);
			if (!fieldMap.containsKey(newRange)) {
				ECR ecr = createFieldECR(range, ptr2Type, parent);
				fieldMap.put(newRange, ecr);
			}
		}
		return e;
	}
}