/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steensfs;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.FunctionT;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.type.VoidT;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

class ECREncoder extends Visitor {

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
			ECR addrECR = createECR(type);
			ecrMap.put(key, addrECR);

			if (type.resolve().isFunction()) { // For function pointer analysis
				ECR varECR = deref(addrECR, type);
				ECR lamECR = uf.getFunc(varECR);
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

			Type type = varInfo.getXtcType();
			ECR addrECR = createECR(type);
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
			return getOpECR(Size.createForType(baseType), srcECR);
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
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
		}

		public ECR visitShiftExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
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
			return ECR.create(type);
		}

		public ECR visitAddressExpression(GNode node) {
			return lvalVisitor.encodeECR(node.getNode(0));
		}

		public ECR visitAssignmentExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
		}

		public ECR visitBitwiseAndExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
		}

		public ECR visitBitwiseOrExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
		}

		public ECR visitBitwiseXorExpression(GNode node) {
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(1);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			Type lhsType = CType.getInstance().pointerize(CType.getType(lhsNode));
			Type rhsType = CType.getInstance().pointerize(CType.getType(rhsNode));
			ECR srcECR = rhsType.isPointer() ? rhsECR : lhsECR;
			return getOpECR(Size.createForType(PointerT.TO_VOID), srcECR);
		}

		public ECR visitBitwiseNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitCastExpression(GNode node) {
			ECR srcECR = encodeECR(node.getNode(1));
			Type targetType = CType.getType(node);
			pointerCast(srcECR, targetType);
			return srcECR;
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
			return getOpECR(Size.createForType(CType.getType(node.getNode(0))), base);
		}

		public ECR visitPredecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(Size.createForType(CType.getType(node.getNode(0))), base);
		}

		public ECR visitPostincrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(Size.createForType(CType.getType(node.getNode(0))), base);
		}

		public ECR visitPostdecrementExpression(GNode node) {
			ECR base = encodeECR(node.getNode(0));
			return getOpECR(Size.createForType(CType.getType(node.getNode(0))), base);
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
			Node lhsNode = node.getNode(0);
			Node rhsNode = node.getNode(2);
			ECR lhsECR = encodeECR(lhsNode);
			ECR rhsECR = encodeECR(rhsNode);
			return getOpECR(Size.createForType(CType.getType(node)), lhsECR, rhsECR);
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

	/**
	 * Get the lambda ECR created for <code>functionName</code>
	 */
	ECR getFunctionECR(String functionName) {
		return ecrMap.get(Pair.of(functionName, CScopeAnalyzer.getRootScopeName()));
	}

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

	ECR getComponent(ECR srcECR, long offset, Type fieldType) {
		ECR loc = uf.getLoc(srcECR);
		Offset off = loc.getOffset();

		if (off != null) {
			if (off.isUnknown()) {
				uf.collapse(loc);
				return srcECR;
			} else {
				uf.unlessZero(off, loc);
			}
		}

		ValueType locType = uf.getType(loc);
		long size = CType.getInstance().getSize(fieldType);

		if (locType.isSimple() || locType.isObject()) {
			uf.promote(loc, Size.create(size));
			return srcECR;
		}

		Size sizePrime = locType.isBottom() ? Size.getTop() : locType.getSize();
		ValueType structType = ValueType.struct(sizePrime, Parent.getBottom());

		locType = uf.unify(structType, locType); // Ensure locType is struct type
		// The type set to loc might not be locType. Since loc could be with bottom
		// type and associated with ccjoin or cjoin pending, the type change could
		// trigger the pending resolving process and would change the type set to
		// loc (could be ref)
		uf.setType(loc, locType);

		if (uf.getType(loc).isObject()) {
			uf.expand(loc);
			return loc;
		}

		RangeMap<Long, ECR> fieldMap = locType.asStruct().getFieldMap();
		Range<Long> range = Range.closedOpen(offset, offset + size);
		normalize(loc, fieldType, range, fieldMap);
		return fieldMap.get(offset);
	}

	ValueType getLamdaType(Type type) {
		Preconditions.checkArgument(type.resolve().isFunction());
		FunctionT funcType = type.resolve().toFunction();
		List<ECR> paramECRs;
		if (!funcType.getParameters().isEmpty()) {
			int paramSize = funcType.getParameters().size();
			paramECRs = Lists.newArrayListWithCapacity(paramSize);
			for (int i = 0; i < paramSize; i++) {
				Type paramType = funcType.getParameters().get(i);
				ECR paramECR = deref(createECR(paramType), paramType);
				paramECRs.add(paramECR);
			}
		} else {
			paramECRs = Collections.<ECR> emptyList();
		}

		ECR retECR = ECR.createBottom();
		ValueType lambdaType = ValueType.lam(retECR, paramECRs,
				Size.createForType(funcType), Parent.getBottom());
		return lambdaType;
	}

	ECR deref(ECR ecr, Type type) {
		if (CType.isScalar(type) || type.resolve().isFunction()) {
			return uf.getLoc(ecr);
		} else {
			return ecr;
		}
	}

	private void createVar(Expression lval, Node lvalNode) {
		String name = lval.asVariable().getName();
		String scopeName = CType.getScopeName(lvalNode);
		Type type = CType.getType(lvalNode);
		if (type.isFunction()) {
			type = CType.getInstance().pointerize(type);
		}

		ECR lvalECR = rvalVisitor.encodeECR(lvalNode);
		VarImpl var = new VarImpl(name, type, scopeName, lvalECR);
		uf.add(var);
	}

	private ECR getConstant() {
		return ECR.createBottom();
	}

	private ECR createECR(Type type) {
		type = type.resolve();

		if (type.isFunction())
			return createForFunction(type);

		Size size = null;
		if (type.isInternal() || type.isArray()) {
			size = Size.getTop();
		} else { // scalar type, structure or union type
			size = Size.createForType(type);
		}

		BlankType varType = ValueType.blank(size, Parent.getBottom());

		ECR varECR = ECR.create(varType);
		varECR.setOffset(Offset.createZero());

		if (type.isInternal())
			return varECR;

		ValueType addrType = ValueType.simple(varECR, ECR.createBottom(),
				Size.createForType(new PointerT(type)), Parent.getBottom());

		return ECR.create(addrType);
	}

	private ECR createForFunction(Type type) {
		ValueType lambdaType = getLamdaType(type);
		ECR func = ECR.create(lambdaType);

		ECR loc = ECR.createBottom();
		loc.setOffset(Offset.createZero());

		Type addrXtcType = CType.getInstance().pointerize(type);
		Size size = Size.createForType(addrXtcType);

		ValueType varType = ValueType.simple(loc, func, size, Parent.getBottom());
		ECR varECR = ECR.create(varType);
		varECR.setOffset(Offset.createZero());

		SimpleType addrType = ValueType.simple(varECR, ECR.createBottom(), size,
				Parent.getBottom());

		return ECR.create(addrType);
	}

	private ECR getOpECR(Size size, ECR leftECR, ECR rightECR) {
		uf.ensureSimObj(leftECR, size);
		uf.ensureSimObj(rightECR, size);
		uf.ccjoin(size, leftECR, rightECR);
		ValueType type = uf.getType(leftECR);
		ECR loc = type.isSimple() ? type.asSimple().getLoc()
				: type.asObject().getLoc();

		Offset offset = loc.getOffset();
		if (offset != null && offset.isZero()) {
			uf.makeUnknown(offset);
		}
		return leftECR;
	}

	private ECR getOpECR(Size size, ECR sourceECR) {
		uf.ensureSimObj(sourceECR, size);
		ValueType type = uf.getType(sourceECR);
		ECR loc = type.isSimple() ? type.asSimple().getLoc()
				: type.asObject().getLoc();

		Offset offset = loc.getOffset();
		if (offset != null && offset.isZero()) {
			uf.makeUnknown(offset);
		}
		return sourceECR;
	}

	/**
	 * Side-effecting predicate that modifies mapping fieldMap to be compatible
	 * with access of structure element with fieldType and range, where parent is
	 * the parent for the newly created ECR.
	 */
	private void normalize(ECR srcECR, Type fieldType, Range<Long> range,
			RangeMap<Long, ECR> fieldMap) {

		if (fieldMap.asMapOfRanges().containsKey(range))
			return;

		RangeMap<Long, ECR> subMap = fieldMap.subRangeMap(range);
		Map<Range<Long>, ECR> subMapRanges = subMap.asMapOfRanges();

		if (subMapRanges.isEmpty()) {
			ECR ecr = createFieldECR(range, fieldType, srcECR);
			fieldMap.put(range, ecr);
			return;
		}

		Range<Long> span = subMap.span();
		fieldMap.remove(span);

		Range<Long> newRange = subMap.span().span(range);

		Iterator<ECR> elemECRItr = subMapRanges.values().iterator();
		ECR joinECR = elemECRItr.next();
		while (elemECRItr.hasNext())
			joinECR = uf.cjoin(elemECRItr.next(), joinECR);
		uf.collapse(joinECR);

		fieldMap.put(newRange, joinECR);
		return;
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

		Size size = type.isArray() ? Size.getTop() : Size.createForType(type);
		BlankType fieldType = ValueType.blank(size,
				Parent.create(uf.findRoot(srcECR)));

		ECR fieldECR = ECR.create(fieldType);
		fieldECR.setOffset(Offset.createZero());

		SimpleType addrType = ValueType.simple(fieldECR, ECR.createBottom(),
				Size.createForType(new PointerT(type)), Parent.getBottom());

		ECR addrECR = ECR.create(addrType);

		StructType srcType = uf.getType(srcECR).asStruct();
		srcType.getFieldMap().put(range, addrECR);
		return addrECR;
	}

	private void pointerCast(ECR e, Type type) {
		if (!type.resolve().isPointer())
			return;
		if (uf.getType(e).isBottom())
			return;

		final ECR locECR = uf.getLoc(e);

		Type ptr2Type = type.resolve().toPointer().getType();
		long ptr2Size = CType.getInstance().getSize(ptr2Type);
		uf.promote(locECR, Size.create(ptr2Size));

		ValueType locType = uf.getType(locECR);
		for (ECR parent : locType.getParent().getECRs()) {
			ValueType parentType = uf.getType(parent);
			if (!parentType.isStruct())
				continue;

			RangeMap<Long, ECR> fieldRangeMap = parentType.asStruct().getFieldMap();
			Entry<Range<Long>, ECR> entry = Iterables.find(
					fieldRangeMap.asMapOfRanges().entrySet(),
					new Predicate<Entry<Range<Long>, ECR>>() {
						@Override
						public boolean apply(Entry<Range<Long>, ECR> entry) {
							return uf.getLoc(entry.getValue()).equals(locECR);
						}
					});

			Range<Long> range = entry.getKey();
			long offset = range.lowerEndpoint();
			Range<Long> newRange = Range.closedOpen(offset, offset + ptr2Size);
			normalize(parent, ptr2Type, newRange, fieldRangeMap);
		}
	}
}
