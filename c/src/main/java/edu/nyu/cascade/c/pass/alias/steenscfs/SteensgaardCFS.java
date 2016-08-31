package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Range;
import com.google.common.collect.Sets;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.FunctionT;
import xtc.type.PointerT;
import xtc.type.Type;
import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.LeftValueCollectingPassImpl;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class SteensgaardCFS implements IRAliasAnalyzer<ECR> {
	private final UnionFindECR uf;
	private final SymbolTable symbolTable;
	private final ECREncoder ecrEncoder;
	private ECRChecker ecrChecker;
	private ImmutableMap<ECR, Collection<IRVar>> snapShot;
	private IRControlFlowGraph currentCFG;

	private SteensgaardCFS(SymbolTable symbolTable) {
		uf = UnionFindECR.create();
		ecrEncoder = ECREncoder.create(uf, symbolTable);
		this.symbolTable = symbolTable;
	}

	public static SteensgaardCFS create(SymbolTable symbolTable) {
		return new SteensgaardCFS(symbolTable);
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {
		// Analyze non-global CFGs
		{
			symbolTable.enterScope(globalCFG);
			currentCFG = globalCFG;

			final Collection<IRBasicBlock> topologicSeq = Lists
					.reverse(globalCFG.topologicalSeq(globalCFG.getEntry()));

			for (IRBasicBlock block : topologicSeq) {
				for (IRStatement stmt : block.getStatements())
					analysis(stmt);

				for (IREdge<?> outgoing : globalCFG.getOutgoingEdges(block)) {
					if (null != outgoing.getGuard())
						ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
				}
			}
		}

		// Analyze non-global CFGs

		for (IRControlFlowGraph CFG : CFGs) {
			symbolTable.enterScope(CFG);
			currentCFG = CFG;
			GNode declarator = CFG.getSourceNode().getGeneric(2);
			GNode identifier = CAnalyzer.getDeclaredId(declarator);
			FunctionT funcXtcType = symbolTable.lookupType(identifier.getString(0))
					.resolve().toFunction();

			if (!funcXtcType.getParameters().isEmpty()) {
				GNode parameters = CAnalyzer.getFunctionDeclarator(declarator)
						.getGeneric(1);
				parameters = parameters.getGeneric(0);

				List<ECR> paramECRs = Lists.newArrayList();
				for (Object o : parameters) {
					GNode paramNode = ((Node) o).getGeneric(1);
					assert (null != paramNode);
					Node paramIdNode = CAnalyzer.getDeclaredId(paramNode);
					ECR paramECR = ecrEncoder.toRval(paramIdNode);
					paramECRs.add(paramECR);
				}

				ECR funcECR = ecrEncoder.toRval(identifier);
				LambdaType lamType = uf.getType(uf.getFunc(funcECR)).asLambda();
				List<ECR> lamECRs = lamType.getParams();
				assert lamECRs.size() >= paramECRs.size();

				for (int i = 0; i < paramECRs.size(); i++) {
					ECR lamECR = lamECRs.get(i);
					ECR paramECR = paramECRs.get(i);
					uf.cjoin(lamECR, paramECR);
				}
			}

			final Collection<IRBasicBlock> topologicSeq = Lists
					.reverse(CFG.topologicalSeq(CFG.getEntry()));

			for (IRBasicBlock block : topologicSeq) {
				for (IRStatement stmt : block.getStatements())
					analysis(stmt);

				for (IREdge<?> outgoing : CFG.getOutgoingEdges(block)) {
					if (null != outgoing.getGuard()) {
						ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
					}
				}
			}
		}

		initChecker();
	}

	private void processReservedFunctionCall(String funcName, IRStatement stmt) {
		if (ReservedFunction.MEMCOPY.equals(funcName)
				|| ReservedFunction.MEMMOVE.equals(funcName)) {
			Node lhs = stmt.getOperand(2).getSourceNode();
			Node rhs = stmt.getOperand(3).getSourceNode();
			ECR lhsECR = ecrEncoder.toRval(lhs);
			ECR rhsECR = ecrEncoder.toRval(rhs);
			uf.ensureSimple(lhsECR);
			uf.ensureSimple(rhsECR);
			uf.join(uf.getLoc(lhsECR), uf.getLoc(rhsECR));
			uf.join(uf.getFunc(lhsECR), uf.getFunc(rhsECR));
			return;
		}

		if (ReservedFunction.MEMSET.equals(funcName)) {
			Node lhs = stmt.getOperand(2).getSourceNode();
			Node rhs = stmt.getOperand(3).getSourceNode();
			ecrEncoder.toRval(lhs);
			ecrEncoder.toRval(rhs);
			return;
		}
	}

	private void analysis(IRStatement stmt) {
		IOUtils.debug().pln("Preprocess: " + stmt.getLocation() + ": " + stmt);
		switch (stmt.getType()) {
		case DECLARE:
		case DECLARE_ARRAY: {
			Node lhs = stmt.getOperand(0).getSourceNode();
			ecrEncoder.toLval(lhs);
			break;
		}
		case RETURN: {
			String functionName = currentCFG.getName();
			ECR funcECR = ecrEncoder.getFunctionECR(functionName);
			LambdaType funcType = uf.getType(uf.getFunc(uf.getLoc(funcECR)))
					.asLambda();
			ECR retECR = funcType.getRet();

			Node srcNode = stmt.getOperand(0).getSourceNode();
			ECR srcECR = ecrEncoder.toRval(srcNode);

			Type resType = symbolTable.lookupType(functionName).resolve().toFunction()
					.getResult();
			simpleAssign(resType, retECR, srcECR);
			break;
		}
		case INIT:
		case ASSIGN: {
			Node lhsNode = stmt.getOperand(0).getSourceNode();
			Node rhsNode = stmt.getOperand(1).getSourceNode();

			Type lhsType = CType.getType(lhsNode);
			Type rhsType = CType.getType(rhsNode);

			ECR lhsECR = ecrEncoder.toRval(lhsNode);

			/* Resolve the syntax sugar of assign function to a function pointer */
			boolean isFuncType = rhsType.resolve().isFunction();
			ECR rhsECR = isFuncType ? ecrEncoder.toLval(rhsNode)
					: ecrEncoder.toRval(rhsNode);

			simpleAssign(lhsType, lhsECR, rhsECR);
			break;
		}
		case ALLOCA:
		case CALLOC:
		case MALLOC: {
			Node lhs = stmt.getOperand(0).getSourceNode();
			Type lhsType = CType.getType(lhs);
			ECR lhsECR = ecrEncoder.toRval(lhs);

			heapAssign(lhsType, lhsECR);
			break;
		}
		case CALL: {
			Node funcNode = stmt.getOperand(0).getSourceNode();
			String funcName = CAnalyzer.toFunctionName(funcNode);

			if (funcName != null) { // Function call
				if (ReservedFunction.isReserved(funcName)) {
					processReservedFunctionCall(funcName, stmt);
					IOUtils.debug().pln("Reserved function call: " + funcName);
					break;
				}

				Type funcType = symbolTable.lookupType(funcName).resolve();
				if (funcType.isFunction()) { // Otherwise, function pointer
					if (!symbolTable.rootScope().isDefined(funcName)) {
						IOUtils.debug().pln("Undefined function call: " + funcName);
						// Encode the undefined function node, otherwise, function inline
						// processor will complain about cannot the ECR of the function node.
						ecrEncoder.toRval(funcNode);
						break;
					}
				}
			}

			processCallSite(stmt);
			break;
		}
		case FREE:
		case ASSERT:
		case ASSUME: {
			Node src = stmt.getOperand(0).getSourceNode();
			ecrEncoder.toRval(src);
			break;
		}
		default:
		}
	}

	private void processCallSite(IRStatement stmt) {
		Node funcNode = stmt.getOperand(0).getSourceNode();
		ECR funcECR = ecrEncoder.toRval(funcNode);
		assert (null != funcECR);
		Type funcType = CType.getType(funcNode).resolve();

		if (funcType.isPointer()) {
			funcECR = uf.getLoc(funcECR);
			funcType = funcType.toPointer().getType();
		}

		/* For the function pointer declared but not yet assigned */
		if (uf.getType(funcECR).isBottom()) {
			IOUtils.err().println("WARNING: get Func of " + funcECR);
			Size size = Size.createForType(PointerT.TO_VOID);
			uf.expand(funcECR, size);
		}

		ECR lamECR = uf.getFunc(funcECR);

		if (uf.getType(lamECR).isBottom()) {
			ValueType lamType = ecrEncoder.getLamdaType(funcType);
			uf.setType(lamECR, lamType);
		}

		LambdaType lamType = uf.getType(lamECR).asLambda();
		int paramIndex = 1;

		// Process the return value first.
		if (!funcType.toFunction().getResult().isVoid()) {
			Node retNode = stmt.getOperand(1).getSourceNode();
			ECR retECR = ecrEncoder.toRval(retNode);
			ECR lamRetECR = lamType.getRet();
			ValueType lamRetType = uf.getType(lamRetECR);
			paramRetAssign(lamRetType.getSize(), retECR, lamRetECR);

			++paramIndex; // Shift by one to skip return value.
		}

		// Process the parameters.
		Iterator<ECR> paramECRItr = lamType.getParams().iterator();
		while (paramIndex < stmt.getOperands().size()) {
			Node srcNode = stmt.getOperand(paramIndex).getSourceNode();
			Type paramType = CType.getType(srcNode).resolve();

			// Resolve the syntax sugar of assign function to a function pointer
			ECR argECR = paramType.isFunction() ? ecrEncoder.toLval(srcNode)
					: ecrEncoder.toRval(srcNode);

			if (paramECRItr.hasNext()) {
				ECR paramECR = paramECRItr.next();
				ValueType argType = uf.getType(argECR);
				paramRetAssign(argType.getSize(), paramECR, argECR);
			} else {
				lamType.addParamECR(argECR); // varg
			}

			++paramIndex;
		}
	}

	private void initChecker() {
		uf.clearPointerArithmetic();
		uf.normalizeStructECRs();
		uf.normalizeCollapseECRs();
		ecrChecker = ECRChecker.create(uf, symbolTable, ecrEncoder);
	}

	@Override
	public void reset() {
		uf.reset();
	}

	@Override
	public ECR getPtsToFieldRep(ECR base) {
		if (base.getType().isBottom())
			IOUtils.err().println("WARNING: get points-to Loc ECR of bottom " + base);
		return uf.findRoot(uf.getLoc(base));
	}

	@Override
	public ECR getPtsToRep(Node node) {
		return getPtsToFieldRep(getRep(node));
	}

	@Override
	public Map<Range<Long>, ECR> getStructMap(ECR structECR, long length) {
		ValueType structType = uf.getType(structECR);
		if (!structType.isStruct())
			return Collections.emptyMap();

		return structType.asStruct().getFieldMap();
	}

	/**
	 * Return <code>void</code> type is <code>rep</code> is with the bottom type
	 * (not yet allocated)
	 */
	@Override
	public long getRepWidth(ECR ecr) {
		long defaultWidth = CType.getInstance().getWidth(CType.getUnitType());
		if (Preferences.isSet(Preferences.OPTION_MULTI_CELL))
			return defaultWidth;

		long ptrWidth = CType.getInstance().getWidth(PointerT.TO_VOID);

		switch (ecr.getType().getKind()) {
		// structure's cell type is pointer (not the size of structure)
		case STRUCT:
			return ptrWidth;
		case BOTTOM:
			return defaultWidth;
		default: {
			Size size = ecr.getType().getSize();
			if (!size.isNumber())
				return defaultWidth;

			long value = size.getValue();
			if (value == 0)
				return defaultWidth; // array type without length (stdlib.h)

			return CType.getInstance().toWidth(value);
		}
		}
	}

	@Override
	public void buildSnapShot() {
		snapShot = uf.snapshot();
	}

	@Override
	public String getRepId(ECR ecr) {
		return String.valueOf(ecr.getId());
	}

	@Override
	public ECR getRep(Node node) {
		return uf.findRoot(ecrChecker.toRval(node));
	}

	@Override
	public ECR getStackRep(Node node) {
		ECR rep = getRep(node);
		xtc.type.Type lvalType = CType.getType(node);

		/*
		 * The address should belongs to the group it points-to, where to reason
		 * about disjointness
		 */
		if (lvalType.resolve().isStruct() || lvalType.resolve().isUnion()
				|| lvalType.resolve().isArray() || lvalType.resolve().isFunction()) {
			rep = getPtsToFieldRep(rep);
		}
		return rep;
	}

	@Override
	public void addRegion(Expression region, Node ptrNode) {
		if (!IOUtils.debugEnabled())
			return;

		/* The freshRegionVar should have the same scope and type as place holder */
		ecrChecker.createRegionVar(region, ptrNode);
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public void addVar(Expression lval, Node lvalNode) {
		if (!IOUtils.debugEnabled())
			return;

		ecrChecker.addStackVar(lval, lvalNode);
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public String displaySnapShot() {
		buildSnapShot();

		StringBuilder sb = new StringBuilder().append('\n').append(
				"The result of cell-based field-sensitive Steensgaard analysis:\n");

		for (Entry<ECR, Collection<IRVar>> entry : snapShot.entrySet()) {
			ECR ecr = entry.getKey();
			if (uf.getType(ecr).isLambda())
				continue;
			Collection<IRVar> vars = entry.getValue();
			if (!vars.isEmpty()) {
				sb.append("Partition ").append(ecr.getId()).append(": ");
				sb.append(uf.getType(ecr)).append("\n { ");

				for (IRVar var : vars)
					sb.append(var.getName()).append(' ');
				sb.append("}\n");
			}
		}
		return sb.toString();
	}

	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		ECR rep = ecrChecker.toRval(funcNode);
		Type funcType = CType.getType(funcNode).resolve();
		if (funcType.isPointer())
			rep = getPtsToFieldRep(rep);
		ECR funcRep = uf.getFunc(rep);
		return uf.getEquivClass(funcRep);
	}

	@Override
	public Collection<ECR> getFieldReps(ECR rep, Type Ty) {
		Collection<ECR> reps = Sets.newLinkedHashSet();
		collectFieldReps(reps, rep);
		return reps;
	}

	private void collectFieldReps(Collection<ECR> reps, ECR rep) {
		if (reps.contains(rep))
			return;

		reps.add(rep);
		ValueType repType = uf.getType(rep);

		if (repType.isStruct()) {
			for (ECR elem : repType.asStruct().getFieldMap().values()) {
				ECR elemRep = uf.findRoot(uf.getLoc(elem));
				collectFieldReps(reps, elemRep);
			}
		}
	}

	private void heapAssign(Type lhsType, ECR lhs) {
		Size rangeSize = Size.createForType(lhsType);

		ValueType lhsECRType = uf.getType(lhs);
		Size lhsSize = lhsECRType.getSize();
		if (!Size.isLessThan(rangeSize, lhsSize)) {
			uf.expand(lhs, rangeSize);
		}

		ECR lhsLoc = uf.getLoc(lhs);
		ValueType lhsLocType = uf.getType(lhsLoc);
		if (lhsLocType.isBottom()) {
			ValueType blankType = ValueType.blank(Size.getBot(), Parent.getBottom());
			uf.setType(lhsLoc, blankType);
		}
	}

	private void simpleAssign(Type targetType, ECR lhs, ECR rhs) {
		targetType = targetType.resolve();
		// structure assign, treat like structure pointer assign to unify
		// the structures involved
		if (targetType.isStruct())
			targetType = new PointerT(targetType);
		Size rangeSize = CType.isArithmetic(targetType) ? Size.getBot()
				: Size.createForType(targetType);
		uf.ccjoin(rangeSize, rhs, lhs);
	}

	private void paramRetAssign(Size rangeSize, ECR lhs, ECR rhs) {
		ValueType lhs_type = uf.getType(lhs);
		ValueType rhs_type = uf.getType(rhs);

		Size lhs_size = lhs_type.getSize();
		Size rhs_size = rhs_type.getSize();

		if (!Size.isLessThan(rangeSize, lhs_size))
			uf.expand(lhs, rangeSize);
		if (!Size.isLessThan(rangeSize, rhs_size))
			uf.expand(rhs, rangeSize);

		ECR lhsLoc = uf.getLoc(lhs), rhsLoc = uf.getLoc(rhs);
		ECR lhsFunc = uf.getFunc(lhs), rhsFunc = uf.getFunc(rhs);

		uf.join(rhsLoc, lhsLoc);
		uf.join(rhsFunc, lhsFunc);
	}

	@Override
	public void analyzeVarArg(String func, Type funcTy, Node varArgN) {
		// TODO Auto-generated method stub

	}

	@Override
	public Pair<Integer, Integer> getAliasAnalysisStats(
			IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		LeftValueCollectingPassImpl lvalCollector = new LeftValueCollectingPassImpl();
		lvalCollector.analysis(globalCFG, CFGs);
		Collection<Pair<Node, String>> lvals = lvalCollector.getLeftValues();
		Multimap<ECR, Pair<Node, String>> aliasMap = ArrayListMultimap.create();
		for (Pair<Node, String> lval : lvals) {
			ECR NH = getRep(lval.fst());
			aliasMap.put(NH, lval);
		}

		return Pair.of(lvals.size(), aliasMap.keySet().size());
	}
}