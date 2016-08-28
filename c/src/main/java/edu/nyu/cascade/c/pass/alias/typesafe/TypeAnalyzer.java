package edu.nyu.cascade.c.pass.alias.typesafe;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.Map;

import xtc.tree.Node;
import xtc.type.Type;
import xtc.type.VoidT;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Queues;
import com.google.common.collect.Range;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.LeftValueCollectingPassImpl;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

/**
 * Type analyzer for Burstall memory model
 * 
 * @author Wei
 *
 */

public class TypeAnalyzer implements IRAliasAnalyzer<FSType> {

	private final Multimap<FSType, IRVar> varTypeMap = HashMultimap.create();
	private final FSTypeEncoder typeEncoder = new FSTypeEncoder();

	public static TypeAnalyzer create() {
		return new TypeAnalyzer();
	}

	@Override
	public void reset() {
		varTypeMap.clear();
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {
		// Analyze the global CFG.
		{
			final Collection<IRBasicBlock> visited = Sets.newHashSet();
			Deque<IRBasicBlock> workList = Queues.newArrayDeque();
			workList.push(globalCFG.getEntry());

			while (!workList.isEmpty()) {
				IRBasicBlock block = workList.pop();
				if (visited.contains(block))
					continue;

				visited.add(block);

				for (IRStatement stmt : block.getStatements()) {
					analysis(stmt);
				}

				for (IREdge<?> outgoing : globalCFG.getOutgoingEdges(block)) {
					workList.add(outgoing.getTarget());
				}
			}
		}

		// Analyze the non-global CFG.
		for (IRControlFlowGraph CFG : CFGs) {
			final Collection<IRBasicBlock> visited = Sets.newHashSet();
			Deque<IRBasicBlock> workList = Queues.newArrayDeque();
			workList.push(CFG.getEntry());

			while (!workList.isEmpty()) {
				IRBasicBlock block = workList.pop();
				if (visited.contains(block))
					continue;

				visited.add(block);

				for (IRStatement stmt : block.getStatements()) {
					analysis(stmt);
				}

				for (IREdge<?> outgoing : CFG.getOutgoingEdges(block)) {
					workList.add(outgoing.getTarget());
				}
			}
		}
	}

	private void analysis(IRStatement stmt) {
		switch (stmt.getType()) {
		case ASSIGN: {
			IRExpression lhs = stmt.getOperand(0);
			IRExpression rhs = stmt.getOperand(1);

			Type lhsType = CType.getType(lhs.getSourceNode());
			Type rhsType = CType.getType(rhs.getSourceNode());

			if (!CType.getInstance().equal(lhsType, rhsType))
				IOUtils.err().println("WARNING: inconsistent type " + stmt);

			break;
		}
		default:
			break;
		}
	}

	/**
	 * Get the points-to type of <code>type</code>. AddressOf reference
	 * <code>&((*a).z)</code> should be taken care in order to pick out the
	 * structure selection feature as <code>(*a).z</code>
	 * 
	 * @param type
	 * @return
	 */
	@Override
	public FSType getPtsToFieldRep(FSType fsType) {
		Type type = fsType.getType();
		Type cellType = type;

		Type cleanType = type.resolve();
		assert (cleanType.isPointer() || cleanType.isArray() || cleanType.isStruct()
				|| cleanType.isUnion());

		if (cleanType.isPointer()) {
			cellType = cleanType.toPointer().getType();
		} else if (cellType.isArray()) {
			cleanType = CType.getArrayCellType(cellType);
		}

		String cellTypeName = typeEncoder.parseTypeName(cellType);
		FSType res = FSType.of(cellType, cellTypeName);
		IOUtils.debug().pln("The points-to rep is " + res);
		return res;
	}

	@Override
	public long getRepWidth(FSType rep) {
		return CType.getInstance().getWidth(rep.getType());
	}

	@Override
	public FSType getPtsToRep(Node node) {
		return getPtsToFieldRep(getRep(node));
	}

	/** Don't bother to build snap shot for Burstall memory model */
	@Override
	public void buildSnapShot() {
	}

	@Override
	public FSType getRep(Node node) {
		return typeEncoder.encodeFSType(node);
	}

	@Override
	public FSType getStackRep(Node node) {
		FSType rep = getRep(node);
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

	/**
	 * Get the name of <code>type</code>
	 */
	@Override
	public String getRepId(FSType fsType) {
		return String.valueOf(fsType.getId());
	}

	@Override
	public void addRegion(Expression region, Node ptrNode) {
		String name = region.asVariable().getName();
		String scopeName = CType.getScopeName(ptrNode);
		FSType fsType = getPtsToFieldRep(getRep(ptrNode));

		IRVar var = VarImpl.create(name, VoidT.TYPE, scopeName);
		varTypeMap.put(fsType, var);

		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public void addVar(Expression lval, Node lvalNode) {
		String name = lvalNode.getString(0);
		Type type = CType.getType(lvalNode);
		String scopeName = CType.getScopeName(lvalNode);

		IRVar var = VarImpl.create(name, type, scopeName);
		FSType fsType = typeEncoder.encodeFSType(lvalNode);

		varTypeMap.put(fsType, var);
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public String displaySnapShot() {
		StringBuilder sb = new StringBuilder();
		sb.append('\n').append("The result of type analysis: \n");
		for (FSType fsType : varTypeMap.keySet()) {
			sb.append('\t').append(getRepId(fsType)).append(": ");
			sb.append("Partition ").append(fsType.getTypeName()).append(" { ");

			for (IRVar var : varTypeMap.get(fsType)) {
				sb.append(var.getName()).append(' ');
			}
			sb.append("}\n");
		}
		return sb.toString();
	}

	@Override
	public Map<Range<Long>, FSType> getStructMap(FSType type, long length) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<FSType> getFieldReps(FSType rep, Type Ty) {
		return Collections.singleton(rep);
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
		Multimap<FSType, Pair<Node, String>> aliasMap = ArrayListMultimap.create();
		for (Pair<Node, String> lval : lvals) {
			FSType NH = getRep(lval.fst());
			aliasMap.put(NH, lval);
		}

		return Pair.of(lvals.size(), aliasMap.keySet().size());
	}
}