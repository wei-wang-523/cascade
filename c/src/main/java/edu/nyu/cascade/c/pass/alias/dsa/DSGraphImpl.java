package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.util.Pair;
import xtc.tree.Node;
import xtc.type.Type;

final class DSGraphImpl extends DSGraph {

	DSGraphImpl(EquivalenceClasses<GlobalValue> ECs, SuperSet<Type> tss,
			DSGraph GG) {
		super(ECs, tss, GG);
	}

	DSGraphImpl(DSGraph DSG, EquivalenceClasses<GlobalValue> ECs,
			SuperSet<Type> tss, int CloneFlags) {
		super(DSG, ECs, tss, CloneFlags);
	}

	@Override
	String getFunctionNames() {
		int RetNodesSize = getReturnNodes().size();
		if (RetNodesSize == 0) {
			return "Globals graph";
		} else if (RetNodesSize == 1) {
			return getReturnNodes().keySet().iterator().next().getName();
		} else {
			StringBuilder sb = new StringBuilder();
			for (Function func : getReturnNodes().keySet()) {
				sb.append(func.getName()).append(' ');
			}
			sb.deleteCharAt(sb.length() - 1); // Remove last space character
			return sb.toString();
		}
	}

	@Override
	void buildCallGraph(DSCallGraph DCG, Collection<Function> GlobalFunctionList,
			boolean filter) {

		// Get the list of unresolved call sites.
		for (DSCallSite Call : getFunctionCalls()) {

			// Direct calls are easy. We know to where they go.
			Node CallSite = Call.getCallSite();
			if (Call.isDirectCall()) {
				DCG.insert(CallSite, Call.getCalleeF());
			} else {

				Collection<Function> MaybeTargets = Sets.newTreeSet();

				if (Call.getCalleeN().isIncompleteNode())
					continue;

				// Get the list of known targets of this function.
				Call.getCalleeN().addFullFunctionList(MaybeTargets);

				// Ensure that the call graph at least knows about (has a record of)
				// this
				// call site.
				DCG.insert(CallSite, null);

				// Add to the call graph only function targets that have well-defined
				// behavior using LLVM semantics.
				//
				for (Function Func : MaybeTargets) {
					if (!filter || functionIsCallable(CallSite, Func)) {
						DCG.insert(CallSite, Func);
					}
				}

				for (Node MCS : Call.getMappedSites()) {
					for (Function Func : MaybeTargets) {
						if (!filter || functionIsCallable(MCS, Func)) {
							DCG.insert(MCS, Func);
						}
					}
				}
			}
		}
	}

	/**
	 * Description: Determine whether the specified function can be a target of
	 * the specified call site. We allow the user to configure what we consider to
	 * be uncallable at an indirect function call site.
	 */
	private boolean functionIsCallable(Node CS, Function func) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	void removeFunctionCalls(Function F) {
		// TODO Auto-generated method stub

	}

	@Override
	DSNode addObjectToGraph(Value V, boolean UseDeclaredType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	void markIncompleteNodes(int Flags) {
		// TODO Auto-generated method stub
	}

	@Override
	void computeIntPtrFlags() {
		// TODO Auto-generated method stub

	}

	@Override
	void computeExternalFlags(int Flags) {
		// TODO Auto-generated method stub

	}

	@Override
	void removeDeadNodes(int Flags) {
		// TODO Auto-generated method stub

	}

	@Override
	void updateFromGlobalGraph() {
		// TODO Auto-generated method stub

	}

	@Override
	void computeGToGGMapping(Map<DSNode, DSNodeHandle> NodeMap) {
		// TODO Auto-generated method stub

	}

	@Override
	void computeCalleeCallerMapping(DSCallSite CS, Function Callee,
			DSGraph CalleeGraph, Map<DSNode, DSNodeHandle> NodeMap) {
		// TODO Auto-generated method stub

	}

	@Override
	void spliceFrom(DSGraph RHS) {
		Preconditions.checkArgument(this != RHS);
		// Change all of the nodes in RHS to think we are their parent.
		for (DSNode DN : RHS.Nodes) {
			DN.setParentGraph(this);
		}
		// Take all of the nodes.
		splice(Nodes, RHS.Nodes);

		// Take all of the calls.
		splice(FunctionCalls, RHS.FunctionCalls);
		splice(AuxFunctionCalls, RHS.AuxFunctionCalls);

		// Take all of the return nodes.
		splice(ReturnNodes, RHS.ReturnNodes);

		// Same for the VA nodes
		splice(VANodes, RHS.VANodes);

		// Same for the NodeMap
		NodeMap.spliceFrom(RHS.NodeMap);

		// Merge the scalar map in.
		ScalarMap.spliceFrom(RHS.ScalarMap);
	}

	private <T> void splice(Collection<T> LHS, Collection<T> RHS) {
		LHS.addAll(RHS);
		RHS.clear();
	}

	private <T, S> void splice(Map<T, S> LHS, Map<T, S> RHS) {
		LHS.putAll(RHS);
		RHS.clear();
	}

	@Override
	void cloneInto(DSGraph G, int CloneFlags) {
		Preconditions.checkArgument(G != this);

		// Remove alloca or mod/ref bits as specified...
		int BitsToClear = ((CloneFlags & DSSupport.CloneFlags.StripAllocaBit
				.value()) != 0 ? DSSupport.NodeTy.AllocaNode.value() : 0) | ((CloneFlags
						& DSSupport.CloneFlags.StripModRefBits.value()) != 0
								? (DSSupport.NodeTy.ModifiedNode.value()
										| DSSupport.NodeTy.ReadNode.value()) : 0) | ((CloneFlags
												& DSSupport.CloneFlags.StripIncompleteBit.value()) != 0
														? DSSupport.NodeTy.IncompleteNode.value() : 0);
		BitsToClear |= DSSupport.NodeTy.DeadNode.value(); // Clear dead flag...

		Map<DSNode, DSNodeHandle> OldNodeMap = Maps.newHashMap();
		for (DSNode Old : G.getNodes()) {
			assert !(Old.isForwarding()) : "Forward nodes shouldn't be in node list!";
			DSNode New = new DSNodeImpl(Old, this, false);
			New.maskNodeTypes(~BitsToClear);
			OldNodeMap.put(Old, new DSNodeHandle(New, 0));
		}

		// Rewrite the links in the new nodes to point into the current graph now.
		// Note that we don't loop over the node's list to do this. The problem is
		// that re-mapping links can cause recursive merging to happen, which means
		// that node_iterator's can get easily invalidated! Because of this, we
		// loop over the OldNodeMap, which contains all of the new nodes as the
		// .second element of the map elements. Also note that if we re-map a node
		// more than once, we won't break anything.
		for (Entry<DSNode, DSNodeHandle> entry : OldNodeMap.entrySet()) {
			entry.getValue().getNode().remapLinks(OldNodeMap);
		}

		// Copy the scalar map... merging all of the global nodes...
		for (Entry<Value, DSNodeHandle> entry : G.getScalarMap().getValueMap()
				.entrySet()) {
			DSNodeHandle H = ScalarMap.getRawEntryRef(entry.getKey());
			DSNodeHandle OldNH = entry.getValue();
			DSNode OldN = OldNH.getNode();
			if (Nodes.contains(OldN)) {
				H.mergeWith(OldNH);
			} else {
				assert OldNodeMap.containsKey(OldN) : "Unmapped node";
				DSNodeHandle MappedNH = OldNodeMap.get(OldN);
				DSNode MappedN = MappedNH.getNode();
				H.mergeWith(new DSNodeHandle(MappedN, OldNH.getOffset() + MappedNH
						.getOffset()));
			}
		}

		// Copy the node map... merging all of the global nodes...
		for (Entry<Pair<Node, String>, DSNodeHandle> entry : G.getNodeMap()
				.getNodeMap().entrySet()) {
			DSNodeHandle H = NodeMap.getRawEntryRef(entry.getKey().fst());
			DSNodeHandle OldNH = entry.getValue();
			DSNode OldN = OldNH.getNode();
			if (Nodes.contains(OldN)) {
				H.mergeWith(OldNH);
			} else {
				assert OldNodeMap.containsKey(OldN) : "Unmapped node";
				DSNodeHandle MappedNH = OldNodeMap.get(OldN);
				DSNode MappedN = MappedNH.getNode();
				H.mergeWith(new DSNodeHandle(MappedN, OldNH.getOffset() + MappedNH
						.getOffset()));
			}
		}

		if ((CloneFlags & DSSupport.CloneFlags.DontCloneCallNodes.value()) == 0) {
			// Copy the function calls list.
			for (DSCallSite CS : G.getFunctionCalls()) {
				FunctionCalls.add(DSCallSite.createWithDSNodeMap(CS, OldNodeMap));
			}
		}

		// Map the return node pointers over...
		for (Entry<Function, DSNodeHandle> entry : G.ReturnNodes.entrySet()) {
			DSNodeHandle Ret = entry.getValue();
			assert OldNodeMap.containsKey(Ret.getNode()) : "Unmapped node";
			DSNodeHandle MappedRet = OldNodeMap.get(Ret.getNode());
			DSNode MappedRetN = MappedRet.getNode();
			ReturnNodes.put(entry.getKey(), new DSNodeHandle(MappedRetN, MappedRet
					.getOffset() + Ret.getOffset()));
		}

		// Map the VA node pointers over...
		for (Entry<Function, DSNodeHandle> entry : G.getVANodes().entrySet()) {
			DSNodeHandle VarArg = entry.getValue();
			assert OldNodeMap.containsKey(VarArg.getNode()) : "Unmapped node";
			DSNodeHandle MappedVarArg = OldNodeMap.get(VarArg.getNode());
			DSNode MappedVarArgN = MappedVarArg.getNode();
			VANodes.put(entry.getKey(), new DSNodeHandle(MappedVarArgN, MappedVarArg
					.getOffset() + VarArg.getOffset()));
		}
	}

	@Override
	void getFunctionArgumentsForCall(Function F, Collection<DSNodeHandle> Args) {
		// TODO Auto-generated method stub

	}

	@Override
	void mergeInGraph(DSCallSite CS, Collection<DSNodeHandle> Args, DSGraph G2,
			int CloneFlags) {
		// TODO Auto-generated method stub

	}

	@Override
	void mergeInGraph(DSCallSite CS, Function F, DSGraph Graph, int CloneFlags) {
		// TODO Auto-generated method stub

	}

	@Override
	DSCallSite getCallSiteForArguments(Function F) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	DSCallSite getDSCallSiteForCallSite(DSCallSite CS) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	void AssertNodeContainsGlobal(DSNode N, GlobalValue GV) {
		// TODO Auto-generated method stub

	}

	@Override
	void AssertCallSiteInGraph(DSCallSite CS) {
		// TODO Auto-generated method stub

	}

	@Override
	void AssertCallNodesInGraph() {
		// TODO Auto-generated method stub

	}

	@Override
	void AssertAuxCallNodesInGraph() {
		// TODO Auto-generated method stub

	}

	@Override
	void AssertGraphOK() {
		// TODO Auto-generated method stub

	}

	@Override
	void removeTriviallyDeadNodes() {
		// TODO Auto-generated method stub

	}
}
