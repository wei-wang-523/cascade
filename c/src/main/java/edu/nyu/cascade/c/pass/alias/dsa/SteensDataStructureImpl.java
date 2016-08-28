package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.common.collect.Sets.SetView;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRPass;
import xtc.type.Type;

/***
 * ===- Steensgaard.cpp - Context Insensitive Data Structure Analysis ------===
 * 
 * The LLVM Compiler Infrastructure
 * 
 * This file was developed by the LLVM research group and is distributed under
 * the University of Illinois Open Source License. See LICENSE.TXT for details.
 * 
 * ===----------------------------------------------------------------------===/
 * /
 * 
 * This pass computes a context-insensitive data analysis graph. It does this by
 * computing the local analysis graphs for all of the functions, then merging
 * them together into a single big graph without cloning.
 *
 */

public class SteensDataStructureImpl extends DataStructuresImpl {
	private DataStructures LocalDS;
	private DSGraph ResultGraph;

	private SteensDataStructureImpl() {
		super("dsa-steens");
	}

	static SteensDataStructureImpl create(IRPass... prePasses) {
		SteensDataStructureImpl ds = new SteensDataStructureImpl();
		assert (prePasses.length == 1);
		assert (prePasses[0] instanceof DataStructures);
		ds.LocalDS = (DataStructures) prePasses[0];
		return ds;
	}

	/**
	 * getDSGraph - Return the data structure graph for the specified function.
	 */
	DSGraph getDSGraph(Function F) {
		return F.isDeclaration() ? null : ResultGraph;
	}

	boolean hasDSGraph(Function F) {
		return !F.isDeclaration();
	}

	DSGraph getOrCreateGraph(Function F) {
		return getResultGraph();
	}

	/**
	 * getDSGraph - Return the data structure graph for the whole program.
	 */
	DSGraph getResultGraph() {
		return ResultGraph;
	}

	@Override
	public SteensDataStructureImpl init(SymbolTable symbolTable) {
		return (SteensDataStructureImpl) super.init(symbolTable);
	}

	@Override
	boolean runOnModule(SymbolTable symTbl, IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs) {
		// Result graph should not be already allocated!
		Preconditions.checkArgument(ResultGraph == null);
		Preconditions.checkNotNull(LocalDS);

		// Get a copy for the globals graph.
		DSGraph GG = LocalDS.getGlobalsGraph();
		GlobalsGraph = new DSGraphImpl(GG, GG.getGlobalECs(), TypeSS, 0);

		// Create a new, empty, graph...
		ResultGraph = new DSGraphImpl(LocalDS.getGlobalECs(), TypeSS, GlobalsGraph);

		// Loop over the rest of the module, merging graphs for non-external
		// functions into this graph.
		for (IRControlFlowGraph CFG : CFGs) {
			String FuncID = CFG.getName();
			Type FuncTy = SymbolTable.lookupType(FuncID);
			Function FB = (Function) ValueManager.get(FuncID, FuncTy);
			if (!FB.isDeclaration()) {
				ResultGraph.spliceFrom(LocalDS.getDSGraph(FB));
			}
		}

		ResultGraph.removeTriviallyDeadNodes();

		// FIXME: Must recalculate and use the Incomplete markers!!

		// Now that we have all of the graphs inlined, we can go about eliminating
		// call nodes...

		// Start with a copy of the original call sites.
		List<DSCallSite> Calls = Lists.newArrayList(ResultGraph.getFunctionCalls());

		{
			// Loop over and eliminate direct calls
			Iterator<DSCallSite> CallItr = Calls.iterator();
			while (CallItr.hasNext()) {
				DSCallSite Call = CallItr.next();
				if (Call.isDirectCall()) {
					Function F = Call.getCalleeF();
					if (!F.isDeclaration()) {
						ResolveFunctionCall(F, Call, ResultGraph.getReturnNodeFor(F));
					}
					CallItr.remove();
				}
			}
		}

		if (!Calls.isEmpty()) {
			// Loop over indirect calls
			boolean changed;
			Map<DSNode, Set<Function>> IndirectCallFuncs = Maps.newHashMap();
			do {
				changed = false;
				for (DSCallSite Call : Calls) {
					Set<Function> CallFuncs = Sets.newHashSet();
					DSNode CallN = Call.getCalleeN();
					CallN.addFullFunctionList(CallFuncs);
					Set<Function> PreCallFuns = IndirectCallFuncs.put(CallN, CallFuncs);
					SetView<Function> DiffCallFuns;
					if (PreCallFuns == null) {
						DiffCallFuns = Sets.difference(CallFuncs, Sets.newHashSet());
					} else {
						DiffCallFuns = Sets.difference(CallFuncs, PreCallFuns);
					}

					if (!DiffCallFuns.isEmpty()) {
						changed = true;
						for (Function F : DiffCallFuns) {
							if (!F.isDeclaration()) {
								ResolveFunctionCall(F, Call, ResultGraph.getReturnNodeFor(F));
							}
						}
					}
				}
			} while (changed);
		}

		// Update the "incomplete" markers on the nodes, ignoring unknownness due to
		// incoming arguments...
		ResultGraph.maskIncompleteMarkers();
		ResultGraph.markIncompleteNodes(
				DSSupport.MarkIncompleteFlags.MarkFormalArgs.value()
						| DSSupport.MarkIncompleteFlags.IgnoreGlobals.value());

		// Remove any nodes that are dead after all of the merging we have done...
		ResultGraph.removeDeadNodes(
				DSSupport.RemoveDeadNodesFlags.KeepUnreachableGlobals.value());

		GlobalsGraph.removeTriviallyDeadNodes();
		GlobalsGraph.maskIncompleteMarkers();

		// Mark external globals incomplete.
		GlobalsGraph.markIncompleteNodes(
				DSSupport.MarkIncompleteFlags.IgnoreGlobals.value());

		// Copy GlobalsGraph into ResultGraph
		ResultGraph.spliceFrom(GlobalsGraph);

		formGlobalECs();

		// Clone the global nodes into this graph.
		// ReachabilityCloner RC = new ReachabilityCloner(ResultGraph, GlobalsGraph,
		// DSSupport.CloneFlags.DontCloneCallNodes.value() |
		// DSSupport.CloneFlags.DontCloneAuxCallNodes.value(), true);
		//
		// for (GlobalValue GV : GlobalsGraph.getScalarMap().getGlobalSet()) {
		// if (GV instanceof GlobalVariable || GV instanceof Function) {
		// RC.getClonedNH(GlobalsGraph.getNodeForValue(GV));
		// }
		// }

		return false;
	}

	/**
	 * ResolveFunctionCall - Resolve the actual arguments of a call to function F
	 * with the specified call site descriptor. This function links the arguments
	 * and the return value for the call site context-insensitively.
	 */
	private void ResolveFunctionCall(Function F, DSCallSite Call,
			DSNodeHandle RetVal) {
		Preconditions.checkNotNull(ResultGraph);
		DSScalarMap ValMap = ResultGraph.getScalarMap();

		// Handle the return value of the function...
		if (!Call.getRetVal().isNull() && !RetVal.isNull()) {
			RetVal.mergeWith(Call.getRetVal());
		}

		// Loop over all pointer arguments, resolving them to their provided
		// pointers
		int PtrArgIdx = 0;
		Iterator<Value> AI = F.getArguments().iterator();
		while (AI.hasNext() && PtrArgIdx < Call.getNumPtrArgs()) {
			Value Arg = AI.next();
			if (!ValMap.contains(Arg))
				continue;
			Type ArgTy = Arg.getType().resolve();
			if (!(ArgTy.isPointer() || CType.isStructOrUnion(ArgTy)))
				continue;
			DSNodeHandle ParamNH = ValMap.find(Arg);
			DSNodeHandle ArgNH = Call.getPtrArg(PtrArgIdx++);
			ResolveParamAndArg(ParamNH, ArgNH, ArgTy);
		}

		if (AI.hasNext()) {
			DSNodeHandle VAArgNH = Call.getVAVal();
			while (AI.hasNext()) {
				Value Arg = AI.next();
				if (!ValMap.contains(Arg))
					continue;
				Type ArgTy = Arg.getType().resolve();
				if (!(ArgTy.isPointer() || CType.isStructOrUnion(ArgTy)))
					continue;
				DSNodeHandle ParamNH = ValMap.find(Arg);
				ResolveParamAndArg(ParamNH, VAArgNH, ArgTy);
			}
		}
	}

	private void ResolveParamAndArg(DSNodeHandle ParamNH, DSNodeHandle ArgNH,
			Type ArgTy) {
		Preconditions
				.checkArgument(ArgTy.isPointer() || CType.isStructOrUnion(ArgTy));

		if (ArgNH == null) { // Pass nullptr as argument, skip
			return;
		}

		if (ArgTy.isPointer()) {
			if (ParamNH.isNull()) {
				DSNode N = new DSNodeImpl(ResultGraph);
				ParamNH.setTo(N, 0);
			}
			DSNode N = ParamNH.getNode();
			// Mark that the node is written to ...
			N.setModifiedMarker();
			// Ensure a type-record exists
			N.growSizeForType(ArgTy, ParamNH.getOffset());
			ParamNH.addEdgeTo(0, ArgNH);
		} else {
			ParamNH.mergeWith(ArgNH);
		}
	}
}
