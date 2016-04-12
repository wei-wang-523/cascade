package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;
import java.util.Map.Entry;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;
import xtc.type.Type;

abstract class DataStructuresImpl extends DataStructures {

	DataStructuresImpl(String name) {
		super(name);
	}
	
	@Override
	public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		runOnModule(SymbolTable, globalCFG, CFGs);
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	@Override
	DataStructures init(SymbolTable symbolTable) {
		Preconditions.checkArgument(SymbolTable == null);
		GraphSource = null;
		Clone = false;
		SymbolTable = symbolTable;
		TypeSS = new SuperSet<Type>();
		GlobalsGraph = new DSGraphImpl(GlobalECs, TypeSS, null);
		ValueManager = new ValueManager(SymbolTable);
		return this;
	}

	@Override
	DSGraph getOrCreateGraph(Function F) {
		Preconditions.checkNotNull(F);
		if(DSInfo.containsKey(F)) return DSInfo.get(F);
		
		assert(GraphSource.hasDSGraph(F));
		DSGraph BaseGraph = GraphSource.getDSGraph(F);
		
		DSGraph G;
		if (Clone) {
			G = new DSGraphImpl(BaseGraph, GlobalECs, TypeSS, 0);
			if (ResetAuxCalls) {
				G.getAuxFunctionCalls().clear();
				G.getAuxFunctionCalls().addAll(G.getFunctionCalls());
			}
		} else {
			G = new DSGraphImpl(GlobalECs, TypeSS, null);
			G.spliceFrom(BaseGraph);
			if (ResetAuxCalls) {
				G.getAuxFunctionCalls().clear();
				G.getAuxFunctionCalls().addAll(G.getFunctionCalls());
			}
			G.setUseAuxCalls();
			G.setGlobalsGraph(GlobalsGraph);
			
			// Note that this graph is the graph for ALL of the function in the SCC, not
		    // just F.
			for (Entry<Function, DSNodeHandle> entry : G.getReturnNodes().entrySet()) {
			      if (entry.getKey() != F) DSInfo.put(entry.getKey(), G);
			}
		}
		
		return G;
	}
	
	@Override
	void buildGlobalECs(Set<GlobalValue> ECGlobals) {
		DSScalarMap SM = GlobalsGraph.getScalarMap();
		EquivalenceClasses<GlobalValue> GlobalECs = SM.getGlobalECs();
		for (DSNode N : GlobalsGraph.getNodes()) {
			if (N.numGlobals() <= 1) continue;

		    // First, build up the equivalence set for this block of globals.
		    Iterator<GlobalValue> GVItr = N.getGlobals().iterator();
		    GlobalValue First = GVItr.next();
		    if (GlobalECs.findValue(First) != null) {
		    	GlobalValue FirstLeader = GlobalECs.getLeaderValue(First);
		    	if (!FirstLeader.equals(First)) GlobalECs.unionSets(FirstLeader, First);
		    	First = FirstLeader;
		    }
		    
		    while (GVItr.hasNext()) {
		    	GlobalValue GV = GVItr.next();
		    	GlobalECs.unionSets(First, GV);
		    	ECGlobals.add(GV);
		    	if (SM.contains(GV)) {
		    		SM.erase(GV);
		    	} else {
		    		IOUtils.err().println("Global missing in scalar map " + GV.getName());
		    	}
		    }

		    // Next, get the leader element.
		    assert First == GlobalECs.getLeaderValue(First) :
		           "First did not end up being the leader?";

		    // Finally, change the global node to only contain the leader.
		    N.clearGlobals();
		    N.addGlobal(First);
		}
	}

	@Override
	void eliminateUsesOfECGlobals(DSGraph G, Set<GlobalValue> ECGlobals) {
		  DSScalarMap SM = G.getScalarMap();
		  EquivalenceClasses<GlobalValue> GlobalECs = SM.getGlobalECs();

		  Collection<GlobalValue> SMGVV = Sets.newHashSet(SM.getGlobalSet());

		  for (GlobalValue GV : SMGVV) {
		    if (!ECGlobals.contains(GV)) continue;

		    final DSNodeHandle GVNH = SM.get(GV);
		    assert !GVNH.isNull() : "Global has null NH!?";

		    // Okay, this global is in some equivalence class.  Start by finding the
		    // leader of the class.
		    GlobalValue Leader = GlobalECs.getLeaderValue(GV);

		    // If the leader isn't already in the graph, insert it into the node
		    // corresponding to GV.
		    if (!SM.getGlobalSet().contains(Leader)) {
		    	GVNH.getNode().addGlobal(Leader);
		    	SM.put(Leader, GVNH);
		    } else {
		    	// Otherwise, the leader is in the graph, make sure the nodes are the
		    	// merged in the specified graph.
		    	DSNodeHandle LNH = SM.getRawEntryRef(Leader);
		    	if (LNH.getNode() != GVNH.getNode())
		    		LNH.mergeWith(GVNH);
		    }

		    // Next step, remove the global from the DSNode.
		    GVNH.getNode().removeGlobal(GV);

		    // Finally, remove the global from the ScalarMap.
		    SM.erase(GV);
		  }
	}

	@Override
	DataStructures init(DataStructures D, boolean clone,
			boolean useAuxCalls, boolean copyGlobalAuxCalls, boolean resetAux) {
		  Preconditions.checkArgument(GraphSource == null); // Already init
		  GraphSource = D;
		  Clone = clone;
		  ResetAuxCalls = resetAux;
		  TypeSS = D.TypeSS;
		  CallGraph = D.CallGraph;
		  GlobalFunctionList = D.GlobalFunctionList;
		  GlobalECs = D.getGlobalECs();
		  GlobalsGraph = new DSGraphImpl(D.getGlobalsGraph(), GlobalECs, TypeSS,
				  copyGlobalAuxCalls? DSSupport.CloneFlags.CloneAuxCallNodes.value()
						  : DSSupport.CloneFlags.DontCloneAuxCallNodes.value());
		  if (useAuxCalls) GlobalsGraph.setUseAuxCalls();

		  //
		  // Tell the other DSA pass if we're stealing its graph.
		  //
		  if (!clone) D.DSGraphStolen = true;
		  
		  SymbolTable = D.SymbolTable;
		  ValueManager = new ValueManager(SymbolTable);
		  return this;
	}

	@Override
	void formGlobalECs() {
		// Grow the equivalence classes for the globals to include anything that we
		// now know to be aliased.
		Set<GlobalValue> ECGlobals = Sets.newTreeSet();
		buildGlobalECs(ECGlobals);
		if (!ECGlobals.isEmpty()) {
			for (DSGraph graph : DSInfo.values()) {
				eliminateUsesOfECGlobals(graph, ECGlobals);
			}
		}
	}

	@Override
	void cloneIntoGlobals(DSGraph G, int cloneFlags) {
		// When this graph is finalized, clone the globals in the graph into the
		// globals graph to make sure it has everything, from all graphs.
		DSScalarMap MainSM = G.getScalarMap();
		ReachabilityCloner RC = new ReachabilityCloner(GlobalsGraph, G, cloneFlags, true);

		// Clone everything reachable from globals in the function graph into the
		// globals graph.
		for (GlobalValue GV : MainSM.getGlobalSet()) {
		    RC.getClonedNH(MainSM.get(GV));
		}
	}

	@Override
	void cloneGlobalsInto(DSGraph Graph, int cloneFlags) {
		// If this graph contains main, copy the contents of the globals graph over.
		// Note that this is *required* for correctness.  If a callee contains a use
		// of a global, we have to make sure to link up nodes due to global-argument
		// bindings.
		DSGraph GG = Graph.getGlobalsGraph();
		ReachabilityCloner RC = new ReachabilityCloner(Graph, GG, cloneFlags, true);

		// Clone the global nodes into this graph.
		for (GlobalValue GV : Graph.getScalarMap().getGlobalSet()) {
			RC.getClonedNH(GG.getNodeForValue(GV));
		}
	}

	@Override
	void restoreCorrectCallGraph() {
		// TODO Auto-generated method stub
		
	}

	@Override
	void formGlobalFunctionList() {
		  Collection<Function> List = Lists.newArrayList();
		  DSScalarMap SM = GlobalsGraph.getScalarMap();
		  EquivalenceClasses<GlobalValue> EC = GlobalsGraph.getGlobalECs();
		  for (GlobalValue GV : SM.getGlobalSet()) {
			  EquivalenceClasses<GlobalValue>.ECValue ECI = EC.findValue(GV);
			  if (ECI == null) {
				  if (GV instanceof Function) {
					  List.add((Function) GV);
				  }
			  } else {
				  if (ECI.isLeader()) {
					  while (ECI.getNext() != null) {
						  GlobalValue ECIData = ECI.getData();
						  if (ECIData instanceof Function) {
							  List.add((Function) ECIData);
						  }
						  ECI = ECI.getNext();
					  }
				  }
			  }
		  }
		  GlobalFunctionList.addAll(List); List.clear();
	}

	@Override
	void deleteValue(Value V) {
		// TODO Auto-generated method stub
		
	}

	@Override
	void copyValue(Value From, Value To) {
		// TODO Auto-generated method stub
		
	}
}
