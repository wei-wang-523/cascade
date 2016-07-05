package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRPass;
import xtc.type.Type;

public abstract class DataStructures implements IRPass {
	ValueManager ValueManager;

	SymbolTable SymbolTable;

	/// Pass to get Graphs from
	DataStructures GraphSource;

	/// Do we clone Graphs or steal them?
	boolean Clone;

	/// Do we reset the aux list to the func list?
	boolean ResetAuxCalls;

	/// Where are DSGraphs stolen by another pass?
	boolean DSGraphStolen;

	/// DSInfo, one graph for each function
	Map<Function, DSGraph> DSInfo = Maps.newHashMap();

	/// Name for printing
	String printname;

	/// The Globals Graph contains all information on the globals
	DSGraph GlobalsGraph;

	/// GlobalECs - The equivalence classes for each global value that is merged
	/// with other global values in the DSGraphs.
	EquivalenceClasses<GlobalValue> GlobalECs = new EquivalenceClasses<GlobalValue>();

	SuperSet<Type> TypeSS;

	/// CallGraph, as computed so far
	DSCallGraph CallGraph = new DSCallGraphImpl();

	/// List of all address taken functions.
	/// This is used as target, of indirect calls for any indirect call site with
	/// incomplete callee node.
	Collection<Function> GlobalFunctionList = Sets.newTreeSet();

	abstract boolean runOnModule(SymbolTable symTbl, IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs);

	/**
	 * BuildGlobalECs - Look at all of the nodes in the globals graph. If any node
	 * contains multiple globals, DSA will never, ever, be able to tell the
	 * globals apart. Instead of maintaining this information in all of the graphs
	 * throughout the entire program, store only a single global (the "leader") in
	 * the graphs, and build equivalence classes for the rest of the globals.
	 */
	abstract void buildGlobalECs(Set<GlobalValue> ECGlobals);

	/**
	 * EliminateUsesOfECGlobals - Once we have determined that some globals are in
	 * really just equivalent to some other globals, remove the globals from the
	 * specified DSGraph (if present), and merge any nodes with their leader
	 * nodes.
	 */
	abstract void eliminateUsesOfECGlobals(DSGraph G, Set<GlobalValue> ECGlobals);

	abstract DataStructures init(DataStructures D, boolean clone,
			boolean useAuxCalls, boolean copyGlobalAuxCalls, boolean resetAux);

	abstract DataStructures init(SymbolTable symbolTable);

	abstract void formGlobalECs();

	abstract void cloneIntoGlobals(DSGraph G, int cloneFlags);

	abstract void cloneGlobalsInto(DSGraph F, int cloneFlags);

	abstract void restoreCorrectCallGraph();

	abstract void formGlobalFunctionList();

	abstract DSGraph getOrCreateGraph(Function F);

	/// deleteValue/copyValue - Interfaces to update the DSGraphs in the program.
	/// These correspond to the interfaces defined in the AliasAnalysis class.
	abstract void deleteValue(Value V);

	abstract void copyValue(Value From, Value To);

	DataStructures(String name) {
		SymbolTable = null;
		GraphSource = null;
		printname = name;
		GlobalsGraph = null;
		// For now, the graphs are owned by this pass
		DSGraphStolen = false;
	}

	boolean hasDSGraph(Function F) {
		return DSInfo.containsKey(F);
	}

	/// getDSGraph - Return the data structure graph for the specified function.
	///
	DSGraph getDSGraph(Function F) {
		Preconditions.checkArgument(DSInfo.containsKey(F));
		return DSInfo.get(F);
	}

	void setDSGraph(Function F, DSGraph G) {
		DSInfo.put(F, G);
	}

	DSGraph getGlobalsGraph() {
		return GlobalsGraph;
	}

	EquivalenceClasses<GlobalValue> getGlobalECs() {
		return GlobalECs;
	}

	SymbolTable getSymbolTable() {
		return SymbolTable;
	}

	DSCallGraph getCallGraph() {
		return CallGraph;
	}

	SuperSet<Type> getTypeSS() {
		return TypeSS;
	}

	ValueManager getValueManager() {
		return ValueManager;
	}
}
