package edu.nyu.cascade.c.pass.alias.dsa;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CPrinter;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.alias.dsa.DSSupport.NodeTy;
import edu.nyu.cascade.util.Pair;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.type.Type;

/***
 * 
 * DSGraph - The graph that represents a function.
 *
 */

abstract class DSGraph {
	private DSGraph GlobalsGraph;	// The common graph of global objects

	// This is use to differentiate between Local and the rest of the passes.
	// Local should use the FunctionCalls vector that has all the DSCallSites.
	// All other passes, should use the Aux calls vector, as they process and 
	// subsequently might remove some DSCall Sites. Once those call sites
	// have been resolved, we must not revisit them again.
	// UseAuxCalls is false for Local. And true for the other passes.
	private boolean UseAuxCalls;	
	
	protected final Collection<DSNode> Nodes = Sets.newTreeSet();
	
	protected final DSScalarMap ScalarMap;
	
	protected final DSNodeMap NodeMap;
	
	// ReturnNodes - A return value for every function merged into this graph.
	// Each DSGraph may have multiple functions merged into it at any time, which
	// is used for representing SCCs.
	//
	protected final Map<Function, DSNodeHandle> ReturnNodes = Maps.newHashMap();

	// VANodes - Special "Variable Argument" Node for each function
	//
	protected final Map<Function, DSNodeHandle> VANodes = Maps.newHashMap();
	
	// FunctionCalls - This list maintains a single entry for each call
	// instruction in the current graph.  The first entry in the vector is the
	// scalar that holds the return value for the call, the second is the function
	// scalar being invoked, and the rest are pointer arguments to the function.
	// This vector is built by the Local graph and is never modified after that.
	//	
	protected List<DSCallSite> FunctionCalls = Lists.newArrayList();
	
	// AuxFunctionCalls - This vector contains call sites that have been processed
	// by some mechanism.  In practice, the BU Analysis uses this vector to hold
	// the _unresolved_ call sites, because it cannot modify FunctionCalls.
	//
	protected List<DSCallSite> AuxFunctionCalls = Lists.newArrayList();
	
	private SuperSet<Type> TypeSS;
	
	DSGraph(EquivalenceClasses<GlobalValue> ECs, SuperSet<Type> tss,
			DSGraph GG) {
		GlobalsGraph = GG;
		UseAuxCalls = false;
		ScalarMap = new DSScalarMap(ECs);
		NodeMap = new DSNodeMap();
		TypeSS = new SuperSet<Type>(tss);
	}
	
	DSGraph(DSGraph DSG, EquivalenceClasses<GlobalValue> ECs,
			SuperSet<Type> tss, int CloneFlags) {
		GlobalsGraph = null;
		ScalarMap = new DSScalarMap(ECs);
		NodeMap = new DSNodeMap();
		TypeSS = new SuperSet<Type>(tss);
		UseAuxCalls = false;
		cloneInto(DSG, CloneFlags);
	}
	
	DSGraph getGlobalsGraph() { return GlobalsGraph; }
	
	void setGlobalsGraph(DSGraph G) { GlobalsGraph = G; }
	
	/// getGlobalECs - Return the set of equivalence classes that the global
	/// variables in the program form.
	EquivalenceClasses<GlobalValue> getGlobalECs() {
		return ScalarMap.getGlobalECs();
	}

	SuperSet<Type> getTypeSS() {
		return TypeSS;
	}

	/// setUseAuxCalls - If you call this method, the auxiliary call vector will
	/// be used instead of the standard call vector to the dot file.
	///
	void setUseAuxCalls() { UseAuxCalls = true; }
	boolean shouldUseAuxCalls() { return UseAuxCalls; }	
	
	/// getFunctionNames - Return a space separated list of the name of the
	/// functions in this graph (if any)
	///
	abstract String getFunctionNames();
	
	/// addNode - Add a new node to the graph.
	///
	void addNode(DSNode N) { Nodes.add(N); }
	void unlinkNode(DSNode N) { Nodes.remove(N); }

	/// getScalarMap - Get a map that describes what the nodes the scalars in this
	/// function point to...
	///
	DSScalarMap getScalarMap() { return ScalarMap; }
	
	/// getNodeMap - Get a map that describes what the nodes the DSNodeHandle in this
	/// function point to...
	///
	DSNodeMap getNodeMap() { return NodeMap; }

	Collection<DSNode> getNodes() {
		return Nodes;
	}

	/// getFunctionCalls - Return the list of call sites in the original local
	/// graph...
	///
	List<DSCallSite> getFunctionCalls() { return FunctionCalls;}

	/// getAuxFunctionCalls - Get the call sites as modified by whatever passes
	/// have been run.
	///
	List<DSCallSite> getAuxFunctionCalls() { return AuxFunctionCalls; }

	// addAuxFunctionCall - Add a call site to the AuxFunctionCallList
	void addAuxFunctionCall(DSCallSite D) { AuxFunctionCalls.add(D); }

	abstract void buildCallGraph(DSCallGraph DCG, Collection<Function> GlobalFunctionList, boolean filter);

	/// removeFunction - Specify that all call sites to the function have been
	/// fully specified by a pass such as StdLibPass.
	abstract void removeFunctionCalls(Function F);
	
	DSNodeHandle getNodeForValue(Value V) { return ScalarMap.get(V); }
	
	boolean hasNodeForValue(Value V) { return ScalarMap.find(V) != null; }
	
	void eraseNodeForValue(Value V) { ScalarMap.erase(V); }
	
	Map<Function, DSNodeHandle> getReturnNodes() { return ReturnNodes; }
	
	DSNodeHandle getReturnNodeFor(Function F) {
		Preconditions.checkArgument(ReturnNodes.containsKey(F));
		return ReturnNodes.get(F);
	}
	
	Map<Function, DSNodeHandle> getVANodes() { return VANodes; }
	
	DSNodeHandle getVANodeFor(Function F) {
		Preconditions.checkArgument(VANodes.containsKey(F));
		return VANodes.get(F);
	}
	
	DSNodeHandle getOrCreateReturnNodeFor(Function F) {
		if(ReturnNodes.containsKey(F)) return ReturnNodes.get(F);
		DSNodeHandle NH = new DSNodeHandle();
		ReturnNodes.put(F, NH);
		return NH;
	}
	
	DSNodeHandle getOrCreateVANodeFor(Function F) {
		if(VANodes.containsKey(F)) return VANodes.get(F);
		DSNodeHandle NH = new DSNodeHandle();
		VANodes.put(F, NH);
		return NH;
	}

	/// containsFunction - Return true if this DSGraph contains information for
	/// the specified function.
	boolean containsFunction(Function F) {
		return ReturnNodes.containsKey(F);
	}

	/// getGraphSize - Return the number of nodes in this graph.
	///
	int getGraphSize() {
		return Nodes.size();
	}

	/// addObjectToGraph - This method can be used to add global, stack, and heap
	/// objects to the graph.  This can be used when updating DSGraphs due to the
	/// introduction of new temporary objects.  The new object is not pointed to
	/// and does not point to any other objects in the graph.  Note that this
	/// method initializes the type of the DSNode to the declared type of the
	/// object if UseDeclaredType is true, otherwise it leaves the node type as
	/// void.
	abstract DSNode addObjectToGraph(Value V, boolean UseDeclaredType);
	
	/// maskNodeTypes - Apply a mask to all of the node types in the graph.  This
	/// is useful for clearing out masks like Incomplete
	void maskNodeTypes(int Mask) {
		for(DSNode N : Nodes) {
			N.maskNodeTypes(Mask);
		}
	}
	
	void maskIncompleteMarkers() {
		maskNodeTypes(~NodeTy.IncompleteNode.value());
	}

	// markIncompleteNodes - Traverse the graph, identifying nodes that may be
	// modified by other functions that have not been resolved yet.  This marks
	// nodes that are reachable through three sources of "unknownness":
	//   Global Variables, Function Calls, and Incoming Arguments
	//
	// For any node that may have unknown components (because something outside
	// the scope of current analysis may have modified it), the 'Incomplete' flag
	// is added to the NodeType.
	//
	abstract void markIncompleteNodes(int Flags);
	
	// Mark nodes that have overlapping Int and Pointer types.
	abstract void computeIntPtrFlags();
	
	// Mark all reachable from external as external.
	abstract void computeExternalFlags(int Flags);

	// removeDeadNodes - Use a reachability analysis to eliminate subgraphs that
	// are unreachable.  This often occurs because the data structure doesn't
	// "escape" into it's caller, and thus should be eliminated from the caller's
	// graph entirely.  This is only appropriate to use when inlining graphs.
	//
	abstract void removeDeadNodes(int Flags);
	
	abstract void updateFromGlobalGraph();
	
	/// computeNodeMapping - Given roots in two different DSGraphs, traverse the
	/// nodes reachable from the two graphs, computing the mapping of nodes from
	/// the first to the second graph.
	///
//	abstract static void computeNodeMapping(DSNodeHandle NH1, DSNodeHandle NH2, 
//			Map<DSNode, DSNodeHandle> NodeMap, boolean StrictChecking);

	/// computeGToGGMapping - Compute the mapping of nodes in the graph to nodes
	/// in the globals graph.
	abstract void computeGToGGMapping(Map<DSNode, DSNodeHandle> NodeMap);

	/// computeCalleeCallerMapping - Given a call from a function in the current
	/// graph to the 'Callee' function (which lives in 'CalleeGraph'), compute the
	/// mapping of nodes from the callee to nodes in the caller.
	abstract void computeCalleeCallerMapping(DSCallSite CS, Function Callee,
			DSGraph CalleeGraph, Map<DSNode, DSNodeHandle> NodeMap);

	/// spliceFrom - Logically perform the operation of cloning the RHS graph into
	/// this graph, then clearing the RHS graph.  Instead of performing this as
	/// two separate operations, do it as a single, much faster, one.
	///
	abstract void spliceFrom(DSGraph RHS);

	/// cloneInto - Clone the specified DSGraph into the current graph.
	///
	/// The CloneFlags member controls various aspects of the cloning process.
	///
	abstract void cloneInto(DSGraph G, int CloneFlags);

	/// getFunctionArgumentsForCall - Given a function that is currently in this
	/// graph, return the DSNodeHandles that correspond to the pointer-compatible
	/// function arguments.  The vector is filled in with the return value (or
	/// null if it is not pointer compatible), followed by all of the
	/// pointer-compatible arguments.
	abstract void getFunctionArgumentsForCall(Function F,
			Collection<DSNodeHandle> Args);

	/// mergeInGraph - This graph merges in the minimal number of
	/// nodes from G2 into 'this' graph, merging the bindings specified by the
	/// call site (in this graph) with the bindings specified by the vector in G2.
	/// If the StripAlloca's argument is 'StripAllocaBit' then Alloca markers are
	/// removed from nodes.
	///
	abstract void mergeInGraph(DSCallSite CS, Collection<DSNodeHandle> Args,
			DSGraph G2, int CloneFlags);
	
	/// mergeInGraph - This method is the same as the above method, but the
	/// argument bindings are provided by using the formal arguments of F.
	///
	abstract void mergeInGraph(DSCallSite CS, Function F, DSGraph Graph, int CloneFlags);

	/// getCallSiteForArguments - Get the arguments and return value bindings for
	/// the specified function in the current graph.
	///
	abstract DSCallSite getCallSiteForArguments(Function F);

	/// getDSCallSiteForCallSite - Given an LLVM CallSite object that is live in
	/// the context of this graph, return the DSCallSite for it.
	abstract DSCallSite getDSCallSiteForCallSite(DSCallSite CS);

	// Methods for checking to make sure graphs are well formed...
	void AssertNodeInGraph(DSNode N) {
		assert (N == null || N.getParentGraph() == this) :
	           "AssertNodeInGraph: Node is not in graph!";
	}
	
	abstract void AssertNodeContainsGlobal(DSNode N, GlobalValue GV);

	abstract void AssertCallSiteInGraph(DSCallSite CS);
	abstract void AssertCallNodesInGraph();
	abstract void AssertAuxCallNodesInGraph();

	abstract void AssertGraphOK();

	/// removeTriviallyDeadNodes - After the graph has been constructed, this
	/// method removes all unreachable nodes that are created because they got
	/// merged with other nodes in the graph.  This is used as the first step of
	/// removeDeadNodes.
	///
	abstract void removeTriviallyDeadNodes();
	
	/// print - Print a dot graph to the specified ostream...
	///
	public void format(Printer printer) {
		printer
	      .pln("Graph for: " + getFunctionNames())
	      .incr();
		
		for (DSNode Node : Nodes) {
			printer.pln(Node.toString());
			
			printer.incr();
			for(Entry<Long, DSNodeHandle> entry : Node.Links.entrySet()) {
				BigInteger srcID = Node.getID();
				long srcOffset = entry.getKey();
				DSNodeHandle NH = entry.getValue();
				long destOffset = NH.getOffset();
				BigInteger destID = NH.getNode().getID();
				
				printer.indent().pln("(" + srcID + ", " + srcOffset +")"
						+ "--" + "(" + destID + ", " + destOffset + ")");
			}
			printer.decr();
		}
		
		// Add scalar nodes to the graph...
//		for (Entry<Value, DSNodeHandle> entry : ScalarMap.ValueMap.entrySet()) {
//			Value key = entry.getKey();
//			if (!(key instanceof GlobalValue)) {
//				DSNodeHandle NH = entry.getValue();
//				if (!NH.isNull()) {
//					printer.indent().pln(NH.getNode().getID() + ": \t" + key);
//				} else {
//					printer.indent().pln("NIL" + ": \t" + key);
//				}
//			}
//		}
		
		// Add scalar nodes to the graph...
		CPrinter cout = new CPrinter(printer);
		for (Entry<Pair<Node, String>, DSNodeHandle> entry : NodeMap.getNodeMap().entrySet()) {
			Node N = entry.getKey().fst();
			DSNodeHandle NH = entry.getValue();
			printer.indent();
			if (!NH.isNull()) {
				printer.p(NH.getNode().getID() + ": \t");
			} else {
				printer.indent().pln("NIL" + ": \t");
			}
			cout.dispatch(N);
			printer.p(entry.getKey().snd()).pln();
		}
		
		printer.decr();
	}
	
	/// dump - call print(cerr), for use from the debugger...
	///
	public void dump(Printer printer) { format(printer); }
}
