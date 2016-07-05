package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import xtc.tree.Node;

abstract class DSCallGraph {
	// Actual Callees contains CallSite -> set of Function mappings
	private Map<DSCallSite, Set<Function>> ActualCallees = Maps.newHashMap();

	// SimpleCallees contains Function -> set of Functions mappings
	private Map<Function, Set<Function>> SimpleCallees = Maps.newHashMap();

	// These are used for returning empty sets when the caller has no callees
	private Set<Function> EmptyActual = Sets.newHashSet();

	private Set<Function> EmptySimple = Sets.newHashSet();

	// An equivalence class is exactly an SCC
	private EquivalenceClasses<Function> SCCs;

	// Functions we know about that aren't called
	private Set<Function> KnownRoots = Sets.newHashSet();

	// Functions that might be called from an incomplete unresolved call site.
	private Set<Function> IncompleteCalleeSet = Sets.newHashSet();

	private Set<DSCallSite> CompleteCS = Sets.newHashSet();

	DSCallGraph() {
	}

	// Tarjan's SCC algorithm
	abstract int tarjan_rec(Function F, Set<Function> Stack, int NextID,
			Map<Function, Integer> ValMap);

	abstract void removeECFunctions();

	/**
	 * Method: insert()
	 *
	 * Description: Insert a new entry into the call graph. This entry says that
	 * the specified call site calls the specified function.
	 *
	 * Inputs: CS - The call site which calls the specified function. F - The
	 * function which is called. This is permitted to be NULL. It is possible to
	 * have call sites that don't have any targets, and sometimes users just want
	 * to ensure that a call site has an entry within the call graph.
	 */
	abstract void insert(Node CS, Function F);

	abstract void insureEntry(Function F);

	Set<Function> callees(DSCallSite CS) {
		if (!ActualCallees.containsKey(CS))
			return EmptyActual;
		return ActualCallees.get(CS);
	}

	Set<Function> flat_callees(DSCallSite CS) {
		if (!ActualCallees.containsKey(CS))
			return EmptySimple;
		return ActualCallees.get(CS);
	}

	Set<Function> roots() {
		return KnownRoots;
	}

	Function sccsLeader(Function F) {
		return SCCs.getLeaderValue(F);
	}

	int callee_size(DSCallSite CS) {
		if (!ActualCallees.containsKey(CS))
			return 0;
		return ActualCallees.get(CS).size();
	}

	boolean called_from_incomplete_site(Function F) {
		return IncompleteCalleeSet.contains(F);
	}

	void callee_mark_complete(DSCallSite CS) {
		CompleteCS.add(CS);
	}

	boolean callee_is_comlete(DSCallSite CS) {
		return CompleteCS.contains(CS);
	}

	int size() {
		int sum = 0;
		for (Entry<DSCallSite, Set<Function>> Entry : ActualCallees.entrySet()) {
			sum += Entry.getValue().size();
		}
		return sum;
	}

	int flat_size() {
		return SimpleCallees.size();
	}

	abstract void buildSCCs();

	abstract void buildRoots();

	abstract void buildIncompleteCalleeSet(Set<Function> callees);

	abstract void addFullFunctionSet(DSCallSite CS, Set<Function> Set);

	void addFullFunctionList(DSCallSite CS, Collection<Function> List) {
		TreeSet<Function> Set = Sets.newTreeSet();
		addFullFunctionSet(CS, Set);
		List.addAll(Set);
	}

	void assertSCCRoot(Function F) {
		assert F == SCCs.getLeaderValue(F) : "Not Leader?";
	}

	static boolean hasPointers(Function F) {
		throw new UnsupportedOperationException();
	}

	static boolean hasPointers(DSCallSite CS) {
		throw new UnsupportedOperationException();
	}
}
