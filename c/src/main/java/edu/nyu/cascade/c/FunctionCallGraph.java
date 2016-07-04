package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;

class FunctionCallGraph {

	private Table<String, String, Integer> funcCallStats;
	private Multimap<String, String> incomingEdges;

	FunctionCallGraph() {
		funcCallStats = HashBasedTable.create();
		incomingEdges = HashMultimap.create();
	}

	void addCallEdge(String caller, String callee) {
		if (incomingEdges.containsEntry(callee, caller)) {
			int val = funcCallStats.get(caller, callee);
			funcCallStats.put(caller, callee, val + 1);
		} else {
			funcCallStats.put(caller, callee, 1);
			incomingEdges.put(callee, caller);
		}
	}

	Collection<String> getCallers(String callee) {
		return ImmutableSet.copyOf(incomingEdges.get(callee));
	}

	int getCallingTimes(String caller, String callee) {
		Preconditions.checkArgument(funcCallStats.contains(caller, callee));
		return funcCallStats.get(caller, callee);
	}

	Collection<String> getAllCallees(String funcName) {
		Collection<String> calleeCfgs = Sets.newHashSet();
		List<String> worklist = Lists.newArrayList(funcName);
		while (!worklist.isEmpty()) {
			String currFunc = worklist.remove(0);
			if (calleeCfgs.contains(currFunc))
				continue;
			calleeCfgs.add(currFunc);
			worklist.addAll(funcCallStats.row(currFunc).keySet());
		}
		return calleeCfgs;
	}

	void removeCallerEdge(String caller, String callee) {
		Preconditions.checkArgument(incomingEdges.containsEntry(callee, caller));
		Preconditions.checkArgument(funcCallStats.contains(caller, callee));
		incomingEdges.remove(callee, caller);
		funcCallStats.remove(caller, callee);
	}

	/**
	 * Retain the call edges between funcNames
	 * 
	 * @param funcNames
	 */
	void retainFunctions(Collection<String> funcNames) {
		for (Iterator<Entry<String, String>> it = incomingEdges.entries()
		    .iterator(); it.hasNext();) {
			Entry<String, String> entry = it.next();
			String callee = entry.getKey(), caller = entry.getValue();
			if (!(funcNames.contains(callee) && funcNames.contains(caller))) {
				it.remove();
				funcCallStats.remove(caller, callee);
			}
		}
	}
}
