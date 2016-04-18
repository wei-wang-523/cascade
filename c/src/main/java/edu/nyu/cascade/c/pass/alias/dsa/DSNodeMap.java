package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Map;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.util.Pair;
import xtc.tree.Node;

/**
 * Regions track the DSNodeHandle of nodes.
 * 
 * @author Wei
 *
 */

class DSNodeMap {
	Map<Pair<Node, String>, DSNodeHandle> NodeMap = Maps.newHashMap();
	
	Map<Pair<Node, String>, DSNodeHandle> getNodeMap() { return NodeMap; }
	
	DSNodeHandle get(Node N) {
		Pair<Node, String> NKey = getKey(N);
		assert NodeMap.containsKey(NKey) : "No key is stored: " + NKey;
		return NodeMap.get(NKey);
	}
	
	/**
	 * getRawEntryRef - This method can be used by clients that are aware of the
	 * global value equivalence class in effect.
	 */
	DSNodeHandle getRawEntryRef(Node N) {
		Pair<Node, String> NKey = getKey(N);
		
		if(NodeMap.containsKey(NKey)) return NodeMap.get(NKey);
		
		DSNodeHandle NH = new DSNodeHandle();
		NodeMap.put(NKey, NH);
		return NH;
	}

	void put(Node N, DSNodeHandle NH) {
		Preconditions.checkNotNull(NH);
		Preconditions.checkArgument(!NodeMap.containsKey(getKey(N)));
		NodeMap.put(getKey(N), NH);
	}

	boolean contains(Node node) {
		return NodeMap.containsKey(getKey(node));
	}
	
	Pair<Node, String> getKey(Node N) {
		return Pair.of(N, CType.getScopeName(N));
	}

	void clear() {
		NodeMap.clear();
	}

	void spliceFrom(DSNodeMap RHS) {
		NodeMap.putAll(RHS.NodeMap);
		RHS.NodeMap.clear();
	}
}
