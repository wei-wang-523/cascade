package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;

/**
 * DSScalarMap - An instance of this class is used to keep track of all of
 * which DSNode each scalar in a function points to. This is specialized to
 * keep track of globals with nodes in the function, and to keep track of the
 * unique DSNodeHandle being used by the scalar map.
 * 
 * This class is crucial to the efficiency of DSA with some large SCC's. In
 * these cases, the cost of iterating over the scalar map dominates the cost
 * of DSA. In all of these cases, the DSA phase is really trying to identify
 * globals or unique node handles active in the function.
 *
 */

class DSScalarMap {
	Map<Value, DSNodeHandle> ValueMap;
	Set<GlobalValue> GlobalSet;
	EquivalenceClasses<GlobalValue> GlobalECs;
	
	DSScalarMap(EquivalenceClasses<GlobalValue> ECs) {
		GlobalECs = new EquivalenceClasses<GlobalValue>(ECs);
		ValueMap = Maps.newHashMap();
		GlobalSet = Sets.newTreeSet();
	}

	EquivalenceClasses<GlobalValue> getGlobalECs() {
		return GlobalECs;
	}
	
	GlobalValue getLeaderForGlobal(GlobalValue GV) {
		EquivalenceClasses<GlobalValue>.ECValue EC = GlobalECs.findValue(GV);
		if(EC == null) return GV;
		return EC.getData();
	}
	
	Map<Value, DSNodeHandle> getValueMap() { return ValueMap; }

	DSNodeHandle find(Value V) {
		Preconditions.checkNotNull(V);
		if (ValueMap.containsKey(V)) return ValueMap.get(V);
		// If this is a global, check to see if it is equivalenced to something
		// in the map.
		
		if(V instanceof GlobalValue) {
			GlobalValue GV = (GlobalValue) V;
			GlobalValue Leader = getLeaderForGlobal(GV);
			if(Leader != GV) {
				return ValueMap.get((Value) Leader);
			}
		}
		
		return null;
	}
	
	/** getRawEntryRef - This method can be used by clients that are aware of the
	 * global value equivalence class in effect.
	 */
	DSNodeHandle getRawEntryRef(Value V) {
		if(ValueMap.containsKey(V)) return ValueMap.get(V);
		
		DSNodeHandle NH = new DSNodeHandle();
		ValueMap.put(V, NH);
		if(V instanceof GlobalValue) {
			GlobalSet.add((GlobalValue) V);
		}
		return NH;
	}
	
	boolean contains(Value V) {
		return ValueMap.containsKey(V);
	}

	void erase(Value V) {
		DSNodeHandle NH = find(V);
		if(NH == null) return;
		if(V instanceof GlobalValue) {
			GlobalValue GV = (GlobalValue) V;
			GlobalSet.remove(GV);
		}
		ValueMap.remove(V);
	}
	
	/// replaceScalar - When an instruction needs to be modified, this method can
	/// be used to update the scalar map to remove the old and insert the new.
	void replaceScalar(Value Old, Value New) {
		DSNodeHandle NH = find(Old);
		assert NH != null : "Old value is not in the map";
		
		ValueMap.put(New, ValueMap.get(Old));
		erase(Old);
	}
	
	/// copyScalarIfExists - If Old exists in the scalar map, make New point to 
	/// whatever Old did.
	void copyScalarIfExsits(Value Old, Value New) {
		if(find(Old) == null) return;
		ValueMap.put(New, ValueMap.get(Old));
	}
	
	/// get - Return the DSNodeHandle for the specified value, creating a
	/// new null handle if there is no entry yet.
	DSNodeHandle get(Value V) {
		Preconditions.checkNotNull(V);
		if(ValueMap.containsKey(V)) {
			// Return value if already exists.
			return ValueMap.get(V);
		}
		
		if (V instanceof GlobalValue) {
			return AddGlobal((GlobalValue) V);
		}
		
		DSNodeHandle NH = new DSNodeHandle();
		ValueMap.put(V, NH);
		return NH;
	}
	
	void clear_scalars() {
		throw new UnsupportedOperationException();
	}
	
	void clear() {
		ValueMap.clear();
		GlobalSet.clear();
	}
	
	void spliceFrom(DSScalarMap RHS) {
		GlobalSet.addAll(RHS.GlobalSet); 
		RHS.GlobalSet.clear();
		
		// Special case if this is empty.
		if (ValueMap.isEmpty()) {
		    ValueMap.putAll(RHS.ValueMap);
		} else {
			for (Entry<Value, DSNodeHandle> entry : RHS.ValueMap.entrySet()) {
				Value V = entry.getKey();
				DSNodeHandle NH = ValueMap.containsKey(V) ? ValueMap.get(V) : new DSNodeHandle();
				ValueMap.put(V, NH);
				NH.mergeWith(entry.getValue());
			}
		}
		
		RHS.ValueMap.clear();
	}
	
	Set<GlobalValue> getGlobalSet() {
		return GlobalSet;
	}
	
	private DSNodeHandle AddGlobal(GlobalValue GV) {
		Preconditions.checkNotNull(GV);
		Preconditions.checkArgument(!ValueMap.containsKey(GV)); // "GV already exists!"
		
		// If the node doesn't exist, check to see if it's a global that is
		// equated to another global in the program.
		EquivalenceClasses<GlobalValue>.ECValue ECV = GlobalECs.findValue(GV);
		if (ECV != null) {
			GlobalValue Leader = GlobalECs.findLeader(GV).getData();
			if (!Leader.equals(GV)) {
				GV = Leader;
				DSNodeHandle NH = ValueMap.get(GV);
				if (NH != null) return NH;
			}
		}

		// Okay, this is either not an equivalenced global or it is the leader, it
		// will be inserted into the scalar map now.
		GlobalSet.add(GV);

		DSNodeHandle NH = new DSNodeHandle();
		ValueMap.put(GV, NH);
		return NH;
	}

	void put(Value GV, DSNodeHandle NH) {
		ValueMap.put(GV, NH);
		if(GV instanceof GlobalValue) {
			GlobalSet.add((GlobalValue) GV);
		}
	}
}
