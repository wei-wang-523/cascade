package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Map;
import java.util.Map.Entry;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

class EquivalenceClasses<ElemTy> {
	
	/** ECValue - The EquivalenceClasses data structure is just a set of these.
	 * Each of these represents a relation for a value.  First it stores the
	 * value itself, which provides the ordering that the set queries.  Next, it
	 * provides a "next pointer", which is used to enumerate all of the elements
	 * in the unioned set.  Finally, it defines either a "end of list pointer" or
	 * "leader pointer" depending on whether the value itself is a leader.  A
	 * "leader pointer" points to the node that is the leader for this element,
	 * if the node is not a leader.  A "end of list pointer" points to the last
	 * node in the list of members of this list.  Whether or not a node is a
	 * leader is determined by a bit stolen from one of the pointers.
	 */
	class ECValue {
		private boolean IsLeader;
		// Leader - if it is leader, then Leader is the "end of list pointer"; otherwise,
		// if it is non-leader, Leader is the leader.
		private ECValue Leader, Next;
		private ElemTy Data;
		
		// ECValue ctor - Start out with EndOfList pointing to this node, Next is
		// Null, isLeader = true.
		ECValue(ElemTy Elt) {
			Data = Elt;
			Leader = this;
			IsLeader = true;
		}
		
		ECValue(ECValue RHS) {
			// Only support copying of singleton nodes.
			Preconditions.checkArgument(RHS.isLeader() && RHS.getNext() == null);
			Leader = this;
			Next = RHS.getNext();
			Data = RHS.Data;
			IsLeader = RHS.isLeader();			
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object Obj) {
			if (this == Obj) return true;
			if (Obj == null) return false;
			if(!(Obj.getClass() == getClass())) return false;
			ECValue Other = (ECValue) Obj;
			return Other.Data.equals(this.Data);
		}
		
		@Override
		public int hashCode() {
			return Data.hashCode();
		}
		
		ECValue getNext() { return Next; }
		
		boolean isLeader() { return IsLeader; }
		
		ElemTy getData() { return Data; }
		
		ECValue getLeader() {
			if (isLeader()) return this;
			if (Leader.isLeader()) return Leader;
			// Path compression.
			return Leader = Leader.getLeader();
		}
		
		ECValue getEndOfList() {
			Preconditions.checkArgument(isLeader()); // Cannot get the end of a list for a non-leader!
			return Leader;
		}
		
		void setNext(ECValue NewNext) {
			Preconditions.checkArgument(getNext() == null); // Already has a next pointer!
			Next = NewNext;
		}
	};
	
	// TheMapping - This implicitly provides a mapping from ElemTy values to the
	// ECValues, it just keeps the key as part of the value.
	Map<ElemTy, ECValue> TheMapping = Maps.newHashMap();
	
	EquivalenceClasses() {}
	
	EquivalenceClasses(EquivalenceClasses<ElemTy> RHS) {
		TheMapping.clear();
		for(Entry<ElemTy, ECValue> I : RHS.TheMapping.entrySet()) {
			if(I.getValue().isLeader()) {
				ECValue Elem = I.getValue();
				ECValue Leader = insert(Elem.getData());
				
				while(Elem.getNext() != null) {
					ECValue NextElem = Elem.getNext();
					ECValue NextElemCopy = insert(NextElem.getData());
					unionSets(Leader, NextElemCopy);
					Elem = NextElem;
				}
			}
		}
	}
	
	boolean isEmpty() {	return TheMapping.isEmpty(); }
	
	/** getLeaderValue - Return the leader for the specified value that is in the
	 * set.  It is an error to call this method for a value that is not yet in
	 * the set.  For that, call getOrInsertLeaderValue(V).
	 */
	ElemTy getLeaderValue(final ElemTy Data) {
		ECValue Value = findLeader(Data);
		assert Value != null : "Value is not in the set!";
		return Value.Data;
	}
	
	/** getOrInsertLeaderValue - Return the leader for the specified value that is
	 * in the set.  If the member is not in the set, it is inserted, then
	 * returned.
	 */
	ElemTy getOrInsertLeaderValue(final ElemTy Data) {
		ECValue Value = findLeader(insert(Data));
		assert Value != null : "Value is not in the set!";
		return Value.getLeader().getData();
	}

	/** getNumClasses - Return the number of equivalence classes in this set.
	 * Note that this is a linear time operation.
	 */
	int getNumClasses() {
		int NC = 0;
		for(ECValue Elem : TheMapping.values()) {
			if(Elem.isLeader()) ++NC;
		}
		return NC;
	}

	/** insert - Insert a new value into the union/find set, ignoring the request
	 * if the value already exists.
	 */
	ECValue insert(final ElemTy Data) {
		if(TheMapping.containsKey(Data)) {
			return TheMapping.get(Data);
		}
		ECValue Value = new ECValue(Data);
		TheMapping.put(Data, Value);
		return Value;
	}

	/** findLeader - Given a value in the set, return a member iterator for the
	 * equivalence class it is in.  This does the path-compression part that
	 * makes union-find "union findy".  This returns null if the value
	 * is not in the equivalence class.
	 */
	ECValue findLeader(ElemTy Data) {
		ECValue Value = TheMapping.get(Data);
		return findLeader(Value);
	}

	ECValue findLeader(ECValue V) {
		if(V == null) return null;
		return V.getLeader();
	}

	/** union - Merge the two equivalence sets for the specified values, inserting
	 * them if they do not already exist in the equivalence set.
	 */
	ECValue unionSets(final ElemTy V1, final ElemTy V2) {
		ECValue L1 = insert(V1), L2 = insert(V2);
		return unionSets(findLeader(L1), findLeader(L2));
	}

	ECValue unionSets(ECValue L1, ECValue L2) {
		Preconditions.checkNotNull(L1);
		Preconditions.checkNotNull(L2);
		
		if (L1 == L2) return L1; // Unifying the same two sets, noop.
		
		// Otherwise, this is a real union operation.  Set the end of the L1 list to
		// point to the L2 leader node.
		L1.getEndOfList().setNext(L2);
		
		// Update L1's end of list pointer (L1 is leader).
		L1.Leader = L2.getEndOfList();
		
		// Clear L2's leader flag.
		L2.IsLeader = false;
		
		// L2's leader is now L1.
		L2.Leader = L1;
		
		return L1;
	}

	/** findValue - Return an iterator to the specified value.  If it does not
	 * exist, null is returned.
	 */
	ECValue findValue(ElemTy Data) {
		return TheMapping.get(Data);
	}
}
