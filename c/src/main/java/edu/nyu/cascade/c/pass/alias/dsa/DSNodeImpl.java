package edu.nyu.cascade.c.pass.alias.dsa;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.alias.dsa.EquivalenceClasses.ECValue;
import edu.nyu.cascade.util.IOUtils;
import xtc.type.StructOrUnionT;
import xtc.type.Type;
import xtc.type.VariableT;

final class DSNodeImpl extends DSNode {
	private static BigInteger nextId = BigInteger.ZERO;

	static void reset() {
		nextId = BigInteger.ZERO;
	}

	/// ID - For dumping
	private final BigInteger ID;

	DSNodeImpl(DSGraph G) {
		ID = nextId;
		nextId = nextId.add(BigInteger.ONE);
		NumReferrers = 0;
		Size = 0;
		ParentGraph = G;
		NodeType = 0;
		if (G != null)
			G.addNode(this);
	}

	DSNodeImpl(DSNode N, DSGraph G, boolean NullLinks) {
		ID = nextId;
		nextId = nextId.add(BigInteger.ONE);
		NumReferrers = 0;
		Size = N.Size;
		ParentGraph = G;
		TyMap = Maps.newHashMap(N.TyMap);
		Globals = Sets.newTreeSet(N.Globals);
		NodeType = N.NodeType;
		if (!NullLinks)
			Links = N.Links;
		G.addNode(this);
	}

	@Override
	void growSizeForType(Type NewTy, long Offset) {
		if (NewTy == null || NewTy.isVoid())
			return;
		if (isCollapsedNode())
			return;
		if (isArrayNode() && getSize() > 0) {
			Offset %= getSize();
		}
		long NewTySize = CType.getInstance().getSize(NewTy);
		if (Offset + NewTySize >= getSize()) {
			growSize(Offset + NewTySize);
		}
	}

	@Override
	void mergeTypeInfo(Type NewTy, long Offset) {
		if (NewTy == null || NewTy.isVoid())
			return;
		if (isCollapsedNode())
			return;

		growSizeForType(NewTy, Offset);

		// In such cases, merge type information for each struct field
		// individually(at the appropriate offset), instead of the
		// struct type.
		if (NewTy.isStruct() || NewTy.isUnion()) {
			StructOrUnionT STy = NewTy.toStructOrUnion();
			for (VariableT member : STy.getMembers()) {
				long FieldOffset = CType.getInstance().getOffset(STy, member.getName());
				mergeTypeInfo(member, Offset + FieldOffset);
			}
		} else {
			Set<Type> NewTySet = Sets.newHashSet();
			if (TyMap.containsKey(Offset)) {
				NewTySet.addAll(TyMap.get(Offset));
			}
			NewTySet.add(NewTy.resolve());

			SuperSet<Type> TySS = getParentGraph().getTypeSS();
			TyMap.put(Offset, TySS.addSet(NewTySet));
		}

		assert (TyMap.containsKey(Offset));
	}

	@Override
	void mergeTypeInfo(DSNode DN, long Offset) {
		if (isCollapsedNode())
			return;

		for (Entry<Long, Set<Type>> entry : DN.TyMap.entrySet()) {
			mergeTypeInfo(entry.getValue(), entry.getKey() + Offset);
		}
	}

	private void mergeTypeInfo(Set<Type> TySet, long Offset) {
		if (isCollapsedNode())
			return;
		if (isArrayNode())
			Offset %= getSize();

		if (!TyMap.containsKey(Offset)) {
			TyMap.put(Offset, TySet);
			for (Type Ty : TyMap.get(Offset)) {
				long TySize = CType.getInstance().getSize(Ty);
				if (Offset + TySize >= getSize()) {
					growSize(Offset + TySize);
				}
			}
		} else {
			Set<Type> NewTySet = Sets.newHashSet();

			NewTySet.addAll(TyMap.get(Offset));
			NewTySet.addAll(TySet);

			SuperSet<Type> TySS = getParentGraph().getTypeSS();
			TyMap.put(Offset, TySS.addSet(NewTySet));
		}
	}

	@Override
	void markIntPtrFlags() {
		// TODO Auto-generated method stub

	}

	@Override
	void foldNodeCompletely() {
		if (isNodeCompletelyFolded())
			return; // If this node is already folded...

		IOUtils.err().println("Folding is happening");

		// Collapsed nodes don't really need a type
		// Clear the array flag too. Node should be of type VOID
		TyMap.clear();
		maskNodeTypes(~DSSupport.NodeTy.ArrayNode.value());

		// If this node has a size that is <= 1, we don't need to create a
		// forwarding
		// node.
		if (getSize() <= 1) {
			setCollapsedMarker();
			Size = 1;
			assert Links.size() <= 1 : "Size is 1, but has more links?";
		} else {
			// Create the node we are going to forward to. This is required because
			// some referrers may have an offset that is > 0. By forcing them to
			// forward, the forwarder has the opportunity to correct the offset.
			DSNode DestNode = new DSNodeImpl(ParentGraph);
			DestNode.NodeType = NodeType;
			DestNode.setCollapsedMarker();
			DestNode.Size = 1;
			DestNode.Globals.addAll(Globals);
			Globals.clear();

			// Start forwarding to the destination node...
			forwardNode(DestNode, 0);
		}
	}

	@Override
	void addEdgeTo(long Offset, DSNodeHandle NH) {
		if (NH.isNull())
			return;

		if (isNodeCompletelyFolded())
			Offset = 0;

		DSNodeHandle ExistingEdge = getLink(Offset);
		if (!ExistingEdge.isNull()) {
			// Merge the two nodes...
			ExistingEdge.mergeWith(NH);
		} else { // No merging to perform...
			setLink(Offset, NH); // Just force a link in there...
		}
	}

	@Override
	void mergeWith(DSNodeHandle NH, long Offset) {
		DSNode N = NH.getNode();
		if (N == this && NH.getOffset() == Offset)
			return; // Noop

		// If the RHS is a null node, make it point to this node!
		if (N == null) {
			NH.mergeWith(new DSNodeHandle(this, Offset));
			return;
		}

		assert (!N.isDeadNode() && !isDeadNode());
		assert !hasNoReferrers() : "Should not try to fold a useless node!";

		if (N == this) {
			// We cannot merge two pieces of the same node together, collapse the node
			// completely.
			foldNodeCompletely();
			return;
		}

		// If both nodes are not at offset 0, make sure that we are merging the node
		// at an later offset into the node with the zero offset.
		//
		if (Offset < NH.getOffset()) {
			N.mergeWith(new DSNodeHandle(this, Offset), NH.getOffset());
			return;
		} else if (Offset == NH.getOffset() && getSize() < N.getSize()) {
			// If the offsets are the same, merge the smaller node into the bigger
			// node
			N.mergeWith(new DSNodeHandle(this, Offset), NH.getOffset());
			return;
		}

		// Ok, now we can merge the two nodes. Use a static helper that works with
		// two node handles, since "this" may get merged away at intermediate steps.
		DSNodeHandle CurNodeH = new DSNodeHandle(this, Offset);
		DSNodeHandle NHCopy = new DSNodeHandle(NH);
		if (CurNodeH.getOffset() >= NHCopy.getOffset())
			DSSupport.MergeNodes(CurNodeH, NHCopy);
		else
			DSSupport.MergeNodes(NHCopy, CurNodeH);
	}

	@Override
	void addGlobal(GlobalValue GV) {
		// First, check to make sure this is the leader if the global is in an
		// equivalence class.
		GV = getParentGraph().getScalarMap().getLeaderForGlobal(GV);
		Globals.add(GV);
		setGlobalMarker();
	}

	@Override
	void removeGlobal(GlobalValue GV) {
		Preconditions.checkArgument(Globals.contains(GV));
		Globals.remove(GV);
	}

	@Override
	void addFullGlobalsList(Collection<GlobalValue> List) {
		Set<GlobalValue> Set = Sets.newTreeSet();
		addFullGlobalsSet(Set);
		List.addAll(Set);
	}

	@Override
	void addFullGlobalsSet(Set<GlobalValue> Set) {
		// TODO Auto-generated method stub

	}

	@Override
	void addFullFunctionSet(Set<Function> Set) {
		if (Globals.isEmpty())
			return;

		EquivalenceClasses<GlobalValue> EC = getParentGraph().getGlobalECs();

		for (GlobalValue GV : Globals) {
			if (EC.findValue(GV) == null) {
				if (GV instanceof Function)
					Set.add((Function) GV);
			} else {
				ECValue EV = EC.findValue(GV);
				while (EV != null) {
					GlobalValue EVGV = (GlobalValue) EV.getData();
					if (EVGV instanceof Function) {
						Set.add((Function) EVGV);
					}
					EV = EV.getNext();
				}
			}
		}
	}

	@Override
	void addValueList(Collection<Value> List) {
		DSScalarMap SM = getParentGraph().getScalarMap();
		for (Entry<Value, DSNodeHandle> entry : SM.ValueMap.entrySet()) {
			DSNodeHandle NH = SM.get(entry.getKey());
			if (NH.getNode() == this) {
				// entry.getKey().>dump();
			}
		}
	}

	@Override
	void forwardNode(DSNode To, long Offset) {
		// Cannot forward a node to itself!
		Preconditions.checkArgument(this != To);
		// Already forwarding from this node!
		Preconditions.checkArgument(ForwardNH.isNull());
		if (To.Size <= 1)
			Offset = 0;
		assert (Offset < To.Size || (Offset == To.Size
				&& Offset == 0)) : "Forwarded offset is wrong!";
		ForwardNH.setTo(To, Offset);
		NodeType = DSSupport.NodeTy.DeadNode.value();
		Size = 0;

		DSNodeHandle ToNH = new DSNodeHandle(To, Offset);

		// Move the Links
		for (Entry<Long, DSNodeHandle> entry : Links.entrySet()) {
			DSNodeHandle entryNH = entry.getValue();
			if (!entryNH.isNull()) {
				// Compute the offset into the current node at which to
				// merge this link. In the common case, this is a linear
				// relation to the offset in the original node (with
				// wrapping), but if the current node gets collapsed due to
				// recursive merging, we must make sure to merge in all remaining
				// links at offset zero.
				long MergeOffset = 0;
				if (ToNH.getNode().getSize() != 1)
					MergeOffset = (entry.getKey() + Offset) % ToNH.getNode().getSize();
				ToNH.getNode().addEdgeTo(MergeOffset, entryNH);
			}
		}
		Links.clear();

		// Remove this node from the parent graph's Nodes list.
		ParentGraph.unlinkNode(this);
		ParentGraph = null;
	}

	@Override
	void cleanEdges() {
		// TODO Auto-generated method stub

	}

	@Override
	void dump() {
		// TODO Auto-generated method stub

	}

	@Override
	void dumpParentGraph() {
		// TODO Auto-generated method stub

	}

	@Override
	void dumpFuncs() {
		// TODO Auto-generated method stub

	}

	@Override
	void assertOK() {
		// TODO Auto-generated method stub

	}

	@Override
	void remapLinks(Map<DSNode, DSNodeHandle> OldNodeMap) {
		for (Entry<Long, DSNodeHandle> entry : Links.entrySet()) {
			DSNodeHandle NH = entry.getValue();
			DSNode N = NH.getNode();
			if (N != null) {
				if (OldNodeMap.containsKey(N)) {
					DSNodeHandle ONMI = OldNodeMap.get(N);
					DSNode ONMIN = ONMI.getNode();
					NH.setTo(ONMIN, NH.getOffset() + ONMI.getOffset());
				}
			}
		}
	}

	@Override
	void markReachableNodes(Set<DSNode> ReachableNodes) {
		// TODO Auto-generated method stub

	}

	@Override
	void checkOffsetFoldIfNeeded(long Offset) {
		if (!isNodeCompletelyFolded() && (Size != 0 || Offset != 0)
				&& !isForwarding()) {
			if (Offset >= Size || Offset < 0) {
				// Accessing offsets out of node size range
				// This is seen in the "magic" struct in named (from bind), where the
				// fourth field is an array of length 0, presumably used to create
				// struct
				// instances of different sizes
				// More generally this happens whenever code indexes past the end
				// of a struct type. We don't model this, so fold!

				// Collapse the node since its size is now variable
				foldNodeCompletely();
			}
		}
	}

	@Override
	DSNode copy(DSNode other, DSGraph G, boolean NullLinks) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int compareTo(DSNode o) {
		return ID.compareTo(o.getID());
	}

	@Override
	BigInteger getID() {
		return ID;
	}

	@Override
	public String toString() {
		StringBuilder OS = new StringBuilder().append(ID);

		DSGraph G = getParentGraph();

		if (NodeType != 0) {
			OS.append(": ");
			if ((NodeType & DSSupport.NodeTy.AllocaNode.value()) != 0)
				OS.append("S");
			if ((NodeType & DSSupport.NodeTy.HeapNode.value()) != 0)
				OS.append("H");
			if ((NodeType & DSSupport.NodeTy.GlobalNode.value()) != 0)
				OS.append("G");
			if ((NodeType & DSSupport.NodeTy.UnknownNode.value()) != 0)
				OS.append("U");
			if ((NodeType & DSSupport.NodeTy.IncompleteNode.value()) != 0)
				OS.append("I");
			if ((NodeType & DSSupport.NodeTy.ModifiedNode.value()) != 0)
				OS.append("M");
			if ((NodeType & DSSupport.NodeTy.ReadNode.value()) != 0)
				OS.append("R");
			if ((NodeType & DSSupport.NodeTy.ExternalNode.value()) != 0)
				OS.append("E");
			if ((NodeType & DSSupport.NodeTy.ExternFuncNode.value()) != 0)
				OS.append("X");
			if ((NodeType & DSSupport.NodeTy.IntToPtrNode.value()) != 0)
				OS.append("P");
			if ((NodeType & DSSupport.NodeTy.PtrToIntNode.value()) != 0)
				OS.append("2");
			if ((NodeType & DSSupport.NodeTy.VAStartNode.value()) != 0)
				OS.append("V");
			if ((NodeType & DSSupport.NodeTy.DeadNode.value()) != 0)
				OS.append("<dead>");
		}

		if (isNodeCompletelyFolded()) {
			OS.append("COLLAPSED");
		} else {
			if (isArrayNode()) {
				OS.append(" array");
			}

			for (Entry<Long, Set<Type>> Entry : TyMap.entrySet()) {
				OS.append('\n').append("    ").append(Entry.getKey() + ": ");
				if (Entry.getValue() != null) {
					for (Type Ty : Entry.getValue()) {
						OS.append(Ty).append(", ");
					}
					int length = OS.length();
					OS.delete(length - 2, length);
				} else {
					OS.append("VOID");
				}
			}

			OS.append('\n');
		}

		// Indicate if this is a VANode for some function
		for (Entry<Function, DSNodeHandle> Entry : G.getVANodes().entrySet()) {
			DSNodeHandle VANode = Entry.getValue();
			if (this == VANode.getNode()) {
				OS.append("(VANode for ").append(Entry.getKey().getName()).append(
						")\n");
			}
		}

		// EquivalenceClasses<GlobalValue> GlobalECs = null;
		// if (G != null) GlobalECs = G.getGlobalECs();
		//
		// for (GlobalValue GV : Globals) {
		// GN.printAsOperand(OS,false,M);
		//
		// // Figure out how many globals are equivalent to this one.
		// if (GlobalECs != null) {
		// GlobalValue Value = GlobalECs.findValue(GV);
		// if (Value != null) {
		// int NumMembers =
		// std::distance(GlobalECs->member_begin(I), GlobalECs->member_end());
		// if (NumMembers != 1) OS.append(" + ".append((NumMembers-1).append(" EC");
		// }
		// }
		// OS.append("\n");
		// }

		return OS.toString();
	}

}
