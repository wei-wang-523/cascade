package edu.nyu.cascade.c.pass.alias.dsa;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.alias.dsa.DSSupport.NodeTy;
import xtc.type.Type;

/***
 * DSNode - Node definition for data-structure graphs ------*- Java -*
 * 
 * This file was developed by the LLVM research group and is distributed under
 * the University of Illinois Open Source License. See LICENSE.TXT for details.
 * 
 * Data structure graph nodes and some implementation of DSNodeHandle.
 *
 */

abstract class DSNode implements Comparable<DSNode> {

	/**
	 * NumReferrers - The number of DSNodeHandles pointing to this node... if this
	 * is a forwarding node, then this is the number of node handles which are
	 * still forwarding over us.
	 */
	long NumReferrers;

	/**
	 * ForwardNH - This NodeHandle contain the node (and offset into the node)
	 * that this node really is. When nodes get folded together, the node to be
	 * eliminated has these fields filled in, otherwise ForwardNH.getNode() is
	 * null.
	 */
	DSNodeHandle ForwardNH = new DSNodeHandle();

	/**
	 * Size - The current size of the node. This should be equal to the size of
	 * the current type record.
	 */
	long Size;

	/** ParentGraph - The graph this node is currently embedded into. */
	DSGraph ParentGraph;

	/**
	 * TyMap - Keep track of the loadable types and offsets those types are seen
	 * at.
	 */
	Map<Long, Set<Type>> TyMap = Maps.newTreeMap();

	/** Links - Contains one entry for every byte in this memory object. */
	Map<Long, DSNodeHandle> Links = Maps.newTreeMap();

	/** Globals - The list of globals */
	protected SortedSet<GlobalValue> Globals = Sets.newTreeSet();

	short NodeType;

	/**
	 * DSNode "copy ctor" - Copy the specified node, inserting it into the
	 * specified graph. If NullLinks is true, then null out all of the links, but
	 * keep the same number of them. This can be used for efficiency if the links
	 * are just going to be clobbered anyway.
	 */
	abstract DSNode copy(DSNode other, DSGraph G, boolean NullLinks);

	/** getSize - Return the maximum number of bytes occupied by this object... */
	long getSize() {
		return Size;
	}

	/**
	 * getNumReferrers - This method returns the number of referrers to the
	 * current node. Note that if this node is a forwarding node, this will return
	 * the number of nodes forwarding over the node!
	 */
	long getNumReferrers() {
		return NumReferrers;
	}

	/**
	 * hasNoReferrers - Return true if nothing is pointing to this node at all.
	 */
	boolean hasNoReferrers() {
		return getNumReferrers() == 0;
	}

	DSGraph getParentGraph() {
		return ParentGraph;
	}

	void setParentGraph(DSGraph G) {
		ParentGraph = G;
	}

	/**
	 * getForwardNode - This method returns the node that this node is forwarded
	 * to, if any.
	 */
	DSNode getForwardNode() {
		return ForwardNH.getNode();
	}

	/** isForwarding - Return true if this node is forwarding to another. */
	boolean isForwarding() {
		return !ForwardNH.isNull();
	}

	/**
	 * stopForwarding - When the last reference to this forwarding node has been
	 * dropped, delete the node.
	 */
	void stopForwarding() {
		Preconditions.checkArgument(isForwarding());
		ForwardNH.setTo(null, 0);
		assert (ParentGraph == null);
	}

	void growSize(long NSize) {
		Preconditions.checkArgument(NSize >= Size); // Cannot shrink
		Preconditions.checkArgument(!isCollapsedNode()); // Growing a collapsed node
		Size = NSize;
	}

	/**
	 * growSizeForType - This method increases the size of the node to accommodate
	 * NewTy at the given offset. This is useful for updating the size of a
	 * DSNode, without actually inferring a Type.
	 */
	abstract void growSizeForType(Type NewTy, long Offset);

	/** hasLink - Return true if this memory object has a link in slot LinkNo */
	boolean hasLink(long Offset) {
		Preconditions.checkArgument(Offset < getSize()); // Link index is out of
																											// range!
		return Links.containsKey(Offset);
	}

	/** getLink - Return the link at the specified offset. */
	DSNodeHandle getLink(long Offset) {
		Preconditions.checkArgument(Offset < getSize()); // Link index is out of
																											// range!
		Preconditions.checkArgument(!isForwarding()); // Link on a forwarding node.

		if (Links.containsKey(Offset))
			return Links.get(Offset);

		DSNodeHandle NH = new DSNodeHandle();
		Links.put(Offset, NH);
		return NH;
	}

	/**
	 * mergeTypeInfo - This method merges the specified type into the current node
	 * at the specified offset. This may update the current node's type record if
	 * this gives more information to the node, it may do nothing to the node if
	 * this information is already known, or it may merge the node completely (and
	 * return true) if the information is incompatible with what is already known.
	 */
	abstract void mergeTypeInfo(Type Ty, long Offset);

	abstract void mergeTypeInfo(DSNode D, long Offset);

	/** Types records might exist without types in them */
	boolean hasNoType() {
		if (TyMap.isEmpty())
			return true;
		for (Set<Type> types : TyMap.values()) {
			if (!types.isEmpty())
				return false;
		}
		return true;
	}

	/**
	 * markIntPtrFlags - If the node at any offset has overlapping int/ptr types
	 * mark the P2I flags.
	 */
	abstract void markIntPtrFlags();

	/**
	 * foldNodeCompletely - If we determine that this node has some funny behavior
	 * happening to it that we cannot represent, we fold it down to a single,
	 * completely pessimistic, node. This node is represented as a single byte
	 * with a single TypeEntry of "void" with isArray = true.
	 */
	abstract void foldNodeCompletely();

	/**
	 * isNodeCompletelyFolded - Return true if this node has been completely
	 * folded down to something that can never be expanded, effectively losing all
	 * of the field sensitivity that may be present in the node.
	 */
	boolean isNodeCompletelyFolded() {
		return isCollapsedNode();
	}

	/**
	 * setLink - Set the link at the specified offset to the specified NodeHandle,
	 * replacing what was there. It is uncommon to use this method, instead one of
	 * the higher level methods should be used, below.
	 */
	void setLink(long Offset, DSNodeHandle NH) {
		Preconditions.checkArgument(Offset < getSize()); // Link index is out of
																											// range!
		Links.put(Offset, NH);
	}

	/**
	 * addEdgeTo - Add an edge from the current node to the specified node. This
	 * can cause merging of nodes in the graph.
	 */
	abstract void addEdgeTo(long Offset, DSNodeHandle NH);

	/**
	 * mergeWith - Merge this node and the specified node, moving all links to and
	 * from the argument node into the current node, deleting the node argument.
	 * Offset indicates what offset the specified node is to be merged into the
	 * current node.
	 * 
	 * The specified node may be a null pointer (in which case, nothing happens).
	 */
	abstract void mergeWith(DSNodeHandle NH, long Offset);

	/**
	 * addGlobal - Add an entry for a global value to the Globals list. This also
	 * marks the node with the 'G' flag if it does not already have it.
	 */
	abstract void addGlobal(GlobalValue GV);

	void addFunction(Function F) {
		addGlobal(F);
	}

	/**
	 * removeGlobal - Remove the specified global that is explicitly in the
	 * globals list.
	 */
	abstract void removeGlobal(GlobalValue GV);

	void mergeGlobals(DSNode RHS) {
		Globals.addAll(RHS.Globals);
	}

	void clearGlobals() {
		Globals.clear();
	}

	boolean isEmptyGlobals() {
		return Globals.isEmpty();
	}

	int numGlobals() {
		return Globals.size();
	}

	/**
	 * addFullGlobalSet - Compute the full set of global values that are
	 * represented by this node. Unlike getGlobalsList(), this requires fair
	 * amount of work to compute, so don't treat this method call as free.
	 */
	abstract void addFullGlobalsSet(Set<GlobalValue> Set);

	/** Same as above, keeping for compat reasons */
	abstract void addFullGlobalsList(Collection<GlobalValue> List);

	/**
	 * addFullFunctionSet - Identical to addFullGlobalsSet, but only return the
	 * functions in the full list.
	 */
	abstract void addFullFunctionSet(Set<Function> Set);

	/** Same as above, keeping for compact reasons */
	void addFullFunctionList(Collection<Function> List) {
		Set<Function> Set = Sets.newTreeSet();
		addFullFunctionSet(Set);
		List.addAll(Set);
	}

	/**
	 * Same as above, only doesn't include duplicates (keeping both for compact
	 * with existing clients)
	 * 
	 * addValueList - Compute a full set of values that are represented by this
	 * node. High overhead method.
	 */
	abstract void addValueList(Collection<Value> List);

	/** maskNodeTypes - Apply a mask to the node types bitfield. */
	void maskNodeTypes(int Mask) {
		NodeType &= Mask;
	}

	void mergeNodeFlags(int RHS) {
		NodeType |= RHS;
	}

	/**
	 * getNodeFlags - Return all of the flags set on the node. If the DEAD flag is
	 * set, hide it from the caller.
	 */
	int getNodeFlags() {
		return NodeType & ~NodeTy.DeadNode.value();
	}

	/**
	 * clearNodeFlags - Useful for completely resetting a node, used in external
	 * recognizers
	 */
	DSNode clearNodeFlags() {
		NodeType = 0;
		return this;
	}

	boolean isAllocaNode() {
		return (NodeType & NodeTy.AllocaNode.value()) != 0;
	}

	boolean isHeapNode() {
		return (NodeType & NodeTy.HeapNode.value()) != 0;
	}

	boolean isGlobalNode() {
		return (NodeType & NodeTy.GlobalNode.value()) != 0;
	}

	boolean isExternFuncNode() {
		return (NodeType & NodeTy.ExternFuncNode.value()) != 0;
	}

	boolean isUnknownNode() {
		return (NodeType & NodeTy.UnknownNode.value()) != 0;
	}

	boolean isModifiedNode() {
		return (NodeType & NodeTy.ModifiedNode.value()) != 0;
	}

	boolean isReadNode() {
		return (NodeType & NodeTy.ReadNode.value()) != 0;
	}

	boolean isArrayNode() {
		return (NodeType & NodeTy.ArrayNode.value()) != 0;
	}

	boolean isCollapsedNode() {
		return (NodeType & NodeTy.CollapsedNode.value()) != 0;
	}

	boolean isIncompleteNode() {
		return (NodeType & NodeTy.IncompleteNode.value()) != 0;
	}

	boolean isCompleteNode() {
		return !isIncompleteNode();
	}

	boolean isDeadNode() {
		return (NodeType & NodeTy.DeadNode.value()) != 0;
	}

	boolean isExternalNode() {
		return (NodeType & NodeTy.ExternalNode.value()) != 0;
	}

	boolean isIntToPtrNode() {
		return (NodeType & NodeTy.IntToPtrNode.value()) != 0;
	}

	boolean isPtrToIntNode() {
		return (NodeType & NodeTy.PtrToIntNode.value()) != 0;
	}

	boolean isVAStartNode() {
		return (NodeType & NodeTy.VAStartNode.value()) != 0;
	}

	DSNode setAllocaMarker() {
		NodeType |= NodeTy.AllocaNode.value();
		return this;
	}

	DSNode setHeapMarker() {
		NodeType |= NodeTy.HeapNode.value();
		return this;
	}

	DSNode setGlobalMarker() {
		NodeType |= NodeTy.GlobalNode.value();
		return this;
	}

	DSNode setExternFuncMarker() {
		NodeType |= NodeTy.ExternFuncNode.value();
		return this;
	}

	DSNode setExternGlobalMarker() {
		NodeType |= NodeTy.ExternGlobalNode.value();
		return this;
	}

	DSNode setUnknownMarker() {
		NodeType |= NodeTy.UnknownNode.value();
		return this;
	}

	DSNode setModifiedMarker() {
		NodeType |= NodeTy.ModifiedNode.value();
		return this;
	}

	DSNode setReadMarker() {
		NodeType |= NodeTy.ReadNode.value();
		return this;
	}

	DSNode setArrayMarker() {
		NodeType |= NodeTy.ArrayNode.value();
		return this;
	}

	DSNode setCollapsedMarker() {
		NodeType |= NodeTy.CollapsedNode.value();
		return this;
	}

	DSNode setIncompleteMarker() {
		NodeType |= NodeTy.IncompleteNode.value();
		return this;
	}

	DSNode setExternalMarker() {
		NodeType |= NodeTy.ExternalNode.value();
		return this;
	}

	DSNode setIntToPtrMarker() {
		NodeType |= NodeTy.IntToPtrNode.value();
		return this;
	}

	DSNode setPtrToIntMarker() {
		NodeType |= NodeTy.PtrToIntNode.value();
		return this;
	}

	DSNode setVAStartMarker() {
		NodeType |= NodeTy.VAStartNode.value();
		return this;
	}

	void makeNodeDead() {
		Globals.clear();
		assert hasNoReferrers() : "Dead node shouldn't have refs!";
		NodeType = NodeTy.DeadNode.value();
	}

	/**
	 * forwardNode - Mark this node as being obsolete, and all references to it
	 * should be forwarded to the specified node and offset.
	 */
	abstract void forwardNode(DSNode To, long Offset);

	abstract void cleanEdges();

	abstract void dump();

	abstract void dumpParentGraph();

	abstract void dumpFuncs();

	abstract void assertOK();

	void dropAllReferences() {
		Links.clear();
		TyMap.clear();
		if (isForwarding())
			ForwardNH.setTo(null, 0);
	}

	/**
	 * remapLinks - Change all of the Links in the current node according to the
	 * specified mapping.
	 */
	abstract void remapLinks(Map<DSNode, DSNodeHandle> OldNodeMap);

	/**
	 * markReachableNodes - This method recursively traverses the specified
	 * DSNodes, marking any nodes which are reachable. All reachable nodes it adds
	 * to the set, which allows it to only traverse visited nodes once.
	 */
	abstract void markReachableNodes(Set<DSNode> ReachableNodes);

	/**
	 * checkOffsetFoldIfNeeded - Fold DSNode if the specified offset is larger
	 * than its size, and the node isn't an array or forwarding.
	 */
	abstract void checkOffsetFoldIfNeeded(long Offset);

	/** getId - Return the ID of node */
	abstract BigInteger getID();

	SortedSet<GlobalValue> getGlobals() {
		return Globals;
	}
}
