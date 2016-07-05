package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.alias.dsa.DSSupport.NodeTy;
import edu.nyu.cascade.util.IOUtils;

/***
 * DSNodeHandle - Implement a "handle" to a data structure node that takes care
 * of all of the add/un'refing of the node to prevent the back-pointers in the
 * graph from getting out of date. This class represents a "pointer" in the
 * graph, whose destination is an indexed offset into a node.
 *
 */

class DSNodeHandle implements Comparable<DSNodeHandle> {
	private DSNode N;
	private long Offset;

	DSNodeHandle() {
		N = null;
		Offset = 0;
	}

	DSNodeHandle(DSNode n, long offs) {
		N = null;
		Offset = 0;
		setTo(n, offs);
	}

	DSNodeHandle(DSNodeHandle H) {
		N = null;
		Offset = 0;
		DSNode NN = H.getNode();
		setTo(NN, H.Offset); // Must read offset AFTER the getNode()
	}

	DSNode getNode() {
		if (N == null || !N.isForwarding())
			return N;
		return HandleForwarding();
	}

	long getOffset() {
		getNode();
		assert !isForwarding() : "This is a forwarding NH, call getNode first";
		if (N.isNodeCompletelyFolded())
			Offset = 0;
		return Offset;
	}

	void setOffset(long Off) {
		// This is a forwarding NH, call getNode() first!
		Preconditions.checkArgument(!isForwarding());
		Offset = Off;
	}

	/**
	 * Forwarding simulates the union-find algorithm. For DSNode, ForwardNH is a
	 * representative of the equivalence class. We update the DSNode and Offset in
	 * DSNodeHandle.
	 */
	private DSNode HandleForwarding() {
		Preconditions.checkArgument(N.isForwarding()); // Can only be invoked if
																										// forwarding!

		if (IOUtils.debugEnabled()) { // assert not looping
			DSNode NH = N;
			Set<DSNode> seen = Sets.newTreeSet();
			while (NH != null && NH.isForwarding()) {
				assert !seen.contains(NH) : "Loop detected";
				seen.add(NH);
				NH = NH.ForwardNH.N;
			}
		}

		// Handle node forwarding here!
		DSNode Next = N.ForwardNH.getNode(); // Cause recursive shrinkage
		Offset += N.ForwardNH.getOffset();

		if (--N.NumReferrers == 0) {
			// Removing the last referrer to the node, sever the forwarding link
			N.stopForwarding();
		}

		N = Next;
		N.NumReferrers++;

		if (N.getSize() <= Offset) {
			assert N.getSize() <= 1 : "Forwarded to shrunk but not collapsed node?";
			Offset = 0;
		}
		return N;
	}

	/**
	 * isForwarding - Return true if this NodeHandle is forwarding to another one.
	 */
	boolean isForwarding() {
		return N != null && N.isForwarding();
	}

	/**
	 * isNull - Check to see if getNode() == null, without going through the
	 * trouble of checking to see if we are forwarding...
	 */
	boolean isNull() {
		return N == null;
	}

	/** setTo - Set the forward node to n with offset */
	void setTo(DSNode n, long offset) {
		// Cannot set node to a forwarded node!
		Preconditions.checkArgument(n == null || !n.isForwarding());

		if (N != null)
			getNode().NumReferrers--;
		N = n;
		Offset = offset;
		if (N != null) {
			N.NumReferrers++;
			if (Offset >= N.Size) {
				assert (Offset == 0
						|| N.Size == 1) : "Pointer to non-collapsed node with invalid offset!";
				Offset = 0;
			}
		}
		assert (N == null || ((N.NodeType & NodeTy.DeadNode.value()) == 0));
		assert (N == null || Offset < N.Size || (N.Size == 0 && Offset == 0) || N
				.isForwarding()) : "Node handle offset out of range!";

	}

	/** hasLink - Return true if there is a link at the specified offset... */
	boolean hasLink(long Num) {
		Preconditions.checkNotNull(N); // DSNodeHandle does not point to a node yet!
		return getNode().hasLink(Num + Offset);
	}

	/**
	 * getLink - Treat this current node pointer as a pointer to a structure of
	 * some sort. This method will return the pointer a mem[this+Num]
	 */
	DSNodeHandle getLink(long Off) {
		Preconditions.checkNotNull(N); // DSNodeHandle does not point to a node yet!
		return getNode().getLink(Offset + Off);
	}

	void setLink(long Off, DSNodeHandle NH) {
		Preconditions.checkNotNull(N);
		getNode().setLink(Off + Offset, NH);
	}

	/**
	 * addEdgeTo - Add an edge from the current node to the specified node. This
	 * can cause merging of nodes in the graph.
	 */
	void addEdgeTo(long Off, DSNodeHandle NH) {
		Preconditions.checkNotNull(N);
		getNode().addEdgeTo(Off + Offset, NH);
	}

	/**
	 * mergeWith - Merge the logical node pointed to by 'this' with the node
	 * pointed to by 'N'.
	 */
	void mergeWith(DSNodeHandle NH) {
		if (!isNull()) {
			getNode().mergeWith(NH, Offset);
		} else { // No node to merge with, so just point to Node
			Offset = 0;
			DSNode NHN = NH.getNode();
			setTo(NHN, NH.getOffset());
		}
	}

	@Override
	public boolean equals(Object O) {
		if (!(O instanceof DSNodeHandle))
			return false;
		DSNodeHandle ONH = (DSNodeHandle) O;
		if (ONH.getNode() != this.getNode())
			return false;
		return ONH.getOffset() == this.getOffset();
	}

	@Override
	public int compareTo(DSNodeHandle NH) {
		int res = getNode().compareTo(NH.getNode());
		if (res != 0)
			return res;
		return Long.compare(Offset, NH.getOffset());
	}

	@Override
	public String toString() {
		return N == null ? "" : N.getID() + ":" + Offset;
	}
}
