package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Map.Entry;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.pass.Function;

class DSSupport {

	enum NodeTy {
		ShadowNode(0),        		// Nothing is known about this node...
		AllocaNode(1 << 0), 		// This node was allocated with alloca
		HeapNode(1 << 1),        	// This node was allocated with malloc
		GlobalNode(1 << 2),   		// This node was allocated by a global var decl
		ExternFuncNode(1 << 3),   	// This node contains external functions
		ExternGlobalNode(1 << 4),  	// This node contains external globals
		UnknownNode(1 << 5),		// This node points to unknown allocated memory
		IncompleteNode(1 << 6),		// This node may not be complete
		
	    ModifiedNode(1 << 7),   	// This node is modified in this context
	    ReadNode(1 << 8),   		// This node is read in this context

	    ArrayNode(1 << 9),   		// This node is treated like an array
	    CollapsedNode(1 << 10),  	// This node is collapsed
	    ExternalNode(1 << 11),  	// This node comes from an external source
	    IntToPtrNode(1 << 12),  	// This node comes from an int cast
	                                // and is used in pointer operations
	                                // like geps, loads, stores
	    PtrToIntNode(1 << 13),  	// This node escapes to an int cast 
	                                // and DSA does not track it further.
	    VAStartNode(1 << 14),  		// This node is from a vastart call
	    DeadNode(1 << 15),			// This node is dead and should not be pointed to

	    Composition(AllocaNode.value() | 
	    		HeapNode.value() | 
	    		GlobalNode.value() | 
	    		UnknownNode.value());		
		
		private short value;
		private NodeTy(int value) {
			this.value = (short) value;
		}
		
		short value() {
			return value;
		}
	}
	
	enum MarkIncompleteFlags {
		MarkFormalArgs(1),
		IgnoreFormalArgs(0),
		IgnoreGlobals(2),
		MarkGlobalIncomplete(0),
		MarkVAStart(4);
		
		private short value;
		private MarkIncompleteFlags(int value) {
			this.value = (short) value;
		}
		
		short value() { return value; }
	}
	
	enum ComputeExternalFlags {
		MarkFormalsExternal(1), 
		DontMarkFormalsExternal(0),
	    ProcessCallSites(2), 
	    IgnoreCallSites(0),
	    ResetExternal(4), 
	    DontResetExternal(0);
		
		private short value;
		private ComputeExternalFlags(int value) {
			this.value = (short) value;
		}
		
		short value() { return value; }
	};
	
	enum RemoveDeadNodesFlags {
		RemoveUnreachableGlobals(1),
		KeepUnreachableGlobals(0);

		private short value;
		private RemoveDeadNodesFlags(int value) {
			this.value = (short) value;
		}
		
		short value() { return value; }
	};
	
	/// CloneFlags enum - Bits that may be passed into the cloneInto method to
	/// specify how to clone the function graph.
	enum CloneFlags {
		StripAllocaBit(1 << 0), 
		KeepAllocaBit(0),
	    DontCloneCallNodes(1 << 1), 
	    CloneCallNodes(0),
	    DontCloneAuxCallNodes(1 << 2), 
	    CloneAuxCallNodes(0),
	    StripModRefBits(1 << 3), 
	    KeepModRefBits(0),
	    StripIncompleteBit(1 << 4), 
	    KeepIncompleteBit(0);

		private short value;
		private CloneFlags(int value) {
			this.value = (short) value;
		}
		
		short value() { return value; }
	};
	
	// Function: functionIsCallable()
	//
	// Description:
	//  Determine whether the specified function can be a target of the specified
	//  call site.  We allow the user to configure what we consider to be 
	//  uncallable at an indirect function call site.
	//
	// Inputs:
	//   CS - The call site which calls the function.
	//   F - The function that is potentially called by CS.
	//
	// Return value:
	//   true - The function F can be called by the call site.
	//   false - The function F cannout be called by the call site.
	static boolean functionIsCallable(DSCallSite CS, Function F) {
		throw new UnsupportedOperationException();
	}
	
	// static mergeNodes - Helper for mergeWith()
	static void MergeNodes(DSNodeHandle CurNodeH, DSNodeHandle NH) {
		// This should have been enforced in the caller.
		Preconditions.checkArgument(CurNodeH.getOffset() >= NH.getOffset());
		// Cannot merge two nodes that are not in the same graph!
		Preconditions.checkArgument(
				CurNodeH.getNode().getParentGraph() == NH.getNode().getParentGraph());

		// Now we know that Offset >= NH.Offset, so convert it so our "Offset" (with
		// respect to NH.Offset) is now zero.  NOffset is the distance from the base
		// of our object that N starts from.
		//
		long NOffset = CurNodeH.getOffset()-NH.getOffset();
		long NSize = NH.getNode().getSize();

		// If the two nodes are of different size, and the smaller node has the array
		// bit set, collapse!
		if (NSize != CurNodeH.getNode().getSize()) {
//			#if COLLAPSE_ARRAYS_AGGRESSIVELY
			if (NSize < CurNodeH.getNode().getSize()) {
				if (NH.getNode().isArrayNode())
					NH.getNode().foldNodeCompletely();
			} else if (CurNodeH.getNode().isArrayNode()) {
				NH.getNode().foldNodeCompletely();
			}
//			#endif
		}

		// If we are merging a node with a completely folded node, then both nodes are
		// now completely folded.
		//
		if (CurNodeH.getNode().isNodeCompletelyFolded()) {
			if (!NH.getNode().isNodeCompletelyFolded()) {
				NH.getNode().foldNodeCompletely();
				assert NH.getNode() != null && NH.getOffset() == 0 :
						"folding did not make offset 0?";
				NOffset = NH.getOffset();
				NSize = NH.getNode().getSize();
				assert(NOffset == 0 && NSize == 1);
			}
		} else if (NH.getNode().isNodeCompletelyFolded()) {
			CurNodeH.getNode().foldNodeCompletely();
			assert CurNodeH.getNode() != null && CurNodeH.getOffset() == 0 :
					"folding did not make offset 0?";
			NSize = NH.getNode().getSize();
			NOffset = NH.getOffset();
			assert(NOffset == 0 && NSize == 1);
		}

		// FIXME:Add comments.
		if(NH.getNode().isArrayNode() && !CurNodeH.getNode().isArrayNode()) {
			if(NH.getNode().getSize() != 0 && CurNodeH.getNode().getSize() != 0) {
				if((NH.getNode().getSize() != CurNodeH.getNode().getSize() &&
						(NH.getOffset() != 0 || CurNodeH.getOffset() != 0)
			          && NH.getNode().getSize() < CurNodeH.getNode().getSize())) {
					CurNodeH.getNode().foldNodeCompletely();
			        NH.getNode().foldNodeCompletely();
			        NSize = NH.getNode().getSize();
			        NOffset = NH.getOffset();
				}
			}
		}
		
		if(!NH.getNode().isArrayNode() && CurNodeH.getNode().isArrayNode()) {
			if(NH.getNode().getSize() != 0 && CurNodeH.getNode().getSize() != 0) {
				if((NH.getNode().getSize() != CurNodeH.getNode().getSize() &&
			          (NH.getOffset() != 0 || CurNodeH.getOffset() != 0)
			          && NH.getNode().getSize() > CurNodeH.getNode().getSize())) {
					CurNodeH.getNode().foldNodeCompletely();
			        NH.getNode().foldNodeCompletely();
			        NSize = NH.getNode().getSize();
			        NOffset = NH.getOffset();
				}
			}
		}

		if (CurNodeH.getNode().isArrayNode() && NH.getNode().isArrayNode()) {
			if(NH.getNode().getSize() != 0 && CurNodeH.getNode().getSize() != 0
					&& (NH.getNode().getSize() != CurNodeH.getNode().getSize())){
				CurNodeH.getNode().foldNodeCompletely();
				NH.getNode().foldNodeCompletely();
				NSize = NH.getNode().getSize();
				NOffset = NH.getOffset();
			}
		}

		DSNode N = NH.getNode();
		if (CurNodeH.getNode() == N || N == null) return;
		assert(!CurNodeH.getNode().isDeadNode());

		// Merge the type entries of the two nodes together...
		CurNodeH.getNode().mergeTypeInfo(NH.getNode(), NOffset);
		if (NH.getNode().getSize() + NOffset > CurNodeH.getNode().getSize())
			CurNodeH.getNode().growSize(NH.getNode().getSize() + NOffset);
		assert(!CurNodeH.getNode().isDeadNode());

		// Merge the NodeType information.
		CurNodeH.getNode().NodeType |= N.NodeType;
		
		// Start forwarding to the new node!
		N.forwardNode(CurNodeH.getNode(), NOffset);
		assert(!CurNodeH.getNode().isDeadNode());

		// Make all of the outgoing links of N now be outgoing links of CurNodeH.
		//
		for (Entry<Long, DSNodeHandle> entry : N.Links.entrySet()) {
			if (entry.getValue().getNode() != null) {
				// Compute the offset into the current node at which to
				// merge this link.  In the common case, this is a linear
				// relation to the offset in the original node (with
				// wrapping), but if the current node gets collapsed due to
				// recursive merging, we must make sure to merge in all remaining
				// links at offset zero.
				long MergeOffset = 0;
				DSNode CN = CurNodeH.getNode();
				if (CN.Size != 1) {
					MergeOffset = (entry.getKey() + NOffset) % CN.getSize();
				}
				CN.addEdgeTo(MergeOffset, entry.getValue());
			}
		}
		
		// Now that there are no outgoing edges, all of the Links are dead.
		N.Links.clear();

		// Merge the globals list...
		CurNodeH.getNode().mergeGlobals(N);
		
		// Delete the globals from the old node...
		N.Globals.clear();
	}
}
