package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.pass.GlobalValue;

/***
 * ReachabilityCloner - This class is used to incrementally clone and merge
 * nodes from a non-changing source graph into a potentially mutating
 * destination graph.  Nodes are only cloned over on demand, either in
 * responds to a merge() or getClonedNH() call.  When a node is cloned over,
 * all of the nodes reachable from it are automatically brought over as well.
 *
 */

class ReachabilityCloner {
	DSGraph Dest, Src;
	
	// BitsToKeep - These bits are retained from the source node when the
	// source nodes are merged into the destination graph.
	int BitsToKeep;
	
	int CloneFlags;
	
	boolean CreateDest;
	
	// NodeMap - A mapping from nodes in the source graph to the nodes that
	// represent them in the destination graph.
	// We cannot use a densemap here as references into it are not stable across
	// insertion
	final Map<DSNode, DSNodeHandle> NodeMap = Maps.newTreeMap();
	

	ReachabilityCloner(DSGraph dest, DSGraph src, int cloneFlags, boolean createDest) {
		Preconditions.checkArgument(dest != src);
		Dest = dest;
		Src = src;
		CreateDest = createDest;
		
		BitsToKeep = ~DSSupport.NodeTy.DeadNode.value();
		if ((CloneFlags & DSSupport.CloneFlags.StripAllocaBit.value()) != 0) {
			BitsToKeep &= ~DSSupport.NodeTy.AllocaNode.value();
		}

		if ((CloneFlags & DSSupport.CloneFlags.StripModRefBits.value()) != 0) {
			BitsToKeep &= ~(DSSupport.NodeTy.ModifiedNode.value() | DSSupport.NodeTy.ReadNode.value());
		} 

		if ((CloneFlags & DSSupport.CloneFlags.StripIncompleteBit.value()) != 0) {
			BitsToKeep &= ~DSSupport.NodeTy.IncompleteNode.value();
		}
	}

	DSNodeHandle getClonedNH(DSNodeHandle SrcNH) {
		if (SrcNH.isNull()) return new DSNodeHandle();
		DSNode SN = SrcNH.getNode();
		
		DSNodeHandle NH = getOrCreate(NodeMap, SN);
		
		if (!NH.isNull()) { // Node already mapped?
			DSNode NHN = NH.getNode();
			long NewOffset = NH.getOffset() + SrcNH.getOffset();
			if (NHN != null) {
				NHN.checkOffsetFoldIfNeeded(NewOffset);
				NHN = NH.getNode();
			}
			return new DSNodeHandle(NHN, NewOffset);
		}
		
		// If SrcNH has globals and the destination graph has one of the same globals,
		// merge this node with the destination node, which is much more efficient.
		if (!SN.Globals.isEmpty()) {
			DSScalarMap DestSM = Dest.getScalarMap();
			for (GlobalValue GV : SN.Globals) {
				DSNodeHandle DestNH = DestSM.find(GV);
				if (DestNH != null && !DestNH.isNull()) {
					// We found one, use merge instead!
					merge(DestNH, Src.getNodeForValue(GV));
					NH = NodeMap.get(SN);
					assert (! DestNH.isNull()) : "Didn't merge node!";
					DSNode NHN = NH.getNode();
					long NewOffset = NH.getOffset() + SrcNH.getOffset();
					if (NHN != null) {
						NHN.checkOffsetFoldIfNeeded(NewOffset);
						NHN = NH.getNode();
					}
					return new DSNodeHandle(NHN, NewOffset);
				}
			}
		}
		
		if (!CreateDest) return new DSNodeHandle(null, 0);
		
		DSNode DN = new DSNodeImpl(SN, Dest, true /* Null out all links */);
		DN.maskNodeTypes(BitsToKeep);
		NH = new DSNodeHandle(DN, 0);
		NodeMap.put(SN, NH);
		
		// Next, recursively clone all outgoing links as necessary.  Note that
		// adding these links can cause the node to collapse itself at any time, and
		// the current node may be merged with arbitrary other nodes.  For this
		// reason, we must always go through NH.
		DN = null;
		for(Entry<Long, DSNodeHandle> edge : SN.Links.entrySet()) {
			final DSNodeHandle edgeNH = edge.getValue();
			if (edgeNH.isNull()) {
				final DSNodeHandle DestEdge = getClonedNH(edgeNH);
				// Compute the offset into the current node at which to
				// merge this link.  In the common case, this is a linear
				// relation to the offset in the original node (with
				// wrapping), but if the current node gets collapsed due to
				// recursive merging, we must make sure to merge in all remaining
				// links at offset zero.
				long MergeOffset = 0;
				DSNode CN = NH.getNode();
				if (CN.getSize() != 1) {
					MergeOffset = (edge.getKey() + NH.getOffset()) % CN.getSize();
				}
				CN.addEdgeTo(MergeOffset, DestEdge);
			}
		}
		
		// If this node contains any globals, make sure they end up in the scalar
		// map with the correct offset.
		for (GlobalValue GV : SN.Globals) {
			final DSNodeHandle SrcGNH = Src.getNodeForValue(GV);
			DSNodeHandle DestGNH = getOrCreate(NodeMap, SrcGNH.getNode());
			assert DestGNH.getNode() == NH.getNode() : "Global mapping inconsistent";
			Dest.getNodeForValue(GV).mergeWith(
					new DSNodeHandle(DestGNH.getNode(), DestGNH.getOffset()+SrcGNH.getOffset()));
		}
		
		NH.getNode().mergeGlobals(SN);

		DSNode NHN = NH.getNode();
		long NewOffset = NH.getOffset() + SrcNH.getOffset();
		if (NHN != null) {
			NHN.checkOffsetFoldIfNeeded(NewOffset);
			NHN = NH.getNode();
		}
		
		return new DSNodeHandle(NHN, NewOffset);
	}
	
	void merge(final DSNodeHandle NH, final DSNodeHandle SrcNH) {
		if (SrcNH.isNull())	return; // Noop
		if (NH.isNull()) {
			// If there is no destination node, just clone the source and assign the
			// destination node to be it.
			NH.mergeWith(getClonedNH(SrcNH));
			return;
		}
		
		// Okay, at this point, we know that we have both a destination and a source
		// node that need to be merged.  Check to see if the source node has already
		// been cloned.
		final DSNode SN = SrcNH.getNode();
		DSNodeHandle SCNH = getOrCreate(NodeMap, SN); // SourceClonedNodeHandle
		if (!SCNH.isNull()) {   // Node already cloned?
			DSNode SCNHN = SCNH.getNode();
		    NH.mergeWith(new DSNodeHandle(SCNHN,
		    		SCNH.getOffset()+SrcNH.getOffset()));
		    return;  // Nothing to do!
		}
		
		// Okay, so the source node has not already been cloned.  Instead of creating
		// a new DSNode, only to merge it into the one we already have, try to perform
		// the merge in-place.  The only case we cannot handle here is when the offset
		// into the existing node is less than the offset into the virtual node we are
		// merging in.  In this case, we have to extend the existing node, which
		// requires an allocation anyway.
		DSNode DN = NH.getNode();   // Make sure the Offset is up-to-date
		if (NH.getOffset() >= SrcNH.getOffset()) {
			if (!DN.isNodeCompletelyFolded()) {
				// Make sure the destination node is folded if the source node is folded.
				if (SN.isNodeCompletelyFolded()) {
					DN.foldNodeCompletely();
					DN = NH.getNode();
				} else if (SN.getSize() != DN.getSize()) {
					// If the two nodes are of different size, and the smaller node has the
					// array bit set, collapse!
					
					//	#if COLLAPSE_ARRAYS_AGGRESSIVELY
					if (SN.getSize() < DN.getSize()) {
						if (SN.isArrayNode()) {
							DN.foldNodeCompletely();
							DN = NH.getNode();
						}
					} else if (DN.isArrayNode()) {
						DN.foldNodeCompletely();
						DN = NH.getNode();
					}
					//	#endif
				}
						
				if (!DN.isArrayNode() && SN.isArrayNode()) {
					if (DN.getSize() != 0 && SN.getSize() != 0) {
						if (DN.getSize() != SN.getSize()) {
							if (NH.getOffset() != 0 || SrcNH.getOffset() != 0) {
								if (DN.getSize() > SN.getSize()) {
									DN.foldNodeCompletely();
									DN = NH.getNode();
								}
							}
						}
					}
				}
					
				if (!SN.isArrayNode() && DN.isArrayNode()) {
					if (DN.getSize() != 0 && SN.getSize() != 0) {
						if(DN.getSize() != SN.getSize()) {
							if (NH.getOffset() != 0 || SrcNH.getOffset() != 0) {
								if (DN.getSize() < SN.getSize()) {
									DN.foldNodeCompletely();
									DN = NH.getNode();
								}
							}
						}
					}
				}

				if (SN.isArrayNode() && DN.isArrayNode()) {
					if (DN.getSize() != 0 && SN.getSize() != 0) {
						if (DN.getSize() != SN.getSize()) {
							DN.foldNodeCompletely();
							DN = NH.getNode();
						}
					}
				}
		
				if (!DN.isNodeCompletelyFolded() && DN.getSize() < SN.getSize()) {
					DN.growSize(SN.getSize());
				}
					
				// Merge the type entries of the two nodes together...
				if (!DN.isNodeCompletelyFolded()) {
					DN.mergeTypeInfo(SN, NH.getOffset() - SrcNH.getOffset());
				}
			}
		
			assert(!DN.isDeadNode());
		
			// Merge the NodeType information.
			DN.mergeNodeFlags(SN.getNodeFlags() & BitsToKeep);
			
			// Before we start merging outgoing links and updating the scalar map, make
			// sure it is known that this is the representative node for the src node.
			SCNH = new DSNodeHandle(DN, NH.getOffset()-SrcNH.getOffset());
			NodeMap.put(SN, SCNH);
			
			// If the source node contains any globals, make sure they end up in the
			// scalar map with the correct offset.
			if (!SN.getGlobals().isEmpty()) {
				// Update the globals in the destination node itself.
				DN.mergeGlobals(SN);
				
				// Update the scalar map for the graph we are merging the source node into.
				for (GlobalValue GV : SN.getGlobals()) {
					final DSNodeHandle SrcGNH = Src.getNodeForValue(GV);
					DSNodeHandle DestGNH = getOrCreate(NodeMap, SrcGNH.getNode());
					assert DestGNH.getNode() == NH.getNode() : "Global mapping inconsistent";
					Dest.getNodeForValue(GV).mergeWith(
							new DSNodeHandle(DestGNH.getNode(),
									DestGNH.getOffset()+SrcGNH.getOffset()));
				}
	    	
				NH.getNode().mergeGlobals(SN);
			}
		} else { // NH.getOffset() < SrcNH.getOffset()
			// We cannot handle this case without allocating a temporary node.  Fall
			// back on being simple.
			DSNode NewDN = new DSNodeImpl(SN, Dest, true /* Null out all links */);
			NewDN.maskNodeTypes(BitsToKeep);
			NH.mergeWith(new DSNodeHandle(NewDN, SrcNH.getOffset()));
			
			// Before we start merging outgoing links and updating the scalar map, make
			// sure it is known that this is the representative node for the src node.
			SCNH = new DSNodeHandle(NH.getNode(), NH.getOffset()-SrcNH.getOffset());
			NodeMap.put(SN, SCNH);
			
			// If the source node contained any globals, make sure to create entries
			// in the scalar map for them!
			for (GlobalValue GV : SN.getGlobals()) {
				final DSNodeHandle SrcGNH = Src.getNodeForValue(GV);
				DSNodeHandle DestGNH = getOrCreate(NodeMap, SrcGNH.getNode());
	          
				assert DestGNH.getNode() == NH.getNode() : "Global mapping inconsistent";
				assert SrcGNH.getNode() == SN : "Global mapping inconsistent";
				Dest.getNodeForValue(GV).mergeWith(
						new DSNodeHandle(DestGNH.getNode(),
								DestGNH.getOffset()+SrcGNH.getOffset()));
			}
		}

		// Nest, recursively merge all outgoing links as necessary.  Note that
		// adding these links can cause the destination node to collapse itself at
		// any time, and the current node may be merged with arbitrary other nodes.
		// For this reason, we must always got through NH.
		DN = null;
		for (Entry<Long, DSNodeHandle> entry : SN.Links.entrySet()) {
			final DSNodeHandle SrcEdge = entry.getValue();
			if (!SrcEdge.isNull()) {
				// Compute the offset into the current node at which to
				// merge this link.  In the common case, this is a linear
				// relation to the offset in the original node (with
				// wrapping), but if the current node gets collapsed due to
				// recursive merging, we must make sure to merge in all remaining 
				// links at offset zero.
				assert !SCNH.isNull();
				DSNode CN = SCNH.getNode();
				long MergeOffset = (entry.getKey() + SCNH.getOffset()) % CN.getSize();
	    		
				DSNodeHandle Tmp = CN.getLink(MergeOffset);
				if (!Tmp.isNull()) {
					// Perform the recursive merging.  Make sure to create a temp NH,
					// because the Link can disappear in the process of recursive merging.
					merge(Tmp, SrcEdge);
				} else {
					Tmp.mergeWith(getClonedNH(SrcEdge));
					// Merging this could cause all kinds of recursive things to happened,
					// culminating in the current node being eliminated.  Since this is
					// possible, make sure to re-acquire the link from CN.
					CN = SCNH.getNode();
					long TmpMergeOffset = (entry.getKey() + SCNH.getOffset()) % CN.getSize();
					CN.getLink(TmpMergeOffset).mergeWith(Tmp);
				}
			}
		}
	}
	
	/**
	 * mergeCallSite - Merge the nodes reachable from the specified src call
	 * site into the nodes reachable from DestCS.
	 */
	void mergeCallSite(DSCallSite DestCS, DSCallSite SrcCS) {
		
	}
	
	DSCallSite cloneCallSite(DSCallSite SrcCS) {
		return null;
	}

	boolean clonedAnyNodes() { return !NodeMap.isEmpty(); }
	
	boolean hasClonedNode(DSNode N) { return NodeMap.containsKey(N); }

	void destroy() { NodeMap.clear(); }
	
	private DSNodeHandle getOrCreate(Map<DSNode, DSNodeHandle> NodeMap, DSNode DN) {
		Preconditions.checkNotNull(NodeMap);
		DSNodeHandle NH;
		if (NodeMap.containsKey(DN)) {
			NH = NodeMap.get(DN);
		} else {
			NH = new DSNodeHandle();
			NodeMap.put(DN, NH);
		}
		return NH;
	}
}
