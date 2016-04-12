package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.Function;
import xtc.tree.Node;

/***
 * DSCallSite - Representation of a call site via its call instruction,
 * the DSNode handle for the callee function (or function pointer), and
 * the DSNode handles for the function arguments.
 * 
 * @author Wei
 *
 */

class DSCallSite {
	final Node CallSite;	// Actual call site
	final Function CalleeF;	// The function called (indirect call)
	final DSNodeHandle CalleeN;	// The function node called (indirect call)
	final DSNodeHandle RetVal;	// Returned value
	final DSNodeHandle VarArgVal;	// Merged var-arg val
	final List<DSNodeHandle> CallArgs;	// The pointer arguments
	Set<Node> MappedSites = Sets.newHashSet();	// The merged call sites
	
	static void InitNHDSNode(DSNodeHandle NH, DSNodeHandle Src,
			Map<DSNode, DSNode> NodeMap) {
		DSNode N = Src.getNode();
		if (N != null) {
			assert NodeMap.containsKey(N);
			DSNode ValN = NodeMap.get(N);
			NH.setTo(ValN, Src.getOffset());
		}
	}
	
	static void InitNHDSNodeHandle(DSNodeHandle NH, DSNodeHandle Src,
			Map<DSNode, DSNodeHandle> NodeMap) {
		DSNode N = Src.getNode();
		if (N != null) {
			assert NodeMap.containsKey(N);
			DSNode ValN = NodeMap.get(N).getNode();
			NH.setTo(ValN, Src.getOffset());
		}
	}
	
	private DSCallSite(Node callSite, 
			Function calleeF,
			DSNodeHandle calleeN,
			DSNodeHandle retVal, 
			DSNodeHandle varArgNH, 
			List<DSNodeHandle> args, 
			Set<Node> mappedSites) {
		CallSite = callSite;
		CalleeF = calleeF;
		CalleeN = calleeN;
		RetVal = retVal;
		VarArgVal = varArgNH;
		CallArgs = args;
		MappedSites = mappedSites;
	}

	DSCallSite(Node callSite, 
			DSNode funcN, 
			DSNodeHandle retVal, 
			DSNodeHandle varArgNH, 
			List<DSNodeHandle> args) {
		Preconditions.checkNotNull(callSite);	// Null callee node specified for call site!
		CallSite = callSite;
		CalleeF = null;
		CalleeN = new DSNodeHandle(funcN, 0);
		RetVal = retVal;
		VarArgVal = varArgNH;
		CallArgs = ImmutableList.copyOf(args);
	}

	DSCallSite(Node callSite, 
			Function calleeF, 
			DSNodeHandle retVal,
			DSNodeHandle varArgNH,
			List<DSNodeHandle> args) {
		Preconditions.checkNotNull(callSite);	// Null callee node specified for call site!
		CallSite = callSite;
		CalleeF = calleeF;
		CalleeN = new DSNodeHandle();
		RetVal = retVal;
		VarArgVal = varArgNH;
		CallArgs = Lists.newArrayList(args);
	}
	
	 DSCallSite(DSCallSite DSCS) {  // Simple copy ctor
		 CallSite = DSCS.CallSite; 
		 CalleeF = DSCS.CalleeF; 
		 CalleeN = DSCS.CalleeN;
		 RetVal = DSCS.RetVal; 
		 VarArgVal = DSCS.VarArgVal;
		 CallArgs = Lists.newArrayList(DSCS.CallArgs); 
		 MappedSites = ImmutableSet.copyOf(DSCS.MappedSites);
	 }

	 /** 
	  * Mapping copy constructor - This constructor takes a pre-existing call site
	  * to copy plus a map that specifies how the links should be transformed.
	  * This is useful when moving a call site from one graph to another.
	  */
	 static DSCallSite createWithDSNodeMap(DSCallSite FromCall, Map<DSNode, DSNodeHandle> NodeMap) {
		 Node Call = FromCall.CallSite;
		 
		 DSNodeHandle RetVal = new DSNodeHandle();
		 InitNHDSNodeHandle(RetVal, FromCall.RetVal, NodeMap);
		 DSNodeHandle CalleeN = new DSNodeHandle();
		 InitNHDSNodeHandle(CalleeN, FromCall.CalleeN, NodeMap);
		 DSNodeHandle VarArgVal = new DSNodeHandle();
		 InitNHDSNodeHandle(VarArgVal, FromCall.VarArgVal, NodeMap);
		 
		 Function CalleeF = FromCall.CalleeF;

		 int FromCallArgsSize = FromCall.CallArgs.size();
		 List<DSNodeHandle> CallArgs = Lists.newArrayListWithCapacity(FromCallArgsSize);		 
		 for(int i = 0; i < FromCallArgsSize; ++i) {
			 DSNodeHandle CallArg = new DSNodeHandle();
			 InitNHDSNodeHandle(CallArg, FromCall.CallArgs.get(i), NodeMap);
		 }
		 
		 Set<Node> MappedSites = ImmutableSet.copyOf(FromCall.MappedSites);
		 return new DSCallSite(Call, CalleeF, CalleeN, RetVal, VarArgVal, CallArgs, MappedSites);
	 }
	 
	 static DSCallSite createWithDSNodeHandleMap(DSCallSite FromCall, Map<DSNode, DSNodeHandle> NodeMap) {
		 Node Call = FromCall.CallSite;
		 
		 DSNodeHandle RetVal = new DSNodeHandle();
		 InitNHDSNodeHandle(RetVal, FromCall.RetVal, NodeMap);
		 DSNodeHandle CalleeN = new DSNodeHandle();
		 InitNHDSNodeHandle(CalleeN, FromCall.CalleeN, NodeMap);
		 DSNodeHandle VarArgVal = new DSNodeHandle();
		 InitNHDSNodeHandle(VarArgVal, FromCall.VarArgVal, NodeMap);
		 
		 Function CalleeF = FromCall.CalleeF;

		 int FromCallArgsSize = FromCall.CallArgs.size();
		 List<DSNodeHandle> CallArgs = Lists.newArrayListWithCapacity(FromCallArgsSize);		 
		 for(int i = 0; i < FromCallArgsSize; ++i) {
			 DSNodeHandle CallArg = new DSNodeHandle();
			 InitNHDSNodeHandle(CallArg, FromCall.CallArgs.get(i), NodeMap);
		 }
		 
		 Set<Node> MappedSites = ImmutableSet.copyOf(FromCall.MappedSites);
		 return new DSCallSite(Call, CalleeF, CalleeN, RetVal, VarArgVal, CallArgs, MappedSites);
	 }
	 
	 /**
	  * isDirectCall - Return true if this call site is a direct call of the
	  * function specified by getCalleeFunc.  If not, it is an indirect call to
	  * the node specified by getCalleeNode.
	  */
	 boolean isDirectCall() { return CalleeF != null; }
	 boolean isIndirectCall() { return !isDirectCall(); }
	 
	 // Accessor functions...
	 Node getCaller() {
		 throw new UnsupportedOperationException();
	 }
	 
	 Node getCallSite() { return CallSite; }
	 
	 DSNodeHandle getRetVal() { return RetVal; }
	 
	 DSNodeHandle getVAVal() { return VarArgVal; }
	 
	 DSNode getCalleeN()  {
		 Preconditions.checkArgument(CalleeF == null && CalleeN.getNode() != null); 
		 return CalleeN.getNode();
	 }
	 
	 Function getCalleeF() {
		 Preconditions.checkArgument(CalleeN.getNode() == null && CalleeF != null); 
		 return CalleeF;
	 }
	 
	 int getNumPtrArgs() { return CallArgs.size(); }
	 
	 int getNumMappedSites() { return MappedSites.size(); }
	 
	 DSNodeHandle getPtrArg(int i) {
		 Preconditions.checkElementIndex(i, CallArgs.size());
		 return CallArgs.get(i);
	 }
	 
	 Set<Node> getMappedSites() { return MappedSites; }
	 
	 void addPtrArg(DSNodeHandle NH) { CallArgs.add(NH); }
	 
	 /**
	  * mergeWith - Merge the return value and parameters of the these two call
	  * sites.
	  */
	 void mergeWith(DSCallSite CS) {
		 getRetVal().mergeWith(CS.getRetVal());
		 getVAVal().mergeWith(CS.getVAVal());
		 int MinArgs = getNumPtrArgs();
		 if (CS.getNumPtrArgs() < MinArgs) MinArgs = CS.getNumPtrArgs();
		 
		 for (int a = 0; a != MinArgs; ++a)
			 getPtrArg(a).mergeWith(CS.getPtrArg(a));

		 for (int a = MinArgs, e = CS.getNumPtrArgs(); a != e; ++a)
			 CallArgs.add(CS.getPtrArg(a));

		 MappedSites.add(CS.getCallSite());
		 MappedSites.addAll(CS.getMappedSites());
	 }
	 
	 /**
	  * markReachableNodes - This method recursively traverses the specified
	  * DSNodes, marking any nodes which are reachable.  All reachable nodes it
	  * adds to the set, which allows it to only traverse visited nodes once.
	  * 
	  * @param Nodes
	  */
	 void markReachableNodes(Set<DSNode> Nodes) {
		 throw new UnsupportedOperationException();
	 }

	 /**
	  * isVarArg - Determines if the call this represents is to a variable argument
	  * function
	  * 
	  * @return
	  */
	 boolean isVarArg() {
		 throw new UnsupportedOperationException();
	 }
	 
	 /**
	  * isUnresolvable - Determines if this call has properties that would
	  * prevent it from ever being resolved.  Put another way, no amount
	  * additional information will make this callsite resolvable.
	  * 
	  * @return
	  */
	 boolean isUnresolvable() {
		 throw new UnsupportedOperationException();
	 }
}
