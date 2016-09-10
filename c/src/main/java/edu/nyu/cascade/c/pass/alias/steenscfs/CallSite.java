package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import xtc.tree.Node;
import xtc.type.Type;

class CallSite {
	final Node CallNode; // Actual call site
	final CFSFunction CalleeF; // The function called (direct call)
	final ECR CalleeECR; // The function node called (indirect call)
	final ECR RetVal; // Returned value
	final List<ECR> Args; // The arguments.
	final List<Type> ArgTypes;

	// The size of PtrArgMarks is the sum of the size of Args and the size of
	// VarArgs. For the i-th mark of PtrArgMarks, if i is less than the size of
	// Args, PtrArgMarks[i] indicates whether the i-th arg within Args is a
	// pointer or not; otherwise, let 's' be the size of Args, then PtrArgMarks[i]
	// indicates whether the (i-s)-th arg within VarArgs is a pointer or not.
	final List<Boolean> PtrArgMarks; // The marks of pointer arguments;

	// The current size of pointer arguments (including both args and var-args).
	int numPtrArgs = 0;

	int numArgs = 0; // The current size of PtrArgMarks

	CallSite(Node callNode, CFSFunction func, ECR callee, ECR retVal) {
		CallNode = callNode;
		CalleeF = func;
		CalleeECR = callee;
		RetVal = retVal;
		Args = Lists.newArrayList();
		ArgTypes = Lists.newArrayList();
		PtrArgMarks = Lists.newArrayList();
	}

	static CallSite createDirectCall(Node callNode, CFSFunction func,
			ECR retVal) {
		return new CallSite(callNode, func, ECR.createBottom(), retVal);
	}

	static CallSite createIndirectCall(Node callNode, ECR CalleeECR, ECR retVal) {
		return new CallSite(callNode, null, CalleeECR, retVal);
	}

	boolean isDirectCall() {
		return CalleeF != null;
	}

	boolean isIndirectCall() {
		return !isDirectCall();
	}

	CFSFunction getCalleeFunc() {
		return CalleeF;
	}

	Node getCallNode() {
		return CallNode;
	}

	ECR getRetECR() {
		return RetVal;
	}

	int getNumArgs() {
		return Args.size();
	}

	Collection<ECR> getArgs() {
		return ImmutableList.copyOf(Args);
	}

	int getNumPtrArgs() {
		return numPtrArgs;
	}

	void addPtrArg(ECR arg, Type argType) {
		++numPtrArgs;
		Args.add(arg);
		ArgTypes.add(argType);
		++numArgs;
		PtrArgMarks.add(true);
	}

	void addNonPtrArg(ECR arg, Type argType) {
		Args.add(arg);
		ArgTypes.add(argType);
		++numArgs;
		PtrArgMarks.add(false);
	}

	ECR getArg(int i) {
		return Args.get(i);
	}

	Type getArgType(int i) {
		return ArgTypes.get(i);
	}

	ECR getCalleeECR() {
		return CalleeECR;
	}
}
