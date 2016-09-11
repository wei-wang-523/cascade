package edu.nyu.cascade.c.pass.alias;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.pass.alias.Function;
import xtc.tree.Node;
import xtc.type.Type;

public class CallSite<T> {
	final Node CallNode; // Actual call site
	final Function<T> CalleeF; // The function called (direct call)
	final T CalleeECR; // The function node called (indirect call)
	final T RetVal; // Returned value
	final List<T> Args; // The arguments.
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

	CallSite(Node callNode, Function<T> func, T callee, T retVal) {
		CallNode = callNode;
		CalleeF = func;
		CalleeECR = callee;
		RetVal = retVal;
		Args = Lists.newArrayList();
		ArgTypes = Lists.newArrayList();
		PtrArgMarks = Lists.newArrayList();
	}

	public static <T> CallSite<T> createDirectCall(Node callNode, Function<T> func,
			T retVal) {
		return new CallSite<T>(callNode, func, null, retVal);
	}

	public static <T> CallSite<T> createIndirectCall(Node callNode, T CalleeECR,
			T retVal) {
		return new CallSite<T>(callNode, null, CalleeECR, retVal);
	}

	public boolean isDirectCall() {
		return CalleeF != null;
	}

	public boolean isIndirectCall() {
		return !isDirectCall();
	}

	public Function<T> getCalleeFunc() {
		return CalleeF;
	}

	public Node getCallNode() {
		return CallNode;
	}

	public T getRetECR() {
		return RetVal;
	}

	public int getNumArgs() {
		return Args.size();
	}

	public Collection<T> getArgs() {
		return ImmutableList.copyOf(Args);
	}

	public int getNumPtrArgs() {
		return numPtrArgs;
	}

	public void addPtrArg(T arg, Type argType) {
		++numPtrArgs;
		Args.add(arg);
		ArgTypes.add(argType);
		++numArgs;
		PtrArgMarks.add(true);
	}

	public void addNonPtrArg(T arg, Type argType) {
		Args.add(arg);
		ArgTypes.add(argType);
		++numArgs;
		PtrArgMarks.add(false);
	}

	public T getArg(int i) {
		return Args.get(i);
	}

	public Type getArgType(int i) {
		return ArgTypes.get(i);
	}

	public T getCalleeECR() {
		return CalleeECR;
	}
}
