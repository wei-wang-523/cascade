package edu.nyu.cascade.ir.impl;

import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRCallGraphNode;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.util.CacheException;

public class CallGraphNode implements IRCallGraphNode {
	
  private static final LoadingCache<IRVarInfo, CallGraphNode> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<IRVarInfo, CallGraphNode>(){
        public CallGraphNode load(IRVarInfo key) {
          return new CallGraphNode(key);
        }
      });
  
	public static CallGraphNode createDeclaration(IRVarInfo sig, Node declNode) {
		try {
			CallGraphNode res = cache.get(sig);
			res.setFuncDeclareNode(declNode);
			return res;
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}
	
	public static CallGraphNode createDefinition(IRVarInfo sig, Node defNode) {
		try {
			CallGraphNode res = cache.get(sig);
			res.setFuncDefinitionNode(defNode);
			return res;
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}
  
	public static CallGraphNode getCallGraphNode(IRVarInfo sig) {
		CallGraphNode res = cache.getIfPresent(sig);
		if(res == null) {
			throw new IllegalArgumentException("No function node of " + sig.getName());
		}
		return res;
	}

	private final String funcName;
  private Node declNode, defNode;
  private final IRVarInfo signature;
  private final Set<IRCallGraphNode> calledFunctions;
  
  private CallGraphNode(IRVarInfo sig) {
  	this.calledFunctions = Sets.newHashSet();
  	this.signature = sig;
    this.funcName = sig.getName();
  }

  @Override
  public String toString() {
    return getName();
  }

  void format(Printer printer) {
    printer
        .pln("CallGraphNode " + toString());
  }

	@Override
  public void addCalledFunction(IRCallGraphNode function) {
		calledFunctions.add(function);
  }

	@Override
  public ImmutableSet<IRCallGraphNode> getCalledFunctions() {
	  return ImmutableSet.copyOf(calledFunctions);
  }

	@Override
  public String getName() {
	  return funcName;
  }
	
	@Override
	public void setFuncDeclareNode(Node decl) {
		declNode = decl;
	}
	
	@Override
	public void setFuncDefinitionNode(Node def) {
		defNode = def;
	}
	
	@Override
	public Node getFuncDeclareNode() {
		return declNode;
	}
	
	@Override
	public Node getFuncDefinitionNode() {
		return defNode;
	}
	
	@Override
	public boolean isDefined() {
		return defNode != null;
	}
	
	@Override
	public boolean isDeclared() {
		return declNode != null;
	}
	
	@Override
	public String getScopeName() {
		Preconditions.checkArgument(isDefined());
		return CType.getScopeName(defNode);
	}
	
	@Override
	public IRVarInfo getSignature() {
		return signature;
	}
	
	@Override
	public boolean equals(Object node) {
		if(!(node instanceof CallGraphNode)) return false;
		CallGraphNode graphNode = (CallGraphNode) node;
    return (graphNode != null 
    		&& signature.equals(graphNode.signature));
	}
}
