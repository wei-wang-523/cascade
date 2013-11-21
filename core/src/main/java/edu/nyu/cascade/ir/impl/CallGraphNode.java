package edu.nyu.cascade.ir.impl;

import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRCallGraphNode;
import edu.nyu.cascade.util.CacheException;

public class CallGraphNode implements IRCallGraphNode {
	
  private static final LoadingCache<Node, CallGraphNode> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Node, CallGraphNode>(){
        public CallGraphNode load(Node key) {
          return new CallGraphNode(key);
        }
      });
  
	public static CallGraphNode create(Node declNode) {
		try {
			return cache.get(declNode);
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}
  
	private final String funcName;
  private final Node declNode;
  private final Set<IRCallGraphNode> calledFunctions;
  
  private CallGraphNode(Node declNode) {
  	Preconditions.checkArgument(declNode.hasName("FunctionDefinition"));
  	this.calledFunctions = Sets.newHashSet();
  	this.declNode = declNode;
    final GNode declarator = declNode.getGeneric(2);
    final GNode identifier = CAnalyzer.getDeclaredId(declarator);
    this.funcName = identifier.getString(0);
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
	public Node getFuncDeclareNode() {
		return declNode;
	}
	
	@Override
	public String getScopeName() {
		return CType.getScopeName(declNode);
	}
	
	@Override
	public boolean equals(Object node) {
		if(!(node instanceof CallGraphNode)) return false;
		CallGraphNode graphNode = (CallGraphNode) node;
		if(this == graphNode) return true;
		if(funcName != graphNode.funcName) return false;
		if(!declNode.equals(graphNode.declNode)) return false;
		return true;
	}
}
