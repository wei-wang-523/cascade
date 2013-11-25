package edu.nyu.cascade.c;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRCallEdge;
import edu.nyu.cascade.ir.IRCallGraph;
import edu.nyu.cascade.ir.IRCallGraphNode;
import edu.nyu.cascade.ir.SymbolTable;
import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;

public final class CScopeAnalyzer {
	
	public static final class Builder {
		IRCallGraph callGraph;
		SymbolTable symbolTable;

  	public Builder() {}
  	
    public Builder setCallGraph(IRCallGraph _callGraph) {
    	callGraph = _callGraph;
	    return this;
    }
    
    public Builder setSymbolTable(SymbolTable _symbolTable) {
    	symbolTable = _symbolTable;
    	return this;
    }
    
    public CScopeAnalyzer build() {
	    return CScopeAnalyzer.create(callGraph, symbolTable);
    }
  }
	
	public static CScopeAnalyzer create(IRCallGraph callGraph, SymbolTable symbolTable) {
		return new CScopeAnalyzer(callGraph, symbolTable);
	}
	
	/**
	 * Check is <code>scope_a</code> is the (both direct and indirect) parent
	 * <code>scope_b</code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public static boolean isNested(Scope scope_a, Scope scope_b) {
		if(scope_a.equals(scope_b))	return false;
		
		if(scope_a.isRoot()) return true;
		
		String name_a = scope_a.getQualifiedName();
		String name_b = scope_b.getQualifiedName();
		return name_b.startsWith(name_a);
	}
	
	/**
	 * Check is <code>scope_a</code> is either (both direct and indirect) parent
	 * <code>scope_b</code>, or <code>scope_a</code> is same as <code>scope_b
	 * </code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public static boolean isNestedOrEqual(Scope scope_a, Scope scope_b) {
		if(scope_a.equals(scope_b))	return true;
		
		String name_a = scope_a.getQualifiedName();
		String name_b = scope_b.getQualifiedName();
		return name_b.startsWith(name_a);
	}
	
	private final ImmutableMap<Scope, Map<Node, Scope>> callScopeMaps;
	private final SymbolTable symbolTable;
	
	private CScopeAnalyzer(IRCallGraph callGraph, SymbolTable _symbolTable) {
		symbolTable = _symbolTable;
		ImmutableMap.Builder<Scope, Map<Node, Scope>> builder = 
				new ImmutableMap.Builder<Scope, Map<Node, Scope>>();
		
		/* Build all function call scope pair */
		for(IRCallGraphNode callNode : callGraph.getNodes()) {
			if(callNode.isDefined()) {
				Map<Node, Scope> calleeMap = Maps.newHashMap();
				
				for(IRCallEdge<? extends IRCallGraphNode> edge 
						: callGraph.getIncomingEdges(callNode)) {
					IRCallGraphNode callerNode = edge.getSource();
					Scope srcScope = symbolTable.getScope(callerNode.getScopeName());
					calleeMap.put(edge.getCallNode(), srcScope);
				}
				
				Scope destScope = symbolTable.getScope(callNode.getScopeName());
				builder.put(destScope, calleeMap);
			}
		}
		
		callScopeMaps = builder.build();
	}
	
	/**
	 * Check is <code>scope_a</code> is the caller scope or the parent scope
	 * of the caller scope of <code>scope_b</code> with call node <code>
	 * callNode</code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public boolean isCalled(Node callNode, Scope scope_a, Scope scope_b) {
		Preconditions.checkArgument(callScopeMaps != null);
		if(callScopeMaps.isEmpty())	return false;
		
		Map<Node, Scope> calleeMap = callScopeMaps.get(scope_b);
		Scope callerScope = calleeMap.get(callNode);
		
		if(callerScope.equals(scope_a)) return true;
		
		return isNestedOrEqual(scope_a, callerScope);
	}
	
	/**
	 * Check is <code>scope_a</code> is the caller scope or the parent scope
	 * of the caller scope of <code>scope_b</code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public boolean isCalled(Scope scope_a, Scope scope_b) {
		Preconditions.checkArgument(callScopeMaps != null);
		if(callScopeMaps.isEmpty())	return false;
		if(!callScopeMaps.containsKey(scope_b)) return false;
		Map<Node, Scope> calleeMap = callScopeMaps.get(scope_b);
		Iterable<Scope> callees = calleeMap.values();
		return Iterables.contains(callees, scope_a);
	}
	
	/**
	 * Get the parent scope of <code>preScope</code> that
	 * is the neighbor of <code>currScope</code>.
	 * 
	 * If <code>currScope</code> is the caller of <code>preScope
	 * </code>, return the root function scope of <code>
	 * preScope</code>, which is the function called at <code>
	 * currScope</code>.
	 * 
	 * If <code>currScope</code> is under the same parent (might be
	 * indirect) scope as <code>preScope</code>, return the 
	 * scope that is one level lower of the same parent scope;
	 * 
	 * If <code>currScope</code> is the parent of <code>preScope
	 * </code>, return scope that is one level lower of the 
	 * <code>currScope</code>;
	 * 
	 * @param preScope
	 * @param currScope
	 * @return
	 */
	public static Scope findNeighbor(Scope preScope, Scope currScope) {
		Preconditions.checkArgument(!isNestedOrEqual(preScope, currScope));
		if(isNested(currScope, preScope)) {
			Scope resScope = preScope;
			while(!resScope.getParent().equals(currScope)) {
				resScope = resScope.getParent();
			}
			return resScope;
		} else {
			Scope resScope = preScope;
			while(!(isNested(resScope.getParent(), currScope))) {
				resScope = resScope.getParent();
			}
			return resScope;
		}
	}
}
