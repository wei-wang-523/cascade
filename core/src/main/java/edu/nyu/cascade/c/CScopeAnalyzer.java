package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.Map;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Queues;

import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

public final class CScopeAnalyzer {
	
	private static Deque<String> scopeStack = Queues.newArrayDeque();
	private static Map<String, Deque<Long>> scopeMap = Maps.newHashMap();
	private static long id = 0;
	private static Deque<Long> currIdStack = Queues.newArrayDeque();

	public static void reset() {
		id = 0;
		scopeStack.clear();
		scopeMap.clear();
	}
	
	public static void popScope() {
		String scopeName = scopeStack.pop();
		long currId = scopeMap.get(scopeName).pop();
		IOUtils.debug().pln("Pop " + scopeName + currId);
	}
	
	public static void pushScope(String scopeName) {
		scopeStack.push(scopeName);
		if(!scopeMap.containsKey(scopeName)) {
			scopeMap.put(scopeName, Queues.<Long>newArrayDeque());
		};
		scopeMap.get(scopeName).push(++id);
		IOUtils.debug().pln("Push " + scopeName + id);
	}
	
	public static String peekScopeName(Scope scope) {
		String qName = scope.getQualifiedName();
		
		if(scope.isRoot()) return qName;
		if(scopeMap.isEmpty()) return qName;
				
		while(!scope.getParent().isRoot()) {
			scope = scope.getParent();
		}
		
		String topName = scope.getQualifiedName();
		if(!scopeMap.containsKey(topName)) return qName;
		long currId = scopeMap.get(topName).peek();
		
		return qName.replace(topName, topName + String.valueOf(currId));
	}
	
	/**
	 * Get the top scope of all the scope names
	 * @param first
	 * @param rest
	 * @return
	 */
	public static String getTopScope(String first, String... rest) {
		return getTopScope(Lists.asList(first, rest));
	}
	
	/**
	 * Get the root scope name, which is set to be empty string
	 * @return empty string
	 */
	public static String getRootScopeName() {
		return "";
	}

	/**
	 * Remember the id and stored it in <code>currIdStack
	 * </code> to restore after finishing invariant's lift 
	 * statements processing
	 */
	public static void liftStatementsBegin() {
		currIdStack.push(id);
	}

	/**
	 * Restore the id to the id stored in <code>currIdStack
	 * </code> before processing invariant's lift statements
	 */
	public static void liftStatementsEnd() {
	  id = currIdStack.pop();
	}

	/**
	 * Check is <code>scope_a</code> is the (both direct and indirect) parent
	 * <code>scope_b</code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public static boolean isNested(String scope_a, String scope_b) {
		if(scope_a.equals(scope_b))	return false;
		return scope_b.startsWith(scope_a);
	}
	
	/**
	 * Check is <code>scope_a</code> is either (both direct and indirect) parent
	 * <code>scope_b</code>, or <code>scope_a</code> is same as <code>scope_b
	 * </code>
	 * @param scope_a
	 * @param scope_b
	 * @return
	 */
	public static boolean isNestedOrEqual(String scope_a, String scope_b) {
		Preconditions.checkNotNull(scope_a);
		Preconditions.checkNotNull(scope_b);
		if(scope_a.equals(scope_b))	return true;
		return scope_b.startsWith(scope_a);
	}

	private static String getTopScope(Collection<String> elemScopeNames) {
		Preconditions.checkArgument(elemScopeNames.size() > 0);
		Iterable<String> notNullElemScopeNames = Iterables.filter(elemScopeNames, 
				new Predicate<String>() {
					@Override
					public boolean apply(String str) {
						return str != null;
					}
		});
		
		
		Iterator<String> elemScopeNameItr = notNullElemScopeNames.iterator();
		if(!elemScopeNameItr.hasNext()) return null;
		
		String rootScope = elemScopeNameItr.next();
		
		Function<String, String> getParentScope = new Function<String, String>() {
			@Override
	    public String apply(String scopeName) {
		    int index = scopeName.lastIndexOf(Identifiers.SCOPE_INFIX);
		    return scopeName.substring(0, index);
	    }
		};
		
		while(elemScopeNameItr.hasNext()) {
			String elemScope = elemScopeNameItr.next();
			if(isNestedOrEqual(rootScope, elemScope)) continue;
			
			if(isNested(elemScope, rootScope)) {
				rootScope = elemScope; continue;
			}
			
			while(!isNestedOrEqual(rootScope, elemScope)) {
				rootScope = getParentScope.apply(rootScope);
			}
		}
		
		return rootScope;
	}
}
