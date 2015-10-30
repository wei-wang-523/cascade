package edu.nyu.cascade.c;

//import java.util.Deque;
//import java.util.Map;
//
//import com.google.common.collect.Maps;
//import com.google.common.collect.Queues;
//
//import edu.nyu.cascade.util.IOUtils;

public final class CScopeAnalyzer {
	private static String FUNCTION_WRAPPER = "function(";
	
//	private static Deque<String> scopeStack = Queues.newArrayDeque();
//	private static Map<String, Deque<Long>> scopeMap = Maps.newHashMap();
//	private static long id = 0;

	public static void reset() {
//		id = 0;
//		scopeStack.clear();
//		scopeMap.clear();
	}
	
	public static void popScope() {
//		String scopeName = scopeStack.pop();
//		long currId = scopeMap.get(scopeName).pop();
//		IOUtils.debug().pln("Pop " + scopeName + currId);
	}
	
	public static void pushScope(String scopeName) {
//		scopeStack.push(scopeName);
//		if(!scopeMap.containsKey(scopeName)) {
//			scopeMap.put(scopeName, Queues.<Long>newArrayDeque());
//		};
//		scopeMap.get(scopeName).push(++id);
//		IOUtils.debug().pln("Push " + scopeName + id);
	}
	
	/**
	 * Get the root scope name, which is set to be empty string
	 * @return empty string
	 */
	public static String getRootScopeName() {
		return "";
	}
	
	/**
	 * De-qualified scope name
	 */
	public static String getCurrentScopeName(String scopeName) {
		int lastIndexOfDot = scopeName.lastIndexOf('.') + 1;
		String currentScopeName = scopeName.substring(lastIndexOfDot);
		if(currentScopeName.startsWith(FUNCTION_WRAPPER)) {
			int startIndex = FUNCTION_WRAPPER.length();
			int endIndex = currentScopeName.length() - 1;
			currentScopeName = currentScopeName.substring(startIndex, endIndex);
		}
		return currentScopeName;
	}
}
