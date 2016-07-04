package edu.nyu.cascade.c;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import edu.nyu.cascade.util.IOUtils;
import xtc.Constants;

public final class CScopeAnalyzer {
	private static String FUNCTION_WRAPPER = "function(";
	private static String ROOT_SCOPE = "";

	private static List<String> scopeStack = Lists.newArrayList(ROOT_SCOPE);
	private static String lastScope = "";

	public static void reset() {
		scopeStack.clear();
		scopeStack.add(ROOT_SCOPE);
	}

	public static void popScope() {
		lastScope = scopeStack.remove(0);
		IOUtils.debug().pln("Pop " + lastScope);
	}

	public static void pushScope(String scopeName) {
		scopeStack.add(0, scopeName);
		IOUtils.debug().pln("Push " + scopeName);
	}

	public static String getCurrentScope() {
		Preconditions.checkArgument(!scopeStack.isEmpty());
		return scopeStack.get(0);
	}

	public static String getLastScope() {
		return lastScope;
	}

	public static ImmutableList<String> getScopes() {
		return ImmutableList.copyOf(scopeStack);
	}

	/**
	 * Get the root scope name, which is set to be empty string
	 * 
	 * @return empty string
	 */
	public static String getRootScopeName() {
		return ROOT_SCOPE;
	}

	/**
	 * De-qualified scope name
	 */
	public static String getLastScopeName(String scopeName) {
		int lastIndexOfDot = scopeName.lastIndexOf(Constants.QUALIFIER) + 1;
		String currentScopeName = scopeName.substring(lastIndexOfDot);
		if (currentScopeName.startsWith(FUNCTION_WRAPPER)) {
			int startIndex = FUNCTION_WRAPPER.length();
			int endIndex = currentScopeName.length() - 1;
			currentScopeName = currentScopeName.substring(startIndex, endIndex);
		}
		return currentScopeName;
	}
}
