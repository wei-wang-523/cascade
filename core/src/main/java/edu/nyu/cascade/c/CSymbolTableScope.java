package edu.nyu.cascade.c;

import xtc.util.SymbolTable.Scope;

public final class CSymbolTableScope {
	
	public static boolean isNested(Scope scope_a, Scope scope_b) {
		if(scope_a.isRoot()) {
			if (scope_b.isRoot()) return false;
			return true;
		}
		
		String name_a = scope_a.getQualifiedName();
		String name_b = scope_b.getQualifiedName();
		return name_b.startsWith(name_a);
	}
}
