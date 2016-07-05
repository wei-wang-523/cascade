package edu.nyu.cascade.ir.impl;

import xtc.type.Type;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.type.IRType;

public class VarInfoFactory {

	/**
	 * Create a variable info
	 * 
	 * @return
	 */
	public static IRVarInfo createVarInfo(String scope, String name,
			Type srcType) {
		Preconditions.checkNotNull(scope);
		Preconditions.checkArgument(srcType.isSealed() || srcType.hasScope()
				&& scope.equals(srcType.getScope()) || srcType.hasScope() && srcType
						.getScope().equals(CAnalyzer.EXTERN_PATH));
		return new VarInfo(srcType.getScope(), name, IRType.getIRType(srcType),
				srcType);
	}
}
