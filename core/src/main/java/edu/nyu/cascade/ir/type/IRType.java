package edu.nyu.cascade.ir.type;

import java.util.List;

import xtc.tree.Node;
import xtc.type.FunctionT;
import xtc.type.StructT;
import xtc.type.Type;
import xtc.type.UnionT;
import xtc.type.VariableT;

import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;

/**
 * Only used to choose the appropriate encoding: - integer encoding - pointer
 * encoding - boolean encoding
 * 
 * @author weiwang
 *
 */
public abstract class IRType {
	public static enum Kind {
		ARRAY, ASYNC_CHANNEL, BOOLEAN, CHANNEL, INTEGER, PROCESS, FUNCTION, RANGE, VOID, POINTER, STRUCT, LABEL, UNION, UNKNOWN;
	}

	public abstract Kind getKind();

	/**
	 * Get the kind of type corresponding to the type of <code>srcNode</code>
	 * 
	 * @param srcNode
	 * @return
	 */
	public static IRType getIRType(Node srcNode) {
		Type type = CType.getType(srcNode);
		return getIRType(type);
	}

	/**
	 * Get the kind of type corresponding to the type of <code>srcNode</code>
	 * 
	 * @param srcNode
	 * @return
	 */
	public static IRType getIRType(Type type) {
		if (type.resolve().isBoolean())
			return IRBooleanType.getInstance();

		if (type.resolve().isInteger())
			return IRIntegerType.create(type);

		if (type.resolve().isPointer())
			return IRPointerType.getInstance();

		if (type.resolve().isVoid())
			return IRVoidType.getInstance();

		if (type.resolve().isLabel())
			return IRLabelType.getInstance();

		if (type.resolve().isArray()) {
			IRType cellType = getIRType(type.resolve().toArray().getType());
			IRType indexType = IRIntegerType.getInstance();
			return IRArrayType.getInstance(indexType, cellType);
		}

		if (type.resolve().isFunction()) {
			FunctionT funcType = type.resolve().toFunction();
			List<IRType> paramTypes = Lists.newArrayList();
			for (Type paramType : funcType.getParameters()) {
				paramTypes.add(getIRType(paramType));
			}
			IRType returnType = getIRType(funcType.getResult());
			return IRFunctionType.getInstance(paramTypes, returnType);
		}

		if (type.resolve().isStruct()) {
			StructT structType = type.resolve().toStruct();
			int count = structType.getMemberCount();
			if (count < 0) { // none members
				return IRStructType.create(structType.getName(), null, null);
			} else {
				List<IRType> memTypes = Lists.newArrayListWithCapacity(count);
				List<String> memNames = Lists.newArrayListWithCapacity(count);
				for (VariableT memType : structType.getMembers()) {
					memTypes.add(getIRType(memType.resolve()));
					memNames.add(memType.getName());
				}
				return IRStructType.create(structType.getName(), memNames, memTypes);
			}
		}

		if (type.resolve().isUnion()) {
			UnionT structType = type.resolve().toUnion();
			List<IRType> memTypes = Lists.newArrayList();
			List<String> memNames = Lists.newArrayList();
			for (VariableT memType : structType.getMembers()) {
				memTypes.add(getIRType(memType.resolve()));
				memNames.add(memType.getName());
			}
			return IRUnionType.create(structType.getName(), memNames, memTypes);
		}

		return IRUnknownType.create(type);
	}
}
