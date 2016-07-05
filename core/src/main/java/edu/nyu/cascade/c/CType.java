package edu.nyu.cascade.c;

import java.util.List;

import xtc.tree.Node;
import xtc.type.ArrayT;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.StructOrUnionT;
import xtc.type.Type;
import xtc.type.Type.Tag;
import xtc.type.VariableT;
import xtc.type.VoidT;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.util.Preferences;

/**
 * An auxiliary C type analyzer for C programs.
 *
 */
public final class CType {
	public static final String TYPE = xtc.Constants.TYPE;
	public static final String SCOPE = xtc.Constants.SCOPE;

	private static final CType instance = new CType();

	public static CType getInstance() {
		return instance;
	}

	public static boolean hasType(Node node) {
		return node.hasProperty(TYPE);
	}

	public static boolean hasScope(Node node) {
		return node.hasProperty(SCOPE);
	}

	public static Type getType(Node node) {
		Preconditions.checkArgument(hasType(node));
		return (Type) node.getProperty(TYPE);
	}

	public static String getScopeName(Node node) {
		Preconditions.checkArgument(node.hasProperty(SCOPE));
		return node.getStringProperty(SCOPE);
	}

	public static Type getUnitType() {
		return NumberT.U_CHAR;
	}

	public static Type getVoidType() {
		return VoidT.TYPE;
	}

	public static Type getArrayCellType(Type type) {
		Preconditions.checkArgument(Tag.ARRAY.equals(type.tag()));
		Type resType = type.resolve();
		do {
			resType = resType.toArray().getType().resolve();
		} while (resType.isArray());
		return resType;
	}

	public static boolean isUnsigned(Type type) {
		type = type.resolve();
		if (!type.isNumber())
			return true;
		switch (type.toNumber().getKind()) {
		case BYTE:
		case U_CHAR:
		case U_INT:
		case U_LONG:
		case U_LONG_LONG:
		case U_SHORT:
			return true;
		default:
			return false;
		}
	}

	public static boolean isScalar(Type type) {
		switch (type.tag()) {
		case BOOLEAN:
		case INTEGER:
		case FLOAT:
		case POINTER:
			return true;
		default:
			return false;
		}
	}

	public static boolean isArithmetic(Type type) {
		switch (type.tag()) {
		case BOOLEAN:
		case INTEGER:
		case FLOAT:
			return true;
		default:
			return false;
		}
	}

	public static boolean isStructOrUnion(Type type) {
		switch (type.tag()) {
		case STRUCT:
		case UNION:
			return true;
		default:
			return false;
		}
	}

	private final C cops = Preferences.isSet(Preferences.OPTION_M32) ? new C32()
			: new C64();

	public C c() {
		return cops;
	}

	public boolean equal(Type lhs, Type rhs) {
		return cops.equal(lhs, rhs);
	}

	public Type convert(Type lhsType, Type rhsType) {
		if (lhsType.resolve().isPointer() || !cops.isScalar(lhsType) || rhsType
				.resolve().isPointer() || !cops.isScalar(rhsType))
			return PointerT.TO_VOID;

		return cops.convert(lhsType, rhsType);
	}

	public Type compose(Type lhsType, Type rhsType) {
		return cops.compose(lhsType, rhsType, false);
	}

	public int getWordSize() {
		if (Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return getByteSize();

		if (Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE))
			return Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE);

		return (int) cops.getWidth(NumberT.INT);
	}

	public Type pointerize(Type type) {
		return cops.pointerize(type);
	}

	public Type typeInteger(String literal) {
		return cops.typeInteger(literal);
	}

	public Type typeCharacter(String literal) {
		return cops.typeCharacter(literal);
	}

	public long getWidth(Type type) {
		long size = getSize(type);
		if (Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return cops.toWidth(size);
		else {
			return size * cops.getWidth(NumberT.INT);
		}
	}

	public long toWidth(long size) {
		return cops.toWidth(size);
	}

	/**
	 * Get the size of <code>type</code>
	 * 
	 * @param type
	 * @return 0 if the array type without size:
	 *         <code>extern char *sys_errlist[];</code>
	 */
	public long getSize(Type type) {
		if (Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return cops.getSize(type);
		else
			return getSizeSimple(type);
	}

	private long getSizeSimple(Type type) {
		switch (type.resolve().tag()) {
		case BOOLEAN:
		case ENUM:
		case ENUMERATOR:
		case FLOAT:
		case INTEGER:
		case POINTER:
		case FUNCTION:
			return 1;
		case STRUCT: {
			List<VariableT> members = type.resolve().toStruct().getMembers();
			if (members == null)
				return 0;
			long size = 0;

			for (VariableT member : members)
				size += getSizeSimple(member);

			return size;
		}
		case ARRAY: {
			ArrayT arrayT = type.resolve().toArray();
			long length = arrayT.getLength();
			long cellSize = getSizeSimple(arrayT.toArray().getType());
			return length * cellSize;
		}
		case UNION: {
			List<VariableT> members = type.resolve().toUnion().getMembers();
			if (members == null)
				return 0;
			long size = 0;

			for (VariableT member : members)
				size = Math.max(size, getSizeSimple(member));

			return size;
		}
		case VOID:
			return 0;
		default:
			throw new IllegalArgumentException("Unknown size of type: " + type);
		}
	}

	public long getOffset(Type type, String name) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve()
				.isUnion());

		if (Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return cops.getOffset(type.resolve().toStructOrUnion(), name);
		else
			return getOffsetSimple(type, name);
	}

	private long getOffsetSimple(Type type, String name) {
		StructOrUnionT suType = type.resolve().toStructOrUnion();
		if (suType.isStruct()) {
			final List<VariableT> members = suType.getMembers();
			final int memberCount = members.size();
			long size = 0;
			for (int i = 0; i < memberCount; i++) {
				// Process the member.
				final VariableT var = members.get(i);

				if (null != name) {
					if (var.hasName(name)) {
						return size;
					} else if (!var.hasName()) {
						final long offset = getOffsetSimple(var.toStructOrUnion(), name);
						if (-1 != offset)
							return size + offset;
					}
				}

				size += getSizeSimple(var);
			}

			return size;
		} else {
			for (VariableT var : suType.getMembers()) {
				if (var.hasName(name)) {
					return 0;
				} else if (!var.hasName() && !var.hasWidth()) {
					final long offset = getOffset(var.toStructOrUnion(), name);
					if (-1 != offset)
						return offset;
				}
			}
			return -1;
		}
	}

	public static boolean isVarLengthArray(Type type) {
		type = type.resolve();
		while (type.isArray()) {
			if (type.toArray().isVarLength())
				return true;
			type = type.toArray().getType().resolve();
		}
		return false;
	}

	public final int getByteSize() {
		return cops.BYTE_SIZE();
	}
}
