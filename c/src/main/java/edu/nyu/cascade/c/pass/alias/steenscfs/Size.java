package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Map;

import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.util.HashCodeUtil;

class Size {
	enum Kind {
		NUMBER, TOP, BOT
	}

	private static Map<Long, Size> map = Maps.newHashMap();

	private static Size botInstance = new Size(Kind.BOT, 0);

	private final Kind kind;
	private final long value;

	private Size(Kind kind, long value) {
		this.kind = kind;
		this.value = value;
	}

	/**
	 * TODO: create symbolic size like unbounded array
	 * 
	 * @return
	 */

	/**
	 * Get the TOP size, indicating the rest of a memory object and is used in
	 * types describing objects of different sizes.
	 * 
	 * @return
	 */
	static Size getTop(long value) {
		return new Size(Kind.TOP, value);
	}

	/**
	 * Get the BOT size
	 * 
	 * @return
	 */
	static Size getBot() {
		return botInstance;
	}

	/**
	 * Create a numeric size with value <code>size</code>
	 * 
	 * @param size
	 * @return
	 */
	private static Size createNum(long size) {
		Preconditions.checkArgument(size >= 0);
		if (size == 0)
			return getBot();
		if (map.containsKey(size))
			return map.get(size);
		Size res = new Size(Kind.NUMBER, size);
		map.put(size, res);
		return res;
	}

	/**
	 * Create a numeric size for type <code>type</code>
	 * 
	 * @param type
	 * @return
	 */
	static Size createForType(Type type) {
		Preconditions.checkNotNull(type);
		type = CType.getCellType(type);
		if (type.isInternal()) {
			return Size.getTop(0);
		} else if (CType.isScalar(type)) {
			return createNum(CType.getInstance().getSize(type));
		} else if (CType.isStructOrUnion(type)) {
			return createNum(CType.getInstance().getSize(type));
		} else { // Composite type, void type and function type
			return Size.getBot();
		}
	}

	/**
	 * Calculate the partial order relations between <code>s1</code> and
	 * <code>s2</code>
	 */
	static boolean isLessThan(Size s1, Size s2) {
		if (s1.equals(s2))
			return true;
		if (s1.kind.equals(Kind.BOT))
			return true;
		return s2.kind.equals(Kind.TOP);
	}

	/**
	 * Compute the least-upper-bound of two size <code>s1</code> and
	 * <code>s2</code>
	 */
	static Size getLUB(Size s1, Size s2) {
		if (s1.equals(s2)) {
			return s1;
		}
		
		if (s1.isBottom()) {
			return s2;
		} else if (s2.isBottom()) {
			return s1;
		} else {
			return getTop(Math.max(s1.getValue(), s2.getValue()));
		}
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("Size ");
		switch (kind) {
		case NUMBER:
			sb.append(value);
			break;
		case BOT:
			sb.append("BOT").append(':').append(value);
			break;
		default:
			sb.append("TOP").append(':').append(value);
			break;
		}
		return sb.toString();
	}

	@Override
	public int hashCode() {
		return HashCodeUtil.hash(HashCodeUtil.hash(HashCodeUtil.SEED, kind), value);
	}

	long getValue() {
		return value;
	}

	boolean isTop() {
		return kind.equals(Kind.TOP);
	}

	boolean isBottom() {
		return kind.equals(Kind.BOT);
	}

	boolean isNumber() {
		return kind.equals(Kind.NUMBER);
	}
}
