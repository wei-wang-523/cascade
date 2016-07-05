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

	private static Size topInstance = new Size(Kind.TOP);
	private static Size botInstance = new Size(Kind.BOT);

	private final Kind kind;
	private long value = 0;

	private Size(Kind kind) {
		this.kind = kind;
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
	static Size getTop() {
		return topInstance;
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
	private static Size create(long size) {
		Preconditions.checkArgument(size >= 0);
		if (size == 0)
			return getBot();
		if (map.containsKey(size))
			return map.get(size);
		Size res = new Size(Kind.NUMBER);
		res.value = size;
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
		switch (type.tag()) {
		case FUNCTION:
		case VOID:
			return getBot();
		default:
			return create(CType.getInstance().getSize(type));
		}
	}

	/**
	 * Calculate the partial order relations between <code>s1</code> and
	 * <code>s2</code>
	 * 
	 * @param s1
	 * @param s2
	 * @return
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
	 * 
	 * @param s1
	 * @param s2
	 * @return
	 */
	static Size getLUB(Size s1, Size s2) {
		if (isLessThan(s1, s2))
			return s2;
		if (isLessThan(s2, s1))
			return s1;
		return topInstance;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("Size ");
		switch (kind) {
		case NUMBER:
			sb.append(value);
			break;
		case BOT:
			sb.append("BOT");
			break;
		default:
			sb.append("TOP");
			break;
		}
		return sb.toString();
	}

	@Override
	public int hashCode() {
		return HashCodeUtil.hash(HashCodeUtil.hash(HashCodeUtil.SEED, kind), value);
	}

	long getValue() {
		Preconditions.checkArgument(kind.equals(Kind.NUMBER));
		return value;
	}

	Kind getKind() {
		return kind;
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
