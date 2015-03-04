package edu.nyu.cascade.c.preprocessor.steensfs;

import java.util.Map;

import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.util.HashCodeUtil;

class Size {
	enum Kind {
		NUMBER,
		TOP,
		BOT
	}
	
	private static Map<Long, Size> map = Maps.newHashMap();
	
	private static Size topInstance, botInstance;
	
	private final Kind kind;
	private long value = 0;
	
	private Size(Kind kind) {
		this.kind = kind;
	}
	
	/**
	 * TODO: create symbolic size like unbounded array
	 * @return
	 */
	
	/**
	 * Get the size <code>T</code>, indicating the rest of 
	 * a memory object and is used in types describing objects 
	 * of different sizes.
	 * @return
	 */
	static Size getTop() {
		if(topInstance != null)	return topInstance;
		topInstance = new Size(Kind.TOP);
		return topInstance;
	}
	
	/**
	 * Get the size <code>T</code>, indicating the rest of 
	 * a memory object and is used in types describing objects 
	 * of different sizes.
	 * @return
	 */
	static Size getBot() {
		if(botInstance != null)	return botInstance;
		botInstance = new Size(Kind.BOT);
		return botInstance;
	}
	
	/**
	 * Create a numeric size with value <code>size</code>
	 * @param size
	 * @return
	 */
	static Size create(long size) {
		Preconditions.checkArgument(size >= 0);
		if(map.containsKey(size)) return map.get(size);
		Size res = new Size(Kind.NUMBER);
		res.value = size;
		map.put(size, res);
		return res;
	}
	
	/**
	 * Create a numeric size for type <code>type</code>
	 * @param type
	 * @return
	 */
	static Size createForType(Type type) {
		Preconditions.checkNotNull(type);
		return create(CType.getInstance().getSize(type));
	}
	
	/**
	 * Calculate the partial order relations between
	 * <code>s1</code> and <code>s2</code>
	 * @param s1
	 * @param s2
	 * @return
	 */
	static boolean isLessThan(Size s1, Size s2) {
		if(s1.equals(s2)) return true;
		if(s1.equals(getBot())) return true;
		return s2.equals(getTop());
	}

	/**
	 * Compute the least-upper-bound of two size
	 * <code>s1</code> and <code>s2</code>
	 * @param s1
	 * @param s2
	 * @return
	 */
	static Size getLUB(Size s1, Size s2) {
		if(isLessThan(s1, s2)) return s2;
		if(isLessThan(s2, s1)) return s1;
		return getTop();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("Size ");
		switch(kind) {
		case NUMBER:
			return sb.append(value).toString();
		case BOT:
			return sb.append('\u22A5').toString();
		default:
			return sb.append('\u22A4').toString();
		}
	}
	
	@Override
	public int hashCode() {
		return HashCodeUtil.hash(
				HashCodeUtil.hash(HashCodeUtil.SEED, kind), value);
	}
	
	long getValue() {
		Preconditions.checkArgument(kind.equals(Kind.NUMBER));
		return value;
	}
	
	Kind getKind() {
		return kind;
	}
	
	boolean isNumber() {
		return kind.equals(Kind.NUMBER);
	}
}
