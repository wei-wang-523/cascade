package edu.nyu.cascade.c.pass.alias.dsa;

import org.apache.commons.lang.builder.HashCodeBuilder;

import com.google.common.base.Preconditions;

import xtc.type.Type;

public final class Region implements Comparable<Region> {
	DSNode N;
	Type type;
	long offset;
	long length;
	
	boolean singleton, allocated, bytewise, incomplete, complicated, collapsed;
	
	Region(DSNode rep, Type type, long offset, long length) {
		Preconditions.checkNotNull(rep);
		this.N = rep;
		this.type = type;
		this.offset = offset;
		this.length = length;
	}
	
	boolean isSingleton() { return singleton; };
	
	boolean isAllocated() { return allocated; };
	
	boolean bytewiseAccess() { return bytewise; }
	
	Type getType() { return type; }

	boolean isDisjoint(long offset, long length) {
		return this.offset + this.length <= offset  || 
				offset + length <= this.offset;
	}
	
	void merge(Region R) {
		boolean collapse = type != R.type;
		long low = Math.min(offset, R.offset);
		long high = Math.max(offset + length, R.offset + R.length);
		offset = low;
		length = high - low;
		singleton = singleton && R.singleton;
		allocated = allocated || R.allocated;
		bytewise = bytewise || R.bytewise || collapse;
		incomplete = incomplete || R.incomplete;
		complicated = complicated || R.complicated;
		collapsed = collapsed || R.collapsed;
		type = (bytewise || collapse) ? null : type;
	}
	
	boolean overlaps(Region R) {
		return (incomplete && R.incomplete)
				|| (complicated && R.complicated)
				|| (N == R.N
				&& (collapsed || !isDisjoint(R.offset, R.length)));
	}
	
	@Override
	public String toString() {
		//TODO: identify the representative
		StringBuilder sb = new StringBuilder().append(N.getID() + "[")
				.append(offset).append(',')
				.append(offset + length).append("]{");
		if (singleton) 	sb.append('S');
		if (bytewise) 	sb.append('B');
		if (allocated)	sb.append('A');
		sb.append('}');
		return sb.toString();
	}

	@Override
	public int compareTo(Region o) {
		if (N.equals(o.N)) {
			if (offset == o.offset) {
				return Long.compare(length, o.length);
			}
			return Long.compare(offset, o.offset);
		}
		
		return N.compareTo(o.N);
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Region)) return false;
		Region otherReg = (Region) o;
		if (!otherReg.N.equals(N))  return false;
		if (otherReg.offset != offset) return false;
		if (otherReg.length != length) return false;
		return true;
	}
	
	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37)
				.append(N)
				.append(offset)
				.append(length).hashCode();
	}
}
