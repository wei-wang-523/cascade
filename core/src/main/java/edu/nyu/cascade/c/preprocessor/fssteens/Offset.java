package edu.nyu.cascade.c.preprocessor.fssteens;

import java.math.BigInteger;
import java.util.Collection;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

class Offset {

	enum Kind {
		ZERO,
		UNKNOWN
	}
	
	private static BigInteger nextId = BigInteger.ZERO;
	
	private final BigInteger id;
	
	private Kind kind;
	
	final private Collection<Offset> makeunknown;
	final private Collection<ECR> collapse;
	
	Offset(Kind kind) {
		this.kind = kind;
		this.id = nextId;
		nextId = nextId.add(BigInteger.ONE);
		
		this.makeunknown = Sets.newHashSet();
		this.collapse = Sets.newHashSet();
	}
	
	static Offset createZero() {
		return new Offset(Kind.ZERO);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Off ").append(kind);
		return sb.toString();
	}
	
	static Offset createUnknown() {
		return new Offset(Kind.UNKNOWN);
	}
	
	boolean isZero() {
	  return kind.equals(Kind.ZERO);
	}
	
	boolean isUnknown() {
		return kind.equals(Kind.UNKNOWN);
	}
	
	BigInteger getId() {
		return id;
	}

	Kind getKind() {
		return kind;
	}
	
	void setKind(Kind kind) {
		this.kind = kind;
	}
	
	void addMakeUnknown(Offset o) {
		Preconditions.checkArgument(!o.equals(this));
		makeunknown.add(o);
	}
	
	void addCollapse(ECR ecr) {
		collapse.add(ecr);
	}
	
	void addCollapses(Collection<ECR> ecrs) {
		collapse.addAll(ecrs);
	}
	
	void addMakeUnknowns(Collection<Offset> offsets) {
		for(Offset off : offsets) {
			/* avoid make unknown loop o1.makeunknown(o2), o2.makeunknown(o1); */
			if(off.equals(this)) continue;
			makeunknown.add(off);
		}
	}
	
	void clearCollapse() {
		collapse.clear();
	}
	
	void cleanMakeunknown() {
		makeunknown.clear();
	}
	
	Collection<ECR> getCollapse() {
		return collapse;
	}
	
	Collection<Offset> getMakeUnknown() {
		return makeunknown;
	}
}