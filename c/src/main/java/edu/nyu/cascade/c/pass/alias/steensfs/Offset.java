package edu.nyu.cascade.c.pass.alias.steensfs;

import java.math.BigInteger;
import java.util.Collection;

import com.google.common.collect.Sets;

class Offset {

	enum Kind {
		ZERO, UNKNOWN
	}

	private static BigInteger nextId = BigInteger.ZERO;

	private final BigInteger id;

	private Kind kind;

	private final Collection<ECR> collapse = Sets.newHashSet();
	private final Collection<Offset> unknown = Sets.newLinkedHashSet();

	Offset(Kind kind) {
		this.kind = kind;

		this.id = nextId;
		nextId = nextId.add(BigInteger.ONE);
	}

	static Offset createZero() {
		return new Offset(Kind.ZERO);
	}

	@Override
	public String toString() {
		return kind.toString();
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

	void addCollapse(ECR ecr) {
		collapse.add(ecr);
	}

	void addCollapses(Collection<ECR> ecrs) {
		collapse.addAll(ecrs);
	}

	void clearCollapse() {
		collapse.clear();
	}

	Collection<ECR> getCollapse() {
		return collapse;
	}

	void addUnknown(Offset off) {
		if (off == null)
			return;

		unknown.add(off);
	}

	void addUnknowns(Collection<Offset> offs) {
		for (Offset off : offs) {
			addUnknown(off);
		}
	}

	void clearUnknown() {
		unknown.clear();
	}

	Collection<Offset> getUnknown() {
		return unknown;
	}
}