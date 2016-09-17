package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.math.BigInteger;
import java.util.Collection;

import com.google.common.collect.Sets;

import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind.Partition;

final class ECR extends Partition {

	private static final long serialVersionUID = 5892848983695588745L;
	private static BigInteger nextId = BigInteger.ZERO;

	private final BigInteger _id;
	private ValueType _type;

	final private Collection<Pair<Size, ECR>> _ccjoin = Sets.newLinkedHashSet();
	final private Collection<ECR> _cjoin = Sets.newLinkedHashSet();

	ECR(ValueType type) {
		super();
		_type = type;

		_id = nextId;
		nextId = nextId.add(BigInteger.ONE);
	}

	static ECR createBottom() {
		return new ECR(ValueType.bottom());
	}

	@Override
	public int hashCode() {
		return super.hashCode();
	}

	ValueType getType() {
		return _type;
	}

	void setType(ValueType type) {
		_type = type;
	}

	@Override
	public String toString() {
		return "ECR " + _id;
	}

	int getId() {
		return _id.intValue();
	}

	void addCCjoin(Size size, ECR other) {
		_ccjoin.add(Pair.of(size, other));
	}

	void addCjoin(ECR other) {
		_cjoin.add(other);
	}

	void addCCjoins(Collection<Pair<Size, ECR>> ccjoins) {
		_ccjoin.addAll(ccjoins);
	}

	void addCjoins(Collection<ECR> cjoins) {
		_cjoin.addAll(cjoins);
	}

	Collection<Pair<Size, ECR>> getCCjoins() {
		return _ccjoin;
	}

	Collection<ECR> getCjoins() {
		return _cjoin;
	}

	void clearCCjoins(Collection<Pair<Size, ECR>> ccjoins) {
		_ccjoin.removeAll(ccjoins);
	}

	void clearCjoins(Collection<ECR> cjoins) {
		_cjoin.removeAll(cjoins);
	}
}
