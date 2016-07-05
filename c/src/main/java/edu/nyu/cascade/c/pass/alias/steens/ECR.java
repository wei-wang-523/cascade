package edu.nyu.cascade.c.pass.alias.steens;

import java.math.BigInteger;
import java.util.Collection;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import edu.nyu.cascade.util.UnionFind;

/**
 * A class which represents an Equivalence Class Representative (ECR) with
 * associated type information.
 * 
 * The ECR is an extension of partition of union/find data structure.
 * 
 * @author Wei
 *
 */

public final class ECR extends UnionFind.Partition {

	private static final long serialVersionUID = -8706921066542618766L;
	private static BigInteger nextId = BigInteger.ONE;

	/**
	 * A list of 'pending' joins for this ECR. We make conditional joins, if the
	 * type for this variable is BOTTOM. Then, if the type for this variable
	 * changes, we need to update the types of all the ECRs on the pending list.
	 */
	private Collection<ECR> pending = Sets.newHashSet();

	private ValueType type;
	private BigInteger id;

	private ECR(ValueType _type) {
		super();
		type = _type;

		id = nextId;
		nextId = nextId.add(BigInteger.ONE);
	}

	static ECR createBottom() {
		return new ECR(ValueType.bottom());
	}

	static ECR create(ValueType type) {
		return new ECR(type);
	}

	/**
	 * @return the type associated with the ECR.
	 */
	ValueType getType() {
		return type;
	}

	void setType(ValueType _type) {
		type = _type;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("(ECR ").append(id).append(
				" : ").append(type).append(')');

		return sb.toString();
	}

	int getId() {
		return id.intValue();
	}

	/**
	 * @return the pending with the ECR
	 */
	Collection<ECR> getPendings() {
		return pending;
	}

	void clearPending() {
		pending.clear();
	}

	boolean addPendings(Collection<ECR> newPendings) {
		Preconditions.checkNotNull(newPendings);
		return pending.addAll(newPendings);
	}

	boolean addPending(ECR newPending) {
		return pending.add(newPending);
	}
}
