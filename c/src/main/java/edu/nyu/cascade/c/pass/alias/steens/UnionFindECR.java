package edu.nyu.cascade.c.pass.alias.steens;

import java.util.Collection;
import java.util.Iterator;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.alias.steens.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

class UnionFindECR {
	UnionFind<IRVar> uf;

	private UnionFindECR() {
		uf = UnionFind.create();
	}

	static UnionFindECR create() {
		return new UnionFindECR();
	}

	void reset() {
		uf.reset();
	}

	/**
	 * Add <code>var</code> into union find
	 * 
	 * @param var
	 */
	void add(VarImpl var) {
		uf.add(var, var.getECR());
	}

	/**
	 * Add <code>vars</code> into union find
	 * 
	 * @param vars
	 */
	void addAll(Iterable<VarImpl> vars) {
		for (VarImpl var : vars) {
			uf.add(var, var.getECR());
		}
	}

	/**
	 * Conditional join two ECRs <code>e1</code> and <code>e2</code>
	 * 
	 * @param e1
	 * @param e2
	 */
	void cjoin(ECR e1, ECR e2) {
		if (e1.equals(e2))
			return;

		switch (getType(e2).getKind()) {
		case BOTTOM:
			addPending(e2, e1);
			break;
		default:
			join(e1, e2);
			break;
		}
	}

	/**
	 * Join the types represented by <code>e1</code> and <code>e2</code>
	 * 
	 * @param e1
	 * @param e2
	 */
	void join(ECR e1, ECR e2) {
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		Collection<ECR> pending1 = getPendings(e1);
		Collection<ECR> pending2 = getPendings(e2);

		uf.union(e1, e2);
		ECR root = findRoot(e1);

		switch (t1.getKind()) {
		case BOTTOM: {
			root.setType(t2);

			switch (t2.getKind()) {
			case BOTTOM: {
				Collection<ECR> pendings = Sets.newHashSet();
				pendings.addAll(pending1);
				pendings.addAll(pending2);
				root.addPendings(pendings);
				break;
			}
			default:
				for (ECR x : pending1)
					join(root, x);
				break;
			}
			break;
		}

		default: {
			switch (t2.getKind()) {
			case BOTTOM:
				root.setType(t1);
				for (ECR x : pending2)
					join(root, x);
				break;
			default: {
				ValueType t = unify(t1, t2);
				root.setType(t);
				break;
			}
			}
			break;
		}
		}
	}

	/**
	 * Set the type of the ECR @param e to @param type
	 */
	void setType(ECR e, ValueType type) {
		ECR root = findRoot(e);
		root.setType(type);
		for (ECR x : root.getPendings()) {
			join(root, x);
		}
		root.clearPending();
	}

	/**
	 * Get the type of the ECR <code>e</code>
	 * 
	 * @param e
	 */
	ValueType getType(ECR e) {
		ECR root = findRoot(e);
		return root.getType();
	}

	/**
	 * Get the root of ECR <code>e</code>
	 * 
	 * @param e
	 * @return
	 */
	ECR findRoot(ECR e) {
		return (ECR) e.findRoot();
	}

	/**
	 * Get the snapshot of union find
	 */
	ImmutableMap<ECR, Collection<IRVar>> snapshot() {
		SetMultimap<Partition, IRVar> map = uf.snapshot();
		ImmutableMap.Builder<ECR, Collection<IRVar>> builder = ImmutableMap
				.builder();
		for (Partition ecr : map.asMap().keySet()) {
			builder.put((ECR) ecr.findRoot(), ImmutableSet.copyOf(map.asMap().get(
					ecr)));
		}
		return builder.build();
	}

	Collection<IRVar> getEquivClass(ECR key) {
		return uf.getEquivClass(key);
	}

	ECR getLoc(ECR ecr) {
		ValueType ecrType = getType(ecr);
		switch (ecrType.getKind()) {
		case BOTTOM:
			ValueType newRefType = ValueType.ref(ECR.createBottom(), ECR
					.createBottom());
			setType(ecr, newRefType);
			return newRefType.asRef().getLocation();
		case REF:
			return ecrType.asRef().getLocation();
		default:
			throw new IllegalArgumentException();
		}
	}

	ECR getFunc(ECR ecr) {
		ValueType ecrType = getType(ecr);
		switch (ecrType.getKind()) {
		case BOTTOM:
			ValueType newRefType = ValueType.ref(ECR.createBottom(), ECR
					.createBottom());
			setType(ecr, newRefType);
			return newRefType.asRef().getFunction();
		case REF:
			return ecrType.asRef().getFunction();
		default:
			throw new IllegalArgumentException();
		}
	}

	void assign(ECR lhs, ECR rhs) {
		ValueType lhs_type = getType(lhs);
		ValueType rhs_type = getType(rhs);

		ValueTypeKind lKind = lhs_type.getKind();
		ValueTypeKind rKind = rhs_type.getKind();

		switch (lKind) {
		case BOTTOM: {
			switch (rKind) {
			case REF: {
				setType(lhs, rhs_type);
				break;
			}
			default:
				break;
			}
			break;
		}
		case REF: {
			switch (rKind) {
			case BOTTOM: {
				setType(rhs, lhs_type);
				break;
			}
			case REF: {
				ECR lhsLoc = lhs_type.asRef().getLocation();
				ECR rhsLoc = rhs_type.asRef().getLocation();
				cjoin(lhsLoc, rhsLoc);

				ECR lhsFunc = lhs_type.asRef().getFunction();
				ECR rhsFunc = rhs_type.asRef().getFunction();
				cjoin(lhsFunc, rhsFunc);
				break;
			}
			default:
				break;
			}
			break;
		}
		default:
			break;
		}
	}

	/**
	 * Unify two value types <code>t1</code>, <code>t2</code>
	 * 
	 * @param t1
	 * @param t2
	 */
	private ValueType unify(ValueType t1, ValueType t2) {
		Preconditions.checkArgument(t1.getKind().equals(t2.getKind()));
		switch (t1.getKind()) {
		case REF: {
			RefType locType1 = t1.asRef();
			RefType locType2 = t2.asRef();
			ECR location_1 = locType1.getLocation();
			ECR location_2 = locType2.getLocation();
			if (!location_1.equals(location_2)) {
				join(location_1, location_2);
			}

			ECR function_1 = locType1.getFunction();
			ECR function_2 = locType2.getFunction();
			if (!function_1.equals(function_2)) {
				join(function_1, function_2);
			}

			t1 = ValueType.ref(location_1, function_1);
			break;
		}

		case LAMBDA: {
			Collection<ECR> args1 = t1.asLambda().getParams();
			Collection<ECR> args2 = t2.asLambda().getParams();

			Iterator<ECR> args_itr_1 = args1.iterator();
			Iterator<ECR> args_itr_2 = args2.iterator();
			while (args_itr_1.hasNext() && args_itr_2.hasNext()) {
				ECR arg_1 = args_itr_1.next();
				ECR arg_2 = args_itr_2.next();
				if (!arg_1.equals(arg_2)) {
					join(arg_1, arg_2);
				}
			}

			// For unifying incompatible lambda types, force the first type
			// as the lambda type with variable arg-types
			if (args_itr_2.hasNext()) {
				t1.asLambda().addParamECR(args_itr_2.next());
			}

			join(t1.asLambda().getRet(), t2.asLambda().getRet());
			break;
		}
		default:
			break;
		}
		return t1;
	}

	private Collection<ECR> getPendings(ECR ecr) {
		return findRoot(ecr).getPendings();
	}

	private void addPending(ECR ecr, ECR newPending) {
		ECR root = findRoot(ecr);
		root.addPending(newPending);
	}
}
