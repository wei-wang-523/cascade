package edu.nyu.cascade.c.preprocessor.fssteens;

import java.math.BigInteger;
import java.util.Collection;

import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind.Partition;

public final class ECR extends Partition {
	
	private static final long serialVersionUID = 5892848983695588745L;
	private static BigInteger nextId = BigInteger.ZERO;
	
	private final BigInteger id;  
	private ValueType type;
	
	/** Pendings */
	final private Collection<Pair<Size, ECR>> cjoin;
	final private Collection<ECR> join;
	
	ECR(ValueType type) {
		super();
		this.type = type;
		cjoin = Sets.newHashSet();
		join = Sets.newHashSet();
		
	  this.id = nextId;
	  nextId = nextId.add(BigInteger.ONE);
	}
	
	static ECR create(ValueType type) {
		return new ECR(type);
	}
	
	static ECR createBottom() {
	  return new ECR(ValueType.bottom());
  }
	
	@Override
	public int hashCode() {
		return super.hashCode();
	}
	
	ValueType getType() {
		return type;
	}
	
	void setType(ValueType type) {
		this.type = type;
	}
	
	Collection<Pair<Size, ECR>> getCjoins() {
		return cjoin;
	}
	
	Collection<ECR> getJoins() {
		return join;
	}
	
	void clearCjoin() {
		cjoin.clear();
	}
	
	void clearJoin() {
		join.clear();
	}
	
	boolean addCjoin(Size s, ECR e2) {
		return cjoin.add(Pair.of(s, e2));
	}
	
	boolean addJoin(ECR e2) {
		return join.add(e2);
	}
	
	boolean addAllCjoin(Collection<Pair<Size, ECR>> cjoins) {
		return cjoin.addAll(cjoins);
	}
	
	boolean addAllJoin(Collection<ECR> joins) {
		return join.addAll(joins);
	}
	
  @Override
  public String toString() {
    return "ECR " + id;
  }

	String getId() {
	  return String.valueOf(id);
  }

	Type getXtcType() {
		Preconditions.checkArgument(!getType().isBottom());
	  return getType().getXtcType();
  }
}
