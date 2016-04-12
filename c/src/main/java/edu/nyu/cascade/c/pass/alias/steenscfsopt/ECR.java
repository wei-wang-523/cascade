package edu.nyu.cascade.c.pass.alias.steenscfsopt;

import java.math.BigInteger;
import java.util.Collection;

import com.google.common.collect.Sets;

import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind.Partition;

final class ECR extends Partition {
	
	private static final long serialVersionUID = 5892848983695588745L;
	private static BigInteger nextId = BigInteger.ZERO;
	
	private final BigInteger id;  
	private ValueType type;
	
	final private Collection<Pair<Size, ECR>> ccjoin = Sets.newHashSet();
	final private Collection<ECR> cjoin = Sets.newHashSet();
	
	ECR(ValueType _type) {
		super();
		type = _type;
		
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
	
  @Override
  public String toString() {
    return "ECR " + id;
  }

	int getId() {
	  return id.intValue();
  }
	
	void addCCjoin(Size size, ECR other) {
		ccjoin.add(Pair.of(size, other));
	}
	
	void addCjoin(ECR other) {
		cjoin.add(other);
	}
	
	void addCCjoins(Collection<Pair<Size, ECR>> ccjoins) {
		ccjoin.addAll(ccjoins);
	}
	
	void addCjoins(Collection<ECR> cjoins) {
		cjoin.addAll(cjoins);
	}
	
	Collection<Pair<Size, ECR>> getCCjoins() {
		return ccjoin;
	}
	
	Collection<ECR> getCjoins() {
		return cjoin;
	}
	
	void clearCCjoins(Collection<Pair<Size, ECR>> ccjoins) {
		ccjoin.removeAll(ccjoins);
	}
	
	void clearCjoins(Collection<ECR> cjoins) {
		cjoin.removeAll(cjoins);
	}
}
