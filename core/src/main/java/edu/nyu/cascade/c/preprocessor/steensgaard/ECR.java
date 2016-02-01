package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.preprocessor.steensgaard.ValueType.ValueTypeKind;
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

  private ValueType type;
  private BigInteger id;
  
  /**
   * A list of 'pending' joins for this ECR.  We make conditional joins,
   * if the type for this variable is BOTTOM.  Then, if the type for
   * this variable changes, we need to update the types of all the 
   * ECRs on the pending list.
   */
  private Set<ECR> pending = Sets.newHashSet();
  
  private ECR(ValueType _type) {
    super();
    type = _type;
    
    id = nextId;
    nextId = nextId.add(BigInteger.ONE);
  }
  
  protected static ECR createBottom() {
    return new ECR(ValueType.bottom());
  }
  
  protected static ECR create(ValueType type) {
    return new ECR(type);
  }
  
  /**
   * @return the type associated with the ECR.
   */
  protected ValueType getType() {
    return type;
  }
  
  protected void setType(ValueType _type) {
    type = _type;
  }
  
  /**
   * @return the pending with the ECR
   */
  protected Collection<ECR> getPending() {
    return pending;
  }
  
  protected void cleanPending() {
  	pending.clear();
  }
  
  protected boolean hasPending() {
    return pending.isEmpty();
  }
  
  protected boolean addPending(Collection<ECR> newPending) {
    if(newPending == null) return false;    
    pending.addAll(newPending);
    return true;
  }
  
  protected boolean addPending(ECR newPending) {
    return addPending(Collections.singleton(newPending));
  }
  
  protected String toStringShort() {
		return new StringBuilder().append("ECR ")
	  		.append(id).append(" : ").append(type).toString();
	}

	@Override
  public String toString() {
    StringBuilder sb = new StringBuilder().append("(ECR ")
    		.append(id).append(" : ").append(type);
    
    if (!pending.isEmpty()) {
      sb.append(" pending : [ ");
      for(ECR e : pending) {
        sb.append(e.toStringShort()).append(' ');
      }
      sb.append(']');
    }
    sb.append(')');

    return sb.toString();
  }
  
	protected String getId() {
	  return id.toString();
  }
	
	protected Type getXtcType() {
		Preconditions.checkArgument(type.getKind().equals(ValueTypeKind.REF));
		return type.asRef().getXtcType();
	}
}
