package edu.nyu.cascade.c.steensgaard;

import java.util.Collection;
import java.util.Set;

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

  private ValueType type;
  
  private TypeVar initVar;
  
  /**
   * A list of 'pending' joins for this ECR.  We make conditional joins,
   * if the type for this variable is BOTTOM.  Then, if the type for
   * this variable changes, we need to update the types of all the 
   * ECRs on the pending list.
   */
  private Set<ECR> pending;
  
  private ECR(TypeVar var, ValueType _type) {
    super();
    pending = null;
    type = _type;
    initVar = var;
  }
  
  protected static ECR createBottom() {
    return new ECR(null, ValueType.bottom());
  }
  
  protected static ECR create(TypeVar var, ValueType type) {
    return new ECR(var, type);
  }

  protected boolean hasInitTypeVar() {
    return initVar != null;
  }
  
  /**
   * @return the initial type variable
   */
  protected TypeVar getInitTypeVar() {
    return initVar;
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
  
  protected void setInitVar(TypeVar var) {
    initVar = var;
  }
  
  /**
   * @return the pending with the ECR
   */
  protected Iterable<ECR> getPending() {
    return pending;
  }
  
  protected boolean setPending(Iterable<ECR> newPending) {
    if(newPending == null)  return false;
    pending = Sets.newHashSet(newPending);
    return true;
  }
  
  protected boolean hasPending() {
    return pending != null;
  }
  
  protected boolean addPending(Collection<ECR> newPending) {
    if(newPending == null) return false;
    
    if(pending == null) {
      pending = Sets.newHashSet(newPending);
      return true;
    }
    
    pending.addAll(newPending);
    return true;
  }
  
  protected boolean addPending(ECR newPending) {
    if(newPending == null) return false;
    
    if(pending == null) {
      pending = Sets.newHashSet(newPending);
      return true;
    }
    
    pending.add(newPending);
    return true;
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder().append("(ECR ").append(type.toString());

    if ((pending != null) && (pending.size() > 0)) {
      sb.append(" (pending");
      for(ECR e : pending) {
        sb.append(e.toStringShort());
      }
      sb.append(')');
    }
    sb.append(')');

    return sb.toString();
  }
  
  protected String toStringShort() {
    StringBuilder sb = new StringBuilder().append("ECR ").append(getType());
    return sb.toString();
  }
}
