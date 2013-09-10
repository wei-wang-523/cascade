package edu.nyu.cascade.c.steensgaard;

import static edu.nyu.cascade.c.steensgaard.ValueType.ValueTypeKind.BOTTOM;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.alias.AliasVar;
import edu.nyu.cascade.util.UnionFind;

public class UnionFindECR {
  UnionFind<AliasVar> uf;
  
  private UnionFindECR () {
    uf = UnionFind.create();
  }

  protected static UnionFindECR create() {
    return new UnionFindECR();
  }
  

  protected void add(TypeVar var) {
    uf.add(var, var.getECR());
  }
  
 /**
  * Conditional join two ECRs@param e1
  * @param e2
  */
  protected void cjoin(ECR e1, ECR e2) {
    if(BOTTOM.equals(getType(e1).getKind())) {
      addPending(e1, e2);
    } else {
      join(e1, e2);
    }
  }
    
  /**
   * Join the types represented by @param e1 and the specified ECR @param e2
   */
  protected void join(ECR e1, ECR e2) {
    ValueType t1 = getType(e1);
    ValueType t2 = getType(e2);
    uf.union(e1, e2);
    ECR root = (ECR) e1.findRoot();
    if(BOTTOM.equals(t1.getKind())) {
      setType(e1, t2);
      if(BOTTOM.equals(t2.getKind())) {
        if(hasPending(e2)) {
          Set<ECR> pending_2 = Sets.newHashSet(getPending(e2));
          addPending(e1, pending_2);
        }
      } else {
        if(hasPending(e1)) {
          for(ECR x : getPending(e1)) {
            uf.union(root, x);
          }
        }
      }
    } else {
      setType(root, t1);
      if(BOTTOM.equals(t2.getKind())) {
        if(hasPending(e2)) {
          for(ECR x : getPending(e2)) {
            uf.union(root, x);
          }
        }
      } else {
        unify(t1, t2);
      }
    }
  }  
  
  /**
   * Set the type of the ECR @param e to @param type
   */
  protected void setType(ECR e, ValueType type) { 
    ECR root = (ECR) e.findRoot();
    root.setType(type);
    if(root.hasPending()) {
      for(ECR x : root.getPending()) {
        join(root, x);
      }
      root.cleanPending();
    }
  }
  
  protected void setInitVar(ECR e, TypeVar initVar) {
    ECR root = (ECR) e.findRoot();
    root.setInitVar(initVar);
  }
  
  /**
   * Add @param newPending to @param ecr
   */
  protected void addPending(ECR ecr, Collection<ECR> newPending) {
    ECR root = (ECR) ecr.findRoot();
    root.addPending(newPending);
  }
  
  protected void addPending(ECR ecr, ECR newPending) {
    ECR root = (ECR) ecr.findRoot();
    root.addPending(newPending);
  }
  
  /**
   * Get pending of @param ecr
   */
  protected Iterable<ECR> getPending(ECR ecr) {
    ECR root = (ECR) ecr.findRoot();
    return root.getPending();
  }
  
  /**
   * Decide if @param ecr has pending
   */
  protected boolean hasPending(ECR ecr) {
    return ((ECR) ecr.findRoot()).hasPending();
  }
  
  /**
   * Get the type of the ECR @param e
   */
  protected ValueType getType(ECR e) {
    ECR root = (ECR) e.findRoot();
    return root.getType();
  }
  
  
  /**
   * Get the initial type variable
   */
  protected TypeVar getInitVar(ECR e) {
    ECR root = (ECR) e.findRoot();
    return root.getInitTypeVar();
  }
  
  protected String getPointsToChain(ECR e) {
    return e.getPointsToChain();
  }
  
  /**
   * Unify two value types @param t1 and @param t2
   */
  protected void unify(ValueType t1, ValueType t2) {
    Preconditions.checkArgument(t1.getKind().equals(t2.getKind()));
    switch(t1.getKind()) {
    case BOTTOM: return;
    
    case FUNCTION: {
      ECR location_1 = t1.getOperand(0);
      ECR location_2 = t2.getOperand(0);
      if(!location_1.equals(location_2)) {
        join(location_1, location_2);
      }
      
      ECR function_1 = t1.getOperand(1);
      ECR function_2 = t2.getOperand(1);
      if(!function_1.equals(function_2)) {
        join(function_1, function_2);
      }
      break;
    }
    
    case LOCATION: {
      Iterator<ECR> args_itr_1 = t1.getOperands().iterator();
      Iterator<ECR> args_itr_2 = t2.getOperands().iterator();
      while(args_itr_1.hasNext() && args_itr_2.hasNext()) {
        ECR arg_1 = args_itr_1.next();
        ECR arg_2 = args_itr_2.next();
        if(!arg_1.equals(arg_2)) {
          join(arg_1, arg_2);
        }
      }
      break;
    }
    default: 
      throw new IllegalArgumentException("Unknown type kind " + t1.getKind());
    }
  }
  
  /**
   * Get the snapshot of union find
   * @return
   */
  protected ImmutableCollection<Set<AliasVar>> snapshot() {
    return uf.snapshot();
  }
}
