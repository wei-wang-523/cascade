package edu.nyu.cascade.c.steensgaard;

import static edu.nyu.cascade.c.steensgaard.ValueType.ValueTypeKind.BOTTOM;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.c.steensgaard.ValueType.ValueTypeKind;
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
    if(BOTTOM.equals(getType(e2).getKind())) {
      addPending(e2, e1);
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
      root.setType(t2);
      if(BOTTOM.equals(t2.getKind())) {
        if(e1.hasPending()) {
          Set<ECR> pending_1 = Sets.newHashSet(e1.getPending());
          addPending(root, pending_1);
        }
        if(e2.hasPending()) {
          Set<ECR> pending_2 = Sets.newHashSet(e2.getPending());
          addPending(root, pending_2);
        }
      } else {
        if(e1.hasPending()) {
          for(ECR x : e1.getPending()) {
            uf.union(root, x);
          }
        }
      }
    } else {
      root.setType(t1);
      if(BOTTOM.equals(t2.getKind())) {
        if(e2.hasPending()) {
          for(ECR x : e2.getPending()) {
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
  
  protected boolean hasPointsToChain(ECR e) {
    ECR root = (ECR) e.findRoot();
    ValueType rootType = root.getType();
    if(ValueTypeKind.LOCATION.equals(rootType.getKind())) {
      ECR operand_0 = rootType.getOperand(0);
      if(((ECR) operand_0.findRoot()).hasInitTypeVar())
        return true;
    }
    return false;
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
