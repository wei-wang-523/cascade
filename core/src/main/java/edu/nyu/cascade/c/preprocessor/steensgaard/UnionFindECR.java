package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

class UnionFindECR {
  UnionFind<IRVar> uf;
  
  private UnionFindECR () {
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
   * @param var
   */
  void add(VarImpl var) {
    uf.add(var, var.getECR());
  }
  
  /**
   * Add <code>vars</code> into union find
   * @param vars
   */
  void addAll(Iterable<VarImpl> vars) {
  	for(VarImpl var : vars) {
  		uf.add(var, var.getECR());
  	}
  }
  
 /**
  * Conditional join two ECRs <code>e1</code>
   * and <code>e2</code>
  * @param e1
  * @param e2
  */
  void cjoin(ECR e1, ECR e2) {
  	if(e1.equals(e2)) return;
  	
  	switch(getType(e2).getKind()) {
		case BOTTOM:
			addPending(e2, e1); break;
		default:
			join(e1, e2); break;
  	}
  }
    
  /**
   * Join the types represented by <code>e1</code>
   * and <code>e2</code>
   * @param e1
	 * @param e2
   */
  void join(ECR e1, ECR e2) {
    ValueType t1 = getType(e1);
    ValueType t2 = getType(e2);
    
    Collection<ECR> pending1 = findRoot(e1).getPending();
    Collection<ECR> pending2 = findRoot(e2).getPending();
    
    union(e1, e2);
    ECR root = (ECR) e1.findRoot();
    
    switch(t1.getKind()) {
		case BOTTOM: {
			root.setType(t2);
			
			switch(t2.getKind()) {
			case BOTTOM: {
				Set<ECR> pendings = Sets.newHashSet();
				pendings.addAll(pending1);
		        pendings.addAll(pending2);
		        addPendings(root, pendings);
		        break;
			}
			default:
				for(ECR x : pending1) union(root, x);
		        	break;
			}
				break;
		}
		
		default: {
			root.setType(t1);
			
			switch(t2.getKind()) {
			case BOTTOM:
				for(ECR x : pending2) union(root, x);
                break;
			default: {
				ValueType rootType = root.getType();
				ValueType t = unify(t1, t2);
				t.setAddress(rootType.getAddress());
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
    ECR root = (ECR) e.findRoot();
    root.setType(type);
    if(root.hasPending()) {
      for(ECR x : root.getPending()) {
        join(root, x);
      }
      root.cleanPending();
    }
  }
  
  /**
   * Get the type of the ECR <code>e</code>
   * @param e
   */
  ValueType getType(ECR e) {
    ECR root = (ECR) e.findRoot();
    return root.getType();
  }
  
  /**
   * Get the root of ECR <code>e</code>
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
    ImmutableMap.Builder<ECR, Collection<IRVar>> builder = ImmutableMap.builder();
    for (Partition ecr : map.asMap().keySet()) {
      builder.put((ECR) ecr.findRoot(), ImmutableSet.copyOf(map.asMap().get(ecr)));
    }
    return builder.build();
  }
  
  Collection<IRVar> getEquivClass(ECR key) {
  	return uf.getEquivClass(key);
  }
	
	private void addPendings(ECR ecr, Collection<ECR> newPendings) {
	  ECR root = (ECR) ecr.findRoot();
	  root.addPending(newPendings);
	}

	private void addPending(ECR ecr, ECR newPending) {
		addPendings(ecr, Collections.singleton(newPending));
	}

	/**
	 * Union two ecrs, and always attach an initial var to the root ecr.
	 * We need it to pick the name of representative var, and also get 
	 * final snapshot(map) of the points-to relation of the analysis of
	 * all program variables, of course, null will be not acceptable to 
	 * be the key of the map.
	 */
	private void union(ECR e1, ECR e2) {
	  uf.union(e1, e2);
	}

	/**
	 * Unify two value types <code>t1</code>, <code>t2</code>
	 * @param t1 
	 * @param t2
	 */
	private ValueType unify(ValueType t1, ValueType t2) {
	  Preconditions.checkArgument(t1.getKind().equals(t2.getKind()));
	  switch(t1.getKind()) {
	  case REF: {
	  	RefType locType1 = t1.asRef();
	  	RefType locType2 = t2.asRef();
	    ECR location_1 = locType1.getLocation();
	    ECR location_2 = locType2.getLocation();
	    if(!location_1.equals(location_2)) {
	      join(location_1, location_2);
	    }
	    
	    ECR function_1 = locType1.getFunction();
	    ECR function_2 = locType2.getFunction();
	    if(!function_1.equals(function_2)) {
	      join(function_1, function_2);
	    }
	    
	    xtc.type.Type xtcType1 = locType1.getXtcType();
	    xtc.type.Type xtcType2 = locType2.getXtcType();
	    
	    String scopeName1 = locType1.getScopeName();
	    String scopeName2 = locType2.getScopeName();
	    
	    if(xtcType1.equals(xtcType2) && scopeName1.equals(scopeName2)) break;
	    
	    xtc.type.Type xtcType = CType.getBottomType(xtcType1, xtcType2);

	    String scopeName = CScopeAnalyzer.getTopScope(scopeName1, scopeName2);
	    
	    t1 = ValueType.ref(location_1, function_1, xtcType, scopeName);	    
	    break;
	  }
	  
	  case LAMBDA: {
	    Iterator<ECR> args_itr_1 = t1.asLambda().getOperands().iterator();
	    Iterator<ECR> args_itr_2 = t2.asLambda().getOperands().iterator();
	    while(args_itr_1.hasNext() && args_itr_2.hasNext()) {
	      ECR arg_1 = args_itr_1.next();
	      ECR arg_2 = args_itr_2.next();
	      if(!arg_1.equals(arg_2)) {
	        join(arg_1, arg_2);
	      }
	    }
	    break;
	  }
	  default: break;
	  }
	  return t1;
	}
}
