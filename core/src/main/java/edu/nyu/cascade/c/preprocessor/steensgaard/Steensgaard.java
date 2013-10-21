package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;

import xtc.tree.Node;
import xtc.type.DynamicReference;
import xtc.type.Reference;
import xtc.type.Type;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.AddressOfReference;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.IRPreProcessor;
import edu.nyu.cascade.c.preprocessor.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements IRPreProcessor {
  private UnionFindECR uf;
  private Map<Pair<String, String>, IRVarImpl> varsMap; 
  private SymbolTable symbolTable;
  
  private Steensgaard (SymbolTable _symbolTable) {
    uf = UnionFindECR.create();
    varsMap = Maps.newLinkedHashMap();
    symbolTable = _symbolTable;
  }
  
  public static Steensgaard create(SymbolTable symbolTable) {
    return new Steensgaard(symbolTable);
  }

  @Override
	public void analysis(IRStatement stmt) {
  	IOUtils.err().println(stmt.toString());
	  switch (stmt.getType()) {
	  case ASSIGN: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Node rhs = stmt.getOperand(1).getSourceNode();
	    
	    Type lType = CType.getType(lhs);
	    Type rType = CType.getType(rhs);
	    String lScope = CType.getScope(lhs);
	    String rScope = CType.getScope(rhs);
	    String lRefName = CType.getReferenceName(lType);
	    String rRefName = CType.getReferenceName(rType);
	    
	    if(rType.hasShape()) {
	      Reference ref = rType.getShape();
	      if(ref.isCast())    
	        ref = ref.getBase();
	      
	      if(ref instanceof AddressOfReference) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = getRepVar(lRefName, lScope, lType);
	        IRVar rTypeVar_ = getRepVar(rRefName, rScope, rType_);
	        addrAssign(lTypeVar_, rTypeVar_); break;
	      }
	      if(ref.isIndirect()) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = getRepVar(lRefName, lScope, lType);
	        IRVar rTypeVar_ = getRepVar(rRefName, rScope, rType_);
	        ptrAssign(lTypeVar_, rTypeVar_); break;
	      }
	    } 
	    
	    CellKind rKind = CType.getCellKind(rType);
	    if(CellKind.STRUCTORUNION.equals(rKind) || CellKind.ARRAY.equals(rKind)) {
	      IRVar lTypeVar_ = getRepVar(lRefName, lScope, lType);
	      IRVar rTypeVar_ = getRepVar(rRefName, rScope, rType);
	      addrAssign(lTypeVar_, rTypeVar_); break;
	    }
	    
	    if(lType.hasShape()) {
	      if(lType.getShape().isIndirect()) {
	        Reference base = lType.getShape().getBase();
	        Type lType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = getRepVar(lRefName, lScope, lType_);
	        IRVar rTypeVar_ = getRepVar(rRefName, rScope, rType);
	        assignPtr(lTypeVar_, rTypeVar_); break;
	      }
	    }
	    
	    IRVar lTypeVar_ = getRepVar(lRefName, lScope, lType);
	    IRVar rTypeVar_ = getRepVar(rRefName, rScope, rType);
	    simpleAssign(lTypeVar_, rTypeVar_); break;
	  }
	  case ALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    xtc.type.Type lType = CType.getType(lhs);
	    String lScope = CType.getScope(lhs);
	    String lRefName = CType.getReferenceName(lType);
	    IRVar lTypeVar = getRepVar(lRefName, lScope, lType);
	    heapAssign(lTypeVar, lType);
	    break;
	  }
	  default:
	  }
	}

	@Override
	public String displaySnapShot() {
	  ImmutableCollection<Set<IRVar>> sets = uf.snapshot().values();
	  StringBuilder sb = new StringBuilder();
	  if(sets != null) {
	    sb.append("Snapshot of partition (size >= 1) :\n ");
	    for(Set<IRVar> set : sets) {
	      if(set == null || set.size() <= 1) continue;
	      sb.append("  Partition { ");
	      for(IRVar var : set)
	        sb.append(var.getName()).append('@').append(var.getScopeName()).append(' ');
	      sb.append("}\n");
	    }
	  }
	  
	  sb.append("\nThe points to chain:\n");
	  if(sets != null) {
	    for(Set<IRVar> set : sets) {
	      if(set == null) continue;
	      Iterator<IRVar> itr = set.iterator();
	      ECR ecr = ((IRVarImpl) itr.next()).getECR();
	      if(!uf.hasPointsToChain(ecr)) continue;
	      sb.append("  ").append(uf.getPointsToChain(ecr).substring(3));
	      sb.append("\n");
	    }
	  }
	  return sb.toString();
	}

	public IRVar getNullLoc() {
    return IRVarImpl.createNullLoc();
  }

  public IRVar getRepVar(String name, String scope, Type type) {
    if(Identifiers.NULL_LOC_NAME.equals(name)) {
      IRVarImpl nullLoc = IRVarImpl.createNullLoc();
      Pair<String, String> key = Pair.of(nullLoc.getName(), nullLoc.getScopeName());
      varsMap.put(key, nullLoc);
      return nullLoc;
    } else {
      Scope currentScope = symbolTable.getScope(scope);
      Scope scope_ = currentScope.isDefined(name) ? currentScope.lookupScope(name) : currentScope;
      Pair<String, Scope> key = Pair.of(name, scope_);
      IRVarImpl var;
      if(varsMap.containsKey(key)) {
        var = varsMap.get(key);
      } else {
        Type type_ = currentScope.isDefined(name) ? (Type) currentScope.lookup(name) : type;
        var = (IRVarImpl) addVariable(name, scope_.getQualifiedName(), type_);
      }
      
      IRVarImpl res = uf.getRootInitVar(var.getECR());
      if(type.hasShape()) {
        int num = CType.numOfIndRef(type.getShape());
        while(num > 0) {
          res = (IRVarImpl) getPointsToRepVar(res); 
          num--;
        }
      }  
      
      if(res == null) {
        IOUtils.debug().pln(type.getShape() + " is uninitialized.");
        res = IRVarImpl.createNullLoc();
      }
      return res;
    }
  }

  public ImmutableMap<IRVar, Set<IRVar>> snapshot() {
    ImmutableMap.Builder<IRVar, Set<IRVar>> builder = 
        new ImmutableMap.Builder<IRVar, Set<IRVar>>();
    for(Entry<ECR, Set<IRVar>> pair : uf.snapshot().entrySet()) {
      builder.put(uf.getRootInitVar(pair.getKey()),
          pair.getValue());
    }
    return builder.build();
  }

  /**
   * Get the alias variable equivalent class of union find
   */
  public AliasEquivClosure getEquivClass(IRVar var) {
    Iterable<IRVar> elements = uf.getEquivClass(((IRVarImpl) var).getECR());
    return AliasEquivClosure.create(var, elements);
  }
  
  public IRVar addVariable(String name, String scope, Type type) {
	  Pair<String, String> key = Pair.of(name, scope);
	  IRVarImpl res = null;
	  if(!varsMap.containsKey(key))  {
	    res = IRVarImpl.create(name, type, scope);
	    uf.add(res);
	    varsMap.put(key, res);
	  } else {
	    res = varsMap.get(key);
	  }
	  
	  if(res == null) 
	    throw new IllegalArgumentException("Cannot find alias variable for "
	        + name + " in " + scope);
	  return res;
	}

	public void heapAssign(IRVar lhs, Type lhsType) {
	  Preconditions.checkArgument(lhs instanceof IRVarImpl);
	  ValueType lhs_type = uf.getType(((IRVarImpl) lhs).getECR());
	  assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
	  ECR lhs0_ecr = (ECR) lhs_type.getOperand(0);
	  String freshRegionName = Identifiers.uniquify(Identifiers.REGION_VARIABLE_NAME 
	  		+ Identifiers.NAME_INFIX + lhs.getName());
	  assert(lhsType.resolve().isPointer());
	  Type regionType = CType.unwrapped(lhsType).toPointer().getType();
	  regionType = regionType.annotate().shape(new DynamicReference(freshRegionName, regionType));
	  IRVarImpl region = (IRVarImpl) addVariable(freshRegionName, lhs.getScopeName(), regionType);
	  ECR region_ecr = region.getECR();
	  // Attach the fresh region directly the first operand of target var of malloc
	  if(!lhs0_ecr.hasInitTypeVar()) {
	    lhs0_ecr.setInitVar(region_ecr.getInitTypeVar());
	  }
	  uf.join(lhs0_ecr, region_ecr);
	}

	public IRVar getAllocRegion(IRVar var) {
	  Preconditions.checkArgument(var instanceof IRVarImpl);
	  ECR ecr = ((IRVarImpl) var).getECR();
	  ValueType type = uf.getType(ecr);
	  assert(ValueTypeKind.LOCATION.equals(type.getKind()));
	  /* For array, structure or union, just return the root ECR's 
	   * initial type variable
	   */
	  CellKind kind = CType.getCellKind(var.getType());
	  switch(kind) {
	  case POINTER:       return type.getOperand(0).getInitTypeVar();
	  case ARRAY:
	  case STRUCTORUNION: {
	    if(uf.hasPointsToChain(ecr)) {
	      return type.getOperand(0).getInitTypeVar();
	    } else {
	      return uf.getRootInitVar(ecr);
	    }
	  }
	  default:
	    throw new IllegalArgumentException("No points to variable for " + var.getType().getShape());
	  }
	}

	public IRVar getPointsToRepVar(IRVar var) {
    Preconditions.checkArgument(var instanceof IRVarImpl);
    ECR ecr = ((IRVarImpl) var).getECR();
    ValueType type = uf.getType(ecr);
    assert(ValueTypeKind.LOCATION.equals(type.getKind()));
    /* For array, structure or union, just return the root ECR's 
     * initial type variable
     */
    CellKind kind = CType.getCellKind(var.getType());
    switch(kind) {
    case POINTER:       
      return uf.getRootInitVar(type.getOperand(0));
    case ARRAY:
    case STRUCTORUNION: {
      if(uf.hasPointsToChain(ecr)) {
        return uf.getRootInitVar(type.getOperand(0));
      } else {
        return uf.getRootInitVar(ecr);
      }
    }
    default:
      throw new IllegalArgumentException("No points to variable for " + var.getType().getShape());
    }
  }
  
  private void simpleAssign(IRVar lhs, IRVar rhs) {
	  Preconditions.checkArgument(lhs instanceof IRVarImpl && rhs instanceof IRVarImpl);
	  ValueType lhs_type = uf.getType(((IRVarImpl) lhs).getECR());
	  ValueType rhs_type = uf.getType(((IRVarImpl) rhs).getECR());
	  assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()) 
	      && ValueTypeKind.LOCATION.equals(rhs_type.getKind()));
	  ECR lhs0_ecr = lhs_type.getOperand(0);
	  ECR rhs0_ecr = rhs_type.getOperand(0);
	  if(!lhs0_ecr.equals(rhs0_ecr))
	    uf.cjoin(lhs0_ecr, rhs0_ecr);
	  
	  ECR lhs1_ecr = lhs_type.getOperand(1);
	  ECR rhs1_ecr = rhs_type.getOperand(1);
	  if(!lhs1_ecr.equals(rhs1_ecr))
	    uf.cjoin(lhs1_ecr, rhs1_ecr);
	  
	}

	private void assignPtr(IRVar ptr, IRVar rhs) {
	  Preconditions.checkArgument(ptr instanceof IRVarImpl && rhs instanceof IRVarImpl);
	  ValueType ptr_type = uf.getType(((IRVarImpl) ptr).getECR());
	  ValueType rhs_type = uf.getType(((IRVarImpl) rhs).getECR());
	  assert(ValueTypeKind.LOCATION.equals(rhs_type.getKind()) 
	      && ValueTypeKind.LOCATION.equals(ptr_type.getKind()));
	  ECR ptr0_ecr = ptr_type.getOperand(0);
	  if(ValueTypeKind.BOTTOM.equals(uf.getType(ptr0_ecr).getKind())) {
	    uf.setType(ptr0_ecr, rhs_type);
	  } else {
	    assert(ValueTypeKind.LOCATION.equals(uf.getType(ptr0_ecr).getKind()));
	    ECR rhs0_ecr = rhs_type.getOperand(0);
	    ValueType ptr0_type = uf.getType(ptr0_ecr);
	    ECR ptr00_ecr = ptr0_type.getOperand(0);
	    if(!rhs0_ecr.equals(ptr00_ecr)) 
	      uf.cjoin(rhs0_ecr, ptr00_ecr);
	    
	    ECR rhs1_ecr = rhs_type.getOperand(1);
	    ECR ptr01_ecr = uf.getType(ptr0_ecr).getOperand(1);
	    if(rhs1_ecr.equals(ptr01_ecr)) 
	      uf.cjoin(rhs1_ecr, ptr01_ecr);
	  }
	}

	private void addrAssign(IRVar lhs, IRVar addr) {
	  Preconditions.checkArgument(lhs instanceof IRVarImpl && addr instanceof IRVarImpl);
	  ValueType lhs_type = uf.getType(((IRVarImpl) lhs).getECR());
	  assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
	  ECR lhs0_ecr = lhs_type.getOperand(0);
	  ECR addr_ecr = ((IRVarImpl) addr).getECR();
	  if(!lhs0_ecr.equals(addr_ecr)) {
	    uf.join(lhs0_ecr, addr_ecr);
	  }
	}

	private void ptrAssign(IRVar lhs, IRVar ptr) {
	  Preconditions.checkArgument(lhs instanceof IRVarImpl && ptr instanceof IRVarImpl);
	  ValueType lhs_type = uf.getType(((IRVarImpl) lhs).getECR());
	  ValueType ptr_type = uf.getType(((IRVarImpl) ptr).getECR());
	  assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()) 
	      && ValueTypeKind.LOCATION.equals(ptr_type.getKind()));
	  ECR ptr0_ecr = ptr_type.getOperand(0);
	  if(ValueTypeKind.BOTTOM.equals(uf.getType(ptr0_ecr).getKind())) {
	    uf.setType(ptr0_ecr, lhs_type);
	  } else {
	    assert(ValueTypeKind.LOCATION.equals(uf.getType(ptr0_ecr).getKind()));
	    ECR lhs0_ecr = lhs_type.getOperand(0);
	    ECR ptr00_ecr = uf.getType(ptr0_ecr).getOperand(0);
	    if(!lhs0_ecr.equals(ptr00_ecr)) 
	      uf.cjoin(lhs0_ecr, ptr00_ecr);
	    
	    ECR lhs1_ecr = lhs_type.getOperand(1);
	    ECR ptr01_ecr = uf.getType(ptr0_ecr).getOperand(1);
	    if(lhs1_ecr.equals(ptr01_ecr)) 
	      uf.cjoin(lhs1_ecr, ptr01_ecr);
	  }
	}
}
