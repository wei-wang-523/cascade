package edu.nyu.cascade.c.steensgaard;

import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.Maps;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.alias.AliasAnalysis;
import edu.nyu.cascade.c.alias.AliasVar;
import edu.nyu.cascade.c.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements AliasAnalysis {
  
  protected static final String REGION_VARIABLE_NAME = "region_rep";
  private UnionFindECR uf;
  private Map<Pair, TypeVar> varsMap; 
  
  private Steensgaard () {
    uf = UnionFindECR.create();
    varsMap = Maps.newLinkedHashMap();
  }
  
  public static Steensgaard create() {
    return new Steensgaard();
  }

  @Override
  public AliasVar addVariable(String name, Type type, Scope scope) {
    Pair key = Pair.of(name, Pair.of(type, scope));
    TypeVar res = null;
    if(!varsMap.containsKey(key))  {
      res = TypeVar.create(name, type, scope);
      uf.add(res);
      varsMap.put(key, res);
    } else {
      res = varsMap.get(key);
    }
    return res;
  }
  
  @Override
  public AliasVar addVariable(String name, Scope scope) {
    Type type = (Type) scope.lookup(name);
    return addVariable(name, type, scope);
  }

  @Override
  public void addrAssign(AliasVar lhs, AliasVar addr) {
    Preconditions.checkArgument(lhs instanceof TypeVar && addr instanceof TypeVar);
    ValueType lhs_type = ((TypeVar) lhs).getECR().getType();
    assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
    ECR lhs0_ecr = lhs_type.getOperand(0);
    ECR addr_ecr = ((TypeVar) addr).getECR();
    if(!lhs0_ecr.equals(addr_ecr)) {
      uf.join(lhs0_ecr, addr_ecr);
    }
  }

  @Override
  public void assignPtr(AliasVar ptr, AliasVar rhs) {
    Preconditions.checkArgument(ptr instanceof TypeVar && rhs instanceof TypeVar);
    ValueType ptr_type = ((TypeVar) ptr).getECR().getType();
    ValueType rhs_type = ((TypeVar) rhs).getECR().getType();
    assert(ValueTypeKind.LOCATION.equals(rhs_type.getKind()) 
        && ValueTypeKind.LOCATION.equals(ptr_type.getKind()));
    ECR ptr0_ecr = ptr_type.getOperand(0);
    if(ValueTypeKind.BOTTOM.equals(ptr0_ecr.getType().getKind())) {
      ptr0_ecr.setType(rhs_type);
    } else {
      assert(ValueTypeKind.LOCATION.equals(ptr0_ecr.getType().getKind()));
      ECR rhs0_ecr = rhs_type.getOperand(0);
      ECR ptr00_ecr = ptr0_ecr.getType().getOperand(0);
      if(!rhs0_ecr.equals(ptr00_ecr)) 
        uf.cjoin(rhs0_ecr, ptr00_ecr);
      
      ECR rhs1_ecr = rhs_type.getOperand(1);
      ECR ptr01_ecr = ptr0_ecr.getType().getOperand(1);
      if(rhs1_ecr.equals(ptr01_ecr)) 
        uf.cjoin(rhs1_ecr, ptr01_ecr);
    }
  }

  @Override
  public void heapAssign(AliasVar lhs) {
    Preconditions.checkArgument(lhs instanceof TypeVar);
    ValueType lhs_type = ((TypeVar) lhs).getECR().getType();
    assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
    ECR lhs0_ecr = lhs_type.getOperand(0);
    if(ValueTypeKind.BOTTOM.equals(lhs0_ecr.getType().getKind())) {
      String freshRegionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
      Type regionType = CType.unwrapped(lhs.getType()).toPointer().getType();
      TypeVar region = (TypeVar) addVariable(freshRegionName, regionType, lhs.getScope());
      uf.join(lhs0_ecr, region.getECR());
    }
  }

  @Override
  public void opAssign(AliasVar lhs, Iterable<AliasVar> opnds) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void ptrAssign(AliasVar lhs, AliasVar ptr) {
    Preconditions.checkArgument(lhs instanceof TypeVar && ptr instanceof TypeVar);
    ValueType lhs_type = ((TypeVar) lhs).getECR().getType();
    ValueType ptr_type = ((TypeVar) ptr).getECR().getType();
    assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()) 
        && ValueTypeKind.LOCATION.equals(ptr_type.getKind()));
    ECR ptr0_ecr = ptr_type.getOperand(0);
    if(ValueTypeKind.BOTTOM.equals(ptr0_ecr.getType().getKind())) {
      ptr0_ecr.setType(lhs_type);
    } else {
      assert(ValueTypeKind.LOCATION.equals(ptr0_ecr.getType().getKind()));
      ECR lhs0_ecr = lhs_type.getOperand(0);
      ECR ptr00_ecr = ptr0_ecr.getType().getOperand(0);
      if(!lhs0_ecr.equals(ptr00_ecr)) 
        uf.cjoin(lhs0_ecr, ptr00_ecr);
      
      ECR lhs1_ecr = lhs_type.getOperand(1);
      ECR ptr01_ecr = ptr0_ecr.getType().getOperand(1);
      if(lhs1_ecr.equals(ptr01_ecr)) 
        uf.cjoin(lhs1_ecr, ptr01_ecr);
    }
  }

  @Override
  public void simpleAssign(AliasVar lhs, AliasVar rhs) {
    Preconditions.checkArgument(lhs instanceof TypeVar && rhs instanceof TypeVar);
    ValueType lhs_type = ((TypeVar) lhs).getECR().getType();
    ValueType rhs_type = ((TypeVar) rhs).getECR().getType();
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

  @Override
  public void functionCall(AliasVar lhs, AliasVar func, Iterable<AliasVar> args) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void functionDef(AliasVar func, Iterable<AliasVar> params,
      AliasVar retval) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public AliasVar getRepVar(AliasVar var) {
    Preconditions.checkArgument(var instanceof TypeVar);
    return ((TypeVar) var).getECR().getInitTypeVar();
  }
  
  @Override
  public ImmutableCollection<Set<AliasVar>> snapshot() {
    return uf.snapshot();
  }

  @Override
  public AliasVar getPointsToLoc(AliasVar var) {
    Preconditions.checkArgument(var instanceof TypeVar);
    ECR ecr = ((TypeVar) var).getECR();
    ValueType type = ecr.getType();
    assert(ValueTypeKind.LOCATION.equals(type.getKind()));
    /* For array, structure or union, just return the root ECR's 
     * initial type variable
     */
    if(var.getType().resolve().isArray() 
        || var.getType().resolve().isStruct() 
        || var.getType().resolve().isUnion()) {
      return ((ECR) ecr.findRoot()).getInitTypeVar();
    } else {
      return ((ECR) type.getOperand(0).findRoot()).getInitTypeVar();
    }
  }
}
