package edu.nyu.cascade.c.steensgaard;

import java.util.Iterator;
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
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements AliasAnalysis {
  
  protected static final String REGION_VARIABLE_NAME = "region_";
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
  public AliasVar addVariable(String name, Scope scope, Type type) {
    Pair key = Pair.of(name, scope);
    TypeVar res = null;
    if(!varsMap.containsKey(key))  {
      res = TypeVar.create(name, type, scope);
      uf.add(res);
      varsMap.put(key, res);
    } else {
      res = varsMap.get(key);
    }
    
    if(res == null) 
      throw new IllegalArgumentException("Cannot find alias variable for "
          + name + " in " + scope.getQualifiedName());
    return res;
  }

  @Override
  public void addrAssign(AliasVar lhs, AliasVar addr) {
    Preconditions.checkArgument(lhs instanceof TypeVar && addr instanceof TypeVar);
    ValueType lhs_type = uf.getType(((TypeVar) lhs).getECR());
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
    ValueType ptr_type = uf.getType(((TypeVar) ptr).getECR());
    ValueType rhs_type = uf.getType(((TypeVar) rhs).getECR());
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

  @Override
  public void heapAssign(AliasVar lhs) {
    Preconditions.checkArgument(lhs instanceof TypeVar);
    ValueType lhs_type = uf.getType(((TypeVar) lhs).getECR());
    assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
    ECR lhs0_ecr = lhs_type.getOperand(0);
    if(ValueTypeKind.BOTTOM.equals(uf.getType(lhs0_ecr).getKind())) {
      String freshRegionName = Identifiers.uniquify(REGION_VARIABLE_NAME + lhs.getName());
      Type regionType = CType.unwrapped(lhs.getType()).toPointer().getType();
      TypeVar region = (TypeVar) addVariable(freshRegionName, lhs.getScope(), regionType);
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
    ValueType lhs_type = uf.getType(((TypeVar) lhs).getECR());
    ValueType ptr_type = uf.getType(((TypeVar) ptr).getECR());
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

  @Override
  public void simpleAssign(AliasVar lhs, AliasVar rhs) {
    Preconditions.checkArgument(lhs instanceof TypeVar && rhs instanceof TypeVar);
    ValueType lhs_type = uf.getType(((TypeVar) lhs).getECR());
    ValueType rhs_type = uf.getType(((TypeVar) rhs).getECR());
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
  public AliasVar getRepVar(String name, Scope scope, Type type) {
    Scope scope_ = scope.isDefined(name) ? scope.lookupScope(name) : scope;
    Pair<String, Scope> key = Pair.of(name, scope_);
    TypeVar var;
    if(varsMap.containsKey(key)) {
      var = varsMap.get(key);
    } else {
      Type type_ = scope.isDefined(name) ? (Type) scope.lookup(name) : type;
      var = (TypeVar) addVariable(name, scope_, type_);
    }
    
    TypeVar res = uf.getInitVar(var.getECR());
    if(type.hasShape()) {
      int num = CType.numOfIndRef(type.getShape());
      while(num > 0) {
        res = (TypeVar) getPointsToLoc(res); 
        num--;
      }
    }  
    
    if(res == null)
      throw new ExpressionFactoryException(type.getShape() + " is uninitialized.");
    return res;
  }
  
  @Override
  public ImmutableCollection<Set<AliasVar>> snapshot() {
    return uf.snapshot();
  }

  @Override
  public AliasVar getPointsToLoc(AliasVar var) {
    Preconditions.checkArgument(var instanceof TypeVar);
    ECR ecr = ((TypeVar) var).getECR();
    ValueType type = uf.getType(ecr);
    assert(ValueTypeKind.LOCATION.equals(type.getKind()));
    /* For array, structure or union, just return the root ECR's 
     * initial type variable
     */
    TypeVar res = null;
    if(var.getType().resolve().isArray() 
        || var.getType().resolve().isStruct() 
        || var.getType().resolve().isUnion()) {
      res = uf.getInitVar(ecr);
    } else {
      res = uf.getInitVar((ECR) type.getOperand(0));
    }
    
    return res;
  }
  
  @Override
  public String displaySnapShort() {
    ImmutableCollection<Set<AliasVar>> sets = uf.snapshot();
    StringBuilder sb = new StringBuilder();
    if(sets != null) {
      sb.append("Snapshot:\n");
      for(Set<AliasVar> set : sets) {
        if(set == null) continue;
        sb.append("  Partition { ");
        for(AliasVar var : set)
          sb.append(((TypeVar) var).getName()).append(' ');
        sb.append("}\n");
      }
    }
    
    sb.append("The points to chain:\n");
    if(sets != null) {
      for(Set<AliasVar> set : sets) {
        if(set == null) continue;
        Iterator<AliasVar> itr = set.iterator();
        ECR ecr = ((TypeVar) itr.next()).getECR();
        sb.append(uf.getPointsToChain(ecr).substring(3));
        sb.append("\n");
      }
    }
    return sb.toString();
  }
}
