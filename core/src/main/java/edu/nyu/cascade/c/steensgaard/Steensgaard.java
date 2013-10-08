package edu.nyu.cascade.c.steensgaard;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;

import xtc.type.DynamicReference;
import xtc.type.Type;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.c.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.util.IOUtils;
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
  private Map<Pair<String, String>, TypeVar> varsMap; 
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
  public AliasVar getNullLoc() {
    return TypeVar.createNullLoc();
  }

  @Override
  public AliasVar addVariable(String name, String scope, Type type) {
    Pair<String, String> key = Pair.of(name, scope);
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
          + name + " in " + scope);
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
  public void heapAssign(AliasVar lhs, Type lhsType) {
    Preconditions.checkArgument(lhs instanceof TypeVar);
    ValueType lhs_type = uf.getType(((TypeVar) lhs).getECR());
    assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
    ECR lhs0_ecr = (ECR) lhs_type.getOperand(0);
    String freshRegionName = Identifiers.uniquify(REGION_VARIABLE_NAME + lhs.getName());
    assert(lhsType.resolve().isPointer());
    Type regionType = CType.unwrapped(lhsType).toPointer().getType();
    regionType = regionType.annotate().shape(new DynamicReference(freshRegionName, regionType));
    TypeVar region = (TypeVar) addVariable(freshRegionName, lhs.getScope(), regionType);
    ECR region_ecr = region.getECR();
    // Attach the fresh region directly the first operand of target var of malloc
    if(!lhs0_ecr.hasInitTypeVar()) {
      lhs0_ecr.setInitVar(region_ecr.getInitTypeVar());
    }
    uf.join(lhs0_ecr, region_ecr);
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
  public AliasVar getRepVar(String name, String scope, Type type) {
    if(Identifiers.NULL_LOC_NAME.equals(name)) {
      TypeVar nullLoc = TypeVar.createNullLoc();
      Pair<String, String> key = Pair.of(nullLoc.getName(), nullLoc.getScope());
      varsMap.put(key, nullLoc);
      return nullLoc;
    } else {
      Scope currentScope = symbolTable.getScope(scope);
      Scope scope_ = currentScope.isDefined(name) ? currentScope.lookupScope(name) : currentScope;
      Pair<String, Scope> key = Pair.of(name, scope_);
      TypeVar var;
      if(varsMap.containsKey(key)) {
        var = varsMap.get(key);
      } else {
        Type type_ = currentScope.isDefined(name) ? (Type) currentScope.lookup(name) : type;
        var = (TypeVar) addVariable(name, scope_.getQualifiedName(), type_);
      }
      
      TypeVar res = uf.getRootInitVar(var.getECR());
      if(type.hasShape()) {
        int num = CType.numOfIndRef(type.getShape());
        while(num > 0) {
          res = (TypeVar) getPointsToRepVar(res); 
          num--;
        }
      }  
      
      if(res == null) {
        IOUtils.debug().pln(type.getShape() + " is uninitialized.");
        res = TypeVar.createNullLoc();
      }
      return res;
    }
  }
  
  @Override
  public ImmutableMap<AliasVar, Set<AliasVar>> snapshot() {
    ImmutableMap.Builder<AliasVar, Set<AliasVar>> builder = 
        new ImmutableMap.Builder<AliasVar, Set<AliasVar>>();
    for(Entry<ECR, Set<AliasVar>> pair : uf.snapshot().entrySet()) {
      builder.put(uf.getRootInitVar(pair.getKey()),
          pair.getValue());
    }
    return builder.build();
  }

  @Override
  public AliasVar getAllocRegion(AliasVar var) {
    Preconditions.checkArgument(var instanceof TypeVar);
    ECR ecr = ((TypeVar) var).getECR();
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
  
  /**
   * Get the alias variable equivalent class of union find
   */
  @Override
  public ImmutableSet<AliasVar> getEquivClass(AliasVar var) {
    return uf.getEquivClass(((TypeVar) var).getECR());
  }
  
  @Override
  public String displaySnapShort() {
    ImmutableCollection<Set<AliasVar>> sets = uf.snapshot().values();
    StringBuilder sb = new StringBuilder();
    if(sets != null) {
      sb.append("Snapshot of partition (size >= 1) :\n ");
      for(Set<AliasVar> set : sets) {
        if(set == null || set.size() <= 1) continue;
        sb.append("  Partition { ");
        for(AliasVar var : set)
          sb.append(var.getName()).append('@').append(var.getScope()).append(' ');
        sb.append("}\n");
      }
    }
    
    sb.append("\nThe points to chain:\n");
    if(sets != null) {
      for(Set<AliasVar> set : sets) {
        if(set == null) continue;
        Iterator<AliasVar> itr = set.iterator();
        ECR ecr = ((TypeVar) itr.next()).getECR();
        if(!uf.hasPointsToChain(ecr)) continue;
        sb.append("  ").append(uf.getPointsToChain(ecr).substring(3));
        sb.append("\n");
      }
    }
    return sb.toString();
  }
  
  @Override
  public AliasVar getPointsToRepVar(AliasVar var) {
    Preconditions.checkArgument(var instanceof TypeVar);
    ECR ecr = ((TypeVar) var).getECR();
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
}
