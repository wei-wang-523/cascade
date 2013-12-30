package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ExecutionException;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.DynamicReference;
import xtc.type.Reference;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.AddressOfReference;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard extends PreProcessor<IRVar> {
	
  public static final class Builder extends PreProcessor.Builder<IRVar> {
  	SymbolTable symbolTable;

  	public Builder() {}
  	
		@Override
    public Builder setSymbolTable(SymbolTable _symbolTable) {
			symbolTable = _symbolTable;
	    return this;
    }

		@Override
    public Steensgaard build() {
	    return Steensgaard.create(symbolTable);
    }
  }
	
	
  private UnionFindECR uf;
  private Map<Pair<String, Scope>, IRVarImpl> varsMap;
  private ImmutableMap<IRVar, Set<IRVar>> snapShot;
  private SymbolTable symbolTable;
  
  private final IRVarImpl constant, nullLoc;
  
  private final LoadingCache<Pair<GNode, String>, IRVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, IRVar>(){
        public IRVar load(Pair<GNode, String> key) {
        	GNode gnode = key.fst();
          Type type = CType.getType(gnode);
          String scopeName = CType.getScopeName(gnode);
          String refName = CType.getReferenceName(type);
          return loadRepVar(refName, scopeName, type);
        }
      });
  
  private Steensgaard (SymbolTable _symbolTable) {
    symbolTable = _symbolTable;
    
    varsMap = parseSymbolTable(_symbolTable);
    
    Scope rootScope = _symbolTable.rootScope();
    constant = IRVarImpl.create(Identifiers.CONSTANT, xtc.type.IntegerT.INT, rootScope);
    nullLoc = IRVarImpl.createNullLoc(new xtc.type.PointerT(xtc.type.IntegerT.INT), rootScope);
    varsMap.put(Pair.of(Identifiers.CONSTANT, rootScope), constant);
    varsMap.put(Pair.of(Identifiers.NULL_LOC_NAME, rootScope), nullLoc);
    
    uf = UnionFindECR.create();
    uf.addAll(varsMap.values());
  }
  
  public static Steensgaard create(SymbolTable symbolTable) {
    return new Steensgaard(symbolTable);
  }

  @Override
	public void analysis(IRStatement stmt) {
  	IOUtils.debug().pln(stmt.toString());
	  switch (stmt.getType()) {
		case ASSUME : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			// Find all allocated(...) predicates
			Iterable<Node> allocated = findAllocatedFuncNode(srcNode);
			for(Node alloc : allocated) {
				Node ptrNode = alloc.getNode(1).getNode(0);
				Type ptrType = CType.getType(ptrNode);
		    String ptrName = CType.getReferenceName(ptrType);
				String ptrScopeName = CType.getScopeName(ptrNode);			
				IRVar ptrVar = loadRepVar(ptrName, ptrScopeName, ptrType);
				heapAssign(ptrVar, ptrType);
			}
			break;
		}	  
	  case ASSIGN: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Node rhs = stmt.getOperand(1).getSourceNode();
	    
	    Type lType = CType.getType(lhs);
	    Type rType = CType.getType(rhs);
	    String lScope = CType.getScopeName(lhs);
	    String rScope = CType.getScopeName(rhs);
	    String lRefName = CType.getReferenceName(lType);
	    String rRefName = CType.getReferenceName(rType);
	    
	    if(rType.hasShape()) {
	      Reference ref = rType.getShape();
	      if(ref.isCast())    
	        ref = ref.getBase();
	      
	      if(ref instanceof AddressOfReference) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = loadRepVar(lRefName, lScope, lType);
	        IRVar rTypeVar_ = loadRepVar(rRefName, rScope, rType_);
	        addrAssign(lTypeVar_, rTypeVar_); break;
	      }
	      if(ref.isIndirect()) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = loadRepVar(lRefName, lScope, lType);
	        IRVar rTypeVar_ = loadRepVar(rRefName, rScope, rType_);
	        ptrAssign(lTypeVar_, rTypeVar_); break;
	      }
	    } 
	    
	    CellKind rKind = CType.getCellKind(rType);
	    if(CellKind.STRUCTORUNION.equals(rKind) || CellKind.ARRAY.equals(rKind)) {
	      IRVar lTypeVar_ = loadRepVar(lRefName, lScope, lType);
	      IRVar rTypeVar_ = loadRepVar(rRefName, rScope, rType);
	      addrAssign(lTypeVar_, rTypeVar_); break;
	    }
	    
	    if(lType.hasShape()) {
	      if(lType.getShape().isIndirect()) {
	        Reference base = lType.getShape().getBase();
	        Type lType_ = base.getType().annotate().shape(base);
	        IRVar lTypeVar_ = loadRepVar(lRefName, lScope, lType_);
	        IRVar rTypeVar_ = loadRepVar(rRefName, rScope, rType);
	        assignPtr(lTypeVar_, rTypeVar_); break;
	      }
	    }
	    
	    IRVar lTypeVar_ = loadRepVar(lRefName, lScope, lType);
	    IRVar rTypeVar_ = loadRepVar(rRefName, rScope, rType);
	    simpleAssign(lTypeVar_, rTypeVar_); break;
	  }
	  case ALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    xtc.type.Type lType = CType.getType(lhs);
	    String lScope = CType.getScopeName(lhs);
	    String lRefName = CType.getReferenceName(lType);
	    IRVar lTypeVar = loadRepVar(lRefName, lScope, lType);
	    heapAssign(lTypeVar, lType);
	    break;
	  }
	  default:
	  }
	}

	@Override
	public String displaySnapShot() {
		Preconditions.checkNotNull(snapShot);
	  ImmutableCollection<Set<IRVar>> sets = snapShot.values();
	  StringBuilder sb = new StringBuilder();
	  if(sets != null) {
	    sb.append("Snapshot of partition (size >= 1) :\n ");
	    for(Set<IRVar> set : sets) {
	      if(set == null || set.size() <= 1) continue;
	      sb.append("  Partition { ");
	      for(IRVar var : set)
	        sb.append(var.getName()).append('@').append(var.getScope().getQualifiedName()).append(' ');
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
	
  /**
	 * Get the alias variable equivalent class of union find
	 */
	@Override
	public AliasEquivClosure getEquivClass(IRVar var) {
	  return AliasEquivClosure.create(this, var);
	}

	@Override
	public IRVar getPointsToElem(Node node) {
    xtc.type.Type nodeType = CType.getType(node);
    String nodeScopeName = CType.getScopeName(node);
    String refName = CType.getReferenceName(nodeType);
    
    IRVarImpl var = loadRepVar(refName, nodeScopeName, nodeType);
    return getPointsToVar(var);
	}

	@Override
	public ImmutableMap<IRVar, Set<IRVar>> getSnapShot() {
		Preconditions.checkNotNull(snapShot);
		return snapShot;
	}
	
	@Override
	public void buildSnapShot() {
	  ImmutableMap.Builder<IRVar, Set<IRVar>> builder = 
	      new ImmutableMap.Builder<IRVar, Set<IRVar>>();
	  for(Entry<ECR, Set<IRVar>> pair : uf.snapshot().entrySet()) {
	    builder.put(uf.getRootInitVar(pair.getKey()),
	        pair.getValue());
	  }
	  snapShot = builder.build();
	}

	@Override
	public IRVar getAllocateElem(final Node node) {
    xtc.type.Type nodeType = CType.getType(node);
    String nodeScopeName = CType.getScopeName(node);
    String refName = CType.getReferenceName(nodeType);
    
    IRVar var = loadRepVar(refName, nodeScopeName, nodeType);
    
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
	
	@Override
	public String getRepName(IRVar var) {
		return new StringBuilder().append(var.getName())
      	.append(Identifiers.NAME_INFIX)
      	.append(var.getScope().getQualifiedName()).toString();
	}
	
	@Override
	public IRVar getRep(Node node) {
    try {
      String scope = CType.getScopeName(node);
      Pair<GNode, String> key = Pair.of(GNode.cast(node), scope);
      return cache.get(key);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
	}
	
	public Scope getRootScope(String repName) {
		// FIXME: variable name cannot has NAME_INFIX '.'
		int index = repName.indexOf(Identifiers.NAME_INFIX);
		String name = repName.substring(0, index);
		String scopeName = repName.substring(index+1);
		Scope scope = symbolTable.getScope(scopeName); // requires Qualified name
		IRVar var = varsMap.get(Pair.of(name, scope));
		AliasEquivClosure equivClosure = getEquivClass(var);
		Scope res = (Scope) equivClosure.getProperty(Identifiers.SCOPE);
		return res;
	}

	private Map<Pair<String, Scope>, IRVarImpl> parseSymbolTable(SymbolTable _symbolTable) {
		return parseSymbolTableWithScope(_symbolTable.getCurrentScope());
	}

	private Map<Pair<String, Scope>, IRVarImpl> parseSymbolTableWithScope(Scope scope) {
		Map<Pair<String, Scope>, IRVarImpl> resMap = Maps.newLinkedHashMap();
		Scope origScope = symbolTable.getCurrentScope();
		symbolTable.setScope(scope);
		if(scope.hasSymbols()) {
			Iterator<String> itr = scope.symbols();
			while(itr.hasNext()) {
				String name = itr.next();
				if(Identifiers.FUNC.equals(name)) continue;
				Type type = symbolTable.lookupType(name);
				if( type.resolve().isFunction() ) continue;
				if( type.isAlias() )	continue; // alias structure type
				if( !type.hasShape() ) continue; // tag(_addr)

				IRVarInfo info = symbolTable.lookup(name);
				if(!(info.getScope().equals(scope) // check info consistency
						&& CType.getType(info.getDeclarationNode()).equals(type))) {
					throw new ExpressionFactoryException("Inconsistent scope and type for " + name);
				}
				IRVarImpl var = IRVarImpl.create(name, type, info.getScope());
				resMap.put(Pair.of(name, scope), var);
			}
		}
		
		if(scope.hasNested()) {
			Iterator<String> itr = scope.nested();
			while(itr.hasNext()) {
				String scopeName = itr.next();
				Scope nestScope = scope.getNested(scopeName);
				resMap.putAll(parseSymbolTableWithScope(nestScope));
			}
		}
		symbolTable.setScope(origScope);
		return resMap;
	}
	
  private IRVarImpl addVariable(String name, Type type, Scope scope) {
  	Pair<String, Scope> key = Pair.of(name, scope);
  	Preconditions.checkArgument(!varsMap.containsKey(key));
  	IRVarImpl res = IRVarImpl.create(name, type, scope);
  	varsMap.put(key, res);
    uf.add(res);
	  return res;
	}

	private void heapAssign(IRVar lhs, Type lhsType) {
	  Preconditions.checkArgument(lhs instanceof IRVarImpl);
	  ValueType lhs_type = uf.getType(((IRVarImpl) lhs).getECR());
	  assert(ValueTypeKind.LOCATION.equals(lhs_type.getKind()));
	  ECR lhs0_ecr = (ECR) lhs_type.getOperand(0);
	  String freshRegionName = Identifiers.uniquify(Identifiers.REGION_VARIABLE_NAME 
	  		+ Identifiers.NAME_INFIX + lhs.getName());
	  assert(lhsType.resolve().isPointer());
	  Type regionType = CType.unwrapped(lhsType).toPointer().getType();
	  regionType = regionType.annotate().shape(new DynamicReference(freshRegionName, regionType));
	  IRVarImpl region = addVariable(freshRegionName, regionType, lhs.getScope());
	  ECR region_ecr = region.getECR();
	  // Attach the fresh region directly the first operand of target var of malloc
	  if(!lhs0_ecr.hasInitTypeVar()) {
	    lhs0_ecr.setInitVar(region_ecr.getInitTypeVar());
	  }
	  uf.join(lhs0_ecr, region_ecr);
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
	
	private IRVarImpl loadRepVar(String name, String scopeName, Type type) {
		if(Identifiers.CONSTANT.equals(name))	
			return constant;
		
		if(Identifiers.NULL_LOC_NAME.equals(name))	
			return nullLoc;
		
	  Scope currentScope = symbolTable.getScope(scopeName);
	  Scope scope = currentScope.isDefined(name) ? // region is not defined under scope
	  		currentScope.lookupScope(name) : currentScope;
	  Pair<String, Scope> key = Pair.of(name, scope);
	
	  IRVarImpl var = null;
	  if(varsMap.containsKey(key)) {
	  	 var = varsMap.get(key);
	  } else { // bound variable in assertion
	  	Scope origScope = symbolTable.getCurrentScope();
	  	symbolTable.setScope(scope);
	  	Type type_ = symbolTable.lookupType(name);
	  	IRVarInfo info = symbolTable.lookup(name);
	  	Scope scope_ = info.getScope();
	  	if(!(scope_.equals(scope) 
	  			&& type_.equals(CType.getType(info.getDeclarationNode())))) {
	  		throw new ExpressionFactoryException("Inconsistent info for " + name + '@' + scopeName);
	  	}
	  	var = addVariable(name, type_, scope_);
	  	buildSnapShot(); // add bound variable, update snapshot
	  	symbolTable.setScope(origScope);
	  }
	    
	  IRVarImpl res = uf.getRootInitVar(var.getECR());
	  
	  if(!type.hasShape())	return res;
	  
	  int num = CType.numOfIndRef(type.getShape());
	  
	  if(num <= 0) {
		  /*FIXME: int a; &a */
//		Type resType = res.getType().resolve();
//	  	assert resType.isUnion() || resType.isStruct() || resType.isArray();
	  	return res;
	  } else {
	  	int iter = num;
	  	IRVarImpl resPrime = res;
		  while(iter > 0) {
		  	resPrime = getPointsToVar(resPrime); 
		  	if(resPrime == null) break;
		  	iter--;
		  }  
		    
		  if(resPrime == null) {
		  	IOUtils.debug().pln(type.getShape() + " is uninialized.");
		  	return nullLoc;
		  }
		  
		  return resPrime;
	  }
	}

	private IRVarImpl getPointsToVar(IRVarImpl var) {
		Preconditions.checkNotNull(var);
	  ECR ecr = var.getECR();
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
	
	/**
	 * Pre-processing: pick all <code>allocated(...)</code> children nodes 
	 * from <code>node</code>
	 * @param node
	 * @return a collection of allocated nodes
	 */
	private Iterable<Node> findAllocatedFuncNode(Node node) {
		if(node.hasName("FunctionCall") && 
				ReservedFunction.FUN_ALLOCATED.equals(node.getNode(0).getString(0))) {
			return Collections.singleton(node);
		}
		
		ImmutableList.Builder<Node> builder = new ImmutableList.Builder<Node>();
		Iterator<Object> itr = node.iterator();
		while(itr.hasNext()) {
			Object elem = itr.next();
			if(elem instanceof Node)
				builder.addAll(findAllocatedFuncNode((Node) elem));
		}
		return builder.build();
	}
}