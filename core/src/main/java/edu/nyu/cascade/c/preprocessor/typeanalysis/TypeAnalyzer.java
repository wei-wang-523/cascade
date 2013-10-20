package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.Node;
import xtc.type.FieldReference;
import xtc.type.IndexReference;
import xtc.type.Reference;
import xtc.type.Type;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicates;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.AddressOfReference;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.IRPreProcessor;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.Triple;

public class TypeAnalyzer implements IRPreProcessor {
	
  static private final LoadingCache<Pair<Type, Reference>, String> typeNameCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<Type, Reference>, String>(){
        @Override
        public String load(Pair<Type, Reference> pair) {
          return CType.parseTypeName(pair.fst());
        }
      });
  
  static private final LoadingCache<Triple<String, Pair<Type, Reference>, Scope>, IRVarImpl> varCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Triple<String, Pair<Type, Reference>, Scope>, IRVarImpl>(){
        @Override
        public IRVarImpl load(Triple<String, Pair<Type, Reference>, Scope> triple) {
          return loadVariable(triple.fst(), triple.snd(), triple.thd());
        }
      });
  
  private Map<String, Set<IRVar>> varTypeMap;
  private SymbolTable symbolTable;
	
	private TypeAnalyzer(SymbolTable _symbolTable) {
		symbolTable = _symbolTable;
		varTypeMap = Maps.newLinkedHashMap();
		// discard all entries in caches for each test case
		typeNameCache.invalidateAll();
		varCache.invalidateAll();
	}
	
	public static TypeAnalyzer create(SymbolTable _symbolTable) {
		return new TypeAnalyzer(_symbolTable);
	}

	@Override
	public void analysis(IRStatement stmt) {
		IOUtils.err().println("Preprocessing: " + stmt.toString());
		switch(stmt.getType()) {
		case ASSUME : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			// Find all allocated(...) predicates
			Iterable<Node> allocated = findAllocatedFuncNode(srcNode);
			for(Node alloc : allocated) {
				Node ptrNode = alloc.getNode(1).getNode(0);
				Type ptrType = CType.getType(ptrNode);
				String name = CType.getReferenceName(ptrType);
				String ptrScopeName = CType.getScope(ptrNode);
				Scope ptrScope = symbolTable.getScope(ptrScopeName);
				if(ptrType.hasShape() && ptrType.getShape().hasField()) { 
					Reference ptrRef = ptrType.getShape();
					IRVarImpl ptrVar = getVariable(name, ptrType, ptrScope);
					String fieldName = ptrRef.getField();
					Type ptr2Type = ptrType.resolve().toPointer().getType();
					createAllocVarOfField(ptrVar, ptr2Type, fieldName, ptrScope);
				} else {
					IRVarImpl ptrVar = getVariable(name, ptrType, ptrScope);
					Type ptr2Type = ptrType.resolve().toPointer().getType();
					createAllocVar(ptrVar, ptr2Type, ptrScope);
				}
			}
			break;
		}
		case ALLOC : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			String name = CType.getReferenceName(srcType);
			String srcScopeName = CType.getScope(srcNode);
			Scope srcScope = symbolTable.getScope(srcScopeName);
			
			if(srcType.hasShape() && srcType.getShape().hasField()) {
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				String fieldName = srcType.getShape().getField();
				Type ptr2Type = srcType.resolve().toPointer().getType();
				createAllocVarOfField(srcVar, ptr2Type, fieldName, srcScope);
			} else {
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				Type ptr2Type = srcType.resolve().toPointer().getType();
				createAllocVar(srcVar, ptr2Type, srcScope);
			}
			break;
		}
		case ASSIGN : {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Node rhs = stmt.getOperand(1).getSourceNode();
	    
	    Type lType = CType.getType(lhs);
	    Type rType = CType.getType(rhs);
	    Scope lScope = symbolTable.getScope(CType.getScope(lhs));
	    Scope rScope = symbolTable.getScope(CType.getScope(rhs));
	    String lRefName = CType.getReferenceName(lType);
	    String rRefName = CType.getReferenceName(rType);
	    
	    if(rType.hasShape()) {
	      Reference ref = rType.getShape();
	      if(ref.isCast())    
	        ref = ref.getBase();
	      
	      if(ref instanceof AddressOfReference) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVarImpl lTypeVar_ = getVariable(lRefName, lType, lScope);
	        IRVarImpl rTypeVar_ = getVariable(rRefName, rType_, rScope);
	        addrAssign(lType, lTypeVar_, rTypeVar_); break;
	      }
	      if(ref.isIndirect()) {
	        Reference base = ref.getBase();
	        Type rType_ = base.getType().annotate().shape(base);
	        IRVarImpl lTypeVar_ = getVariable(lRefName, lType, lScope);
	        IRVarImpl rTypeVar_ = getVariable(rRefName, rType_, rScope);
	        ptrAssign(lType, lTypeVar_, rTypeVar_); break;
	      }
	    } 
	    
	    CellKind rKind = CType.getCellKind(rType);
	    if(CellKind.STRUCTORUNION.equals(rKind) || CellKind.ARRAY.equals(rKind)) {
	    	IRVarImpl lTypeVar_ = getVariable(lRefName, lType, lScope);
	    	IRVarImpl rTypeVar_ =  getVariable(rRefName, rType, rScope);
	      addrAssign(lType, lTypeVar_, rTypeVar_); break;
	    }
	    
	    if(lType.hasShape()) {
	      if(lType.getShape().isIndirect()) {
	        Reference base = lType.getShape().getBase();
	        Type lType_ = base.getType().annotate().shape(base);
	        IRVarImpl lTypeVar_ = getVariable(lRefName, lType_, lScope);
	        IRVarImpl rTypeVar_ = getVariable(rRefName, rType, rScope);
	        assignPtr(lType, lTypeVar_, rTypeVar_); break;
	      }
	    }
	    
	    getVariable(lRefName, lType, lScope);
	    getVariable(rRefName, rType, rScope);
	    break;
		}
		case FREE : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			String name = CType.getReferenceName(srcType);
			String srcScopeName = CType.getScope(srcNode);
			Scope srcScope = symbolTable.getScope(srcScopeName);
			if(srcType.hasShape() && srcType.getShape().hasField()) { 
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				String fieldName = srcType.getShape().getField();
				freeAllocVarOfField(srcVar, fieldName, srcScope);
			} else {
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				freeAllocVar(srcVar, srcScope);
			}			
			break;
		}
		case CAST : break;
		case CALL : break;
		default : {
			Iterable<IRExpression> operands = stmt.getOperands();
			for(IRExpression operand : operands) {
				Node srcNode = operand.getSourceNode();
				Type srcType = CType.getType(srcNode);
				String name = CType.getReferenceName(srcType);			    
				String srcScopeName = CType.getScope(srcNode);
				Scope srcScope = symbolTable.getScope(srcScopeName);
				getVariable(name, srcType, srcScope);
		  }
			break;			
		}
		}
		IOUtils.err().println(displaySnapShot());
	}

	@Override
	public String displaySnapShot() {
		StringBuilder sb = new StringBuilder();
		for(Entry<String, Set<IRVar>> entry : varTypeMap.entrySet()) {
			sb.append(entry.getKey()).append(": ");
			for(IRVar var : entry.getValue()) {
				sb.append(((IRVarImpl) var).toStringShort()).append(' ');
			}
			sb.append('\n');
		}
		return sb.toString();
	}
	
	/**
	 * Get the name of <code>type</code>
	 */
	public String getTypeName(Type type) {
		return loadTypeName(type);
	}
	
	/**
	 * Get the points-to type of <code>type</code>. AddressOf reference 
	 * <code>&((*a).z)</code> should be taken care in order to pick
	 * out the structure selection feature as <code>(*a).z</code>
	 * 
	 * @param type
	 * @return
	 */
	public Type getPtr2Type(Type type) {
		Preconditions.checkArgument(type.resolve().isPointer());
		if(type.hasShape()) {
			Reference ref = type.getShape();
			if(ref instanceof AddressOfReference){
	    	AddressOfReference addrRef = (AddressOfReference) ref;
	    	Reference baseRef = addrRef.getBase();
	    	if(baseRef instanceof FieldReference) {
	    		return baseRef.getBase().getType();
	    	}
			}
			
		}
		return type.resolve().toPointer().getType();
	}

	public IREquivClosure getEquivClass(String name) {
	  return TypeEquivClosure.create(name, varTypeMap.get(name));
	}
	
/*	public IREquivClosure getEquivClass(String name, String scopeName) {
		final Scope scope = symbolTable.getScope(scopeName);
		Iterable<IRVar> varSet = Iterables.filter(varTypeMap.get(name),
				new Predicate<IRVar>() {
			@Override
			public boolean apply(IRVar var) {
				return scope.hasNested(((IRVarImpl) var).getScope().getName()) ||
						scope.equals(((IRVarImpl) var).getScope());
			}
		});
	  return TypeEquivClosure.create(name, varSet);
	}*/

	public ImmutableMap<String, Set<IRVar>> snapshot() {
	  ImmutableMap.Builder<String, Set<IRVar>> builder = 
	  		new ImmutableMap.Builder<String, Set<IRVar>>().putAll(varTypeMap);
	  return builder.build();
	}
	
	/**
	 * Get the allocated region variable for <code>pVar</code>.
	 * @param pVar
	 * @param pType
	 * @param scopeName
	 * @return a region variable
	 */
	public IRVarImpl getAllocVar(IRVar pVar, Type pType, String scopeName) {
		IRVarImpl var = (IRVarImpl) pVar;
		Scope scope = symbolTable.getScope(scopeName);
		if(pType.hasShape() && pType.getShape() instanceof FieldReference) {
			String fieldName = pType.getShape().getField();
			return var.getUntouchedAllocVarOfField(fieldName, scope);
		} else {
			return var.getUntouchedAllocVar(scope);
		}
	}
	
	/**
	 * Get the variable stored in <code>varCache</code>
	 * @param name
	 * @param type
	 * @param scopeName
	 * @return a variable or <code>null</code> if <code>varCache</code> does
	 * not have it
	 */
	public IRVarImpl getVariable(String name, Type type, String scopeName) {
		Scope scope = symbolTable.getScope(scopeName);
		
		IRVarImpl res = null;
		
		if(!name.equals(Identifiers.CONSTANT)) { // skip constant			
			Pair<Type, Reference> pair = Pair.of(type, type.getShape());
			Scope scope_ = scope.isDefined(name) ? scope.lookupScope(name) : scope;
			res = varCache.getIfPresent(Triple.of(name, pair, scope_));
		}
		
		if(res == null) {
			IOUtils.err().println("WARNING: Cannot find vairable for " + name 
					+ " (" + type.resolve().getName() + ')');
		}
		return res;
	}

	/**
	 * Pre-processing: create a allocated variable in <code>rootVar</code> with 
	 * <code>fieldName</code>
	 * @param rootVar
	 * @param type
	 * @param fieldName
	 * @param scope
	 * @return
	 */
	private IRVarImpl createAllocVarOfField(IRVarImpl rootVar, Type type, String fieldName, Scope scope) {
		IRVarImpl var = rootVar.createAllocVarOfField(fieldName, scope);
		updateVarMap(type, var);
		return var;
	}

	/**
	 * Pre-processing: create a allocated variable in <code>rootVar</code>
	 * @param pVar
	 * @param type
	 * @param scope
	 * @return
	 */
	private IRVarImpl createAllocVar(IRVar rootVar, Type type, Scope scope) {
		IRVarImpl var = ((IRVarImpl) rootVar).createAllocVar(scope);
		updateVarMap(type, var);
		return var;
	}

	/**
	 * Pre-processing: free the allocated variable of <code>rootVar</code>
	 * @param pVar
	 * @param scope
	 */
	private void freeAllocVar(IRVar rootVar, Scope scope) {
		((IRVarImpl) rootVar).freeAllocVar(scope);
	}
	
	/**
	 * Pre-processing: free the allocated variable of <code>rootVar</code> with 
	 * <code>fieldName</code>
	 * @param rootVar
	 * @param fieldName
	 * @param scope
	 */
	private void freeAllocVarOfField(IRVar rootVar, String fieldName, Scope scope) {
		((IRVarImpl) rootVar).freeAllocVarOfField(fieldName, scope);
	}

	/**
	 * Pre-processing: get a variable from <code>varCache</code>, if not contained,
	 * just create a new one.
	 * @param name
	 * @param type
	 * @param scope
	 * @return a variable
	 */
	private IRVarImpl getVariable(String name, Type type, Scope scope) {
		if(name.equals(Identifiers.CONSTANT)) return null; // skip constant
				
		try {
			Pair<Type, Reference> pair = Pair.of(type, type.getShape());
			Scope scope_ = scope.isDefined(name) ? scope.lookupScope(name) : scope;
			IRVarImpl res = varCache.get(Triple.of(name, pair, scope_));
			if(res == null) {
				IOUtils.err().println("WARNING: Cannot find vairable for " + name 
						+ " (" + type.resolve().getName() + ')');
			} else {
				updateVarMap(type, res);
			}
			return res;
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	private void updateVarMap(Type type, IRVar var) {
	  String typeName = loadTypeName(type);
		if(varTypeMap.containsKey(typeName)) {
			Set<IRVar> srcVarSet = varTypeMap.get(typeName);
			srcVarSet.add(var);
			varTypeMap.put(typeName, srcVarSet);
		} else {
			varTypeMap.put(typeName, Sets.newHashSet(var));
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

	private void addrAssign(Type type, IRVarImpl lhs, IRVarImpl addr) {
	  addr.setRootVar(lhs);
	  if(type.hasShape() && type.getShape() instanceof FieldReference) {
	  	String fieldName = type.getShape().getField();
	  	lhs.addAllocVarMap(fieldName, addr);
	  } else {
	  	lhs.addAllocVarSet(addr);
	  }
	}
	
	private void assignPtr(Type type, IRVarImpl ptr, IRVarImpl rhs) {
		return;
	}
	
	private void ptrAssign(Type type, IRVarImpl lhs, IRVarImpl ptr) {
		return;
	}

	private static String loadTypeName(Type type) {
	    Preconditions.checkArgument(type != null);
	/*    if(type.hasConstant() && type.getConstant().isReference()) {
	      Reference ref = type.getConstant().refValue();
	      if(ref.getType().isBoolean())
	        return "$BoolT";
	    }*/
	    try {
	      return typeNameCache.get(Pair.of(type, type.getShape()));
	    } catch (ExecutionException e) {
	      throw new CacheException(e);
	    }
	  }
	
	private static IRVarImpl loadVariable(String name, Pair<Type, Reference> pair, Scope scope) {
		
		if(pair.snd() != null) {
			Reference ref = pair.snd();
			
			if(ref.isIndirect()) {
				IRVarImpl baseVar = loadVariable(name, Pair.of(ref.getBase().getType(), ref.getBase()), scope);
				Type type = pair.fst();
				
				return getNonFreeAllocVar(baseVar, type, scope);
			} 
			
			if(ref instanceof FieldReference) {
				IRVarImpl baseVar = loadVariable(name, Pair.of(ref.getBase().getType(), ref.getBase()), scope);
				return baseVar;
			}
			
			if(ref instanceof IndexReference) {
				IRVarImpl baseVar = loadVariable(name, Pair.of(ref.getBase().getType(), ref.getBase()), scope);
				return baseVar;
			}
		
			if(ref instanceof AddressOfReference) {
				IRVarImpl baseVar = loadVariable(name, Pair.of(ref.getBase().getType(), ref.getBase()), scope);
				return baseVar.getRootVar();
			}
		}
		
		// scope and type of the root variable with name

		// get the root variable
		Type type_ = scope.isDefined(name) ? (Type) scope.lookup(name) : pair.fst();
		IRVarImpl res = varCache.getIfPresent(Triple.of(name, Pair.of(type_, type_.getShape()), scope));
		return res != null ? res : IRVarImpl.create(name, type_, scope);
	}

	/**
	 * Pre-processing: get allocated and not freed variable of <code>pVar</code>, 
	 * if not yet allocated, create placeholder null variable.
	 * @param pVar
	 * @param pType
	 * @param scope
	 * @return a allocated variable
	 */
	private static IRVarImpl getNonFreeAllocVar(IRVarImpl var, Type pType, Scope scope) {
		IRVarImpl res = null;
		if(pType.hasShape() && pType.getShape() instanceof FieldReference) {
			String fieldName = pType.getShape().getField();
			res = Iterables.find(
					var.getAllocVarSetOfField(fieldName, scope), 
					Predicates.not(IRVarImpl.isFreePredicate), null);
		} else {
			res = Iterables.find(var.getAllocVarSet(scope), 
					Predicates.not(IRVarImpl.isFreePredicate), null);
		}
		
		if(res == null) {
			throw new ExpressionFactoryException("ERROR: preprocessing cannot "
					+ "find variable for " + var.toStringShort());
		}
		
		return res;
	}
}
