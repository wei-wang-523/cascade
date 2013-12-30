package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.Node;
import xtc.type.FieldReference;
import xtc.type.Reference;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimaps;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.AddressOfReference;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.IRVar;
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
import edu.nyu.cascade.util.Triple;

/**
 * Preprocessor: type analyzer for Burstall memory model
 * 
 * @author Wei
 *
 */

public class TypeAnalyzer extends PreProcessor<Type> {
	
  public static final class Builder extends PreProcessor.Builder<Type> {
  	SymbolTable symbolTable;

  	public Builder() {}
  	
		@Override
    public Builder setSymbolTable(SymbolTable _symbolTable) {
			symbolTable = _symbolTable;
	    return this;
    }

		@Override
    public TypeAnalyzer build() {
	    return TypeAnalyzer.create(symbolTable);
    }
  }
	
  static private final LoadingCache<Pair<Type, Reference>, String> typeNameCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<Type, Reference>, String>(){
        @Override
        public String load(Pair<Type, Reference> pair) {
          return CType.parseTypeName(pair.fst());
        }
      });
  
  static private final LoadingCache<Triple<String, Type, Scope>, IRVarImpl> varCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Triple<String, Type, Scope>, IRVarImpl>(){
        @Override
        public IRVarImpl load(Triple<String, Type, Scope> triple) {
          return loadVariable(triple.fst(), triple.snd(), triple.thd());
        }
      });
  
  private Map<Type, Set<IRVar>> varTypeMap;
  private SymbolTable symbolTable;
	
	private TypeAnalyzer(SymbolTable _symbolTable) {
		symbolTable = _symbolTable;
		varTypeMap = Maps.newHashMap();
		Map<Type, Collection<IRVar>> tmpMap = parseSymbolTable(_symbolTable);
		for(Entry<Type, Collection<IRVar>> entry : tmpMap.entrySet()) {
			varTypeMap.put(entry.getKey(), Sets.newHashSet(entry.getValue()));
		}
		// discard all entries in caches for each test case
		typeNameCache.invalidateAll();
		varCache.invalidateAll();
	}
	
	public static TypeAnalyzer create(SymbolTable _symbolTable) {
		return new TypeAnalyzer(_symbolTable);
	}

	@Override
	public void analysis(IRStatement stmt) {
//		IOUtils.err().println("Preprocessing: " + stmt.toString());
		switch(stmt.getType()) {
		case ASSUME : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			// Find all allocated(...) predicates
			Iterable<Node> allocated = findAllocatedFuncNode(srcNode);
			for(Node alloc : allocated) {
				Node ptrNode = alloc.getNode(1).getNode(0);
				String ptrScopeName = CType.getScopeName(ptrNode);
				Scope ptrScope = symbolTable.getScope(ptrScopeName);				
				Type ptr2Type = getPointsToElem(ptrNode);
				createAllocVar(ptrNode, ptr2Type, ptrScope);
			}
			break;
		}
		case CAST : {
//			Node typeNode = stmt.getOperand(0).getSourceNode();
//			Type targetType = CType.getType(typeNode);
			
			IRExpression operand = stmt.getOperand(1);
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			
			if(!(srcType.hasConstant()))
				IOUtils.err().println("WARNING: pre-processing " + stmt);
			
			break;
		}
		case ALLOC : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			String srcScopeName = CType.getScopeName(srcNode);
			Scope srcScope = symbolTable.getScope(srcScopeName);
			Type ptr2Type = getPointsToElem(srcNode);
			createAllocVar(srcNode, ptr2Type, srcScope);
			break;
		}
		default : {
			break;			
		}
		}
//		IOUtils.err().println(displaySnapShot());
	}

	@Override
	public String displaySnapShot() {
		StringBuilder sb = new StringBuilder();
		for(Entry<Type, Set<IRVar>> entry : varTypeMap.entrySet()) {
			sb.append(getRepName(entry.getKey())).append(": ");
			for(IRVar var : entry.getValue()) {
				sb.append(var.toStringShort()).append(' ');
			}
			sb.append('\n');
		}
		return sb.toString();
	}
	
	/**
	 * Get the points-to type of <code>type</code>. AddressOf reference 
	 * <code>&((*a).z)</code> should be taken care in order to pick
	 * out the structure selection feature as <code>(*a).z</code>
	 * 
	 * @param type
	 * @return
	 */
	@Override
	public Type getPointsToElem(Node node) {
		Type type = CType.getType(node);
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

	@Override
	public IREquivClosure getEquivClass(Type type) {
		if(type.hasShape()) {
			Reference ref = type.getShape();
			while(ref instanceof FieldReference) {
				ref = ref.getBase();
			}
			type = ref.getType();
		}
		
	  return TypeEquivClosure.create(getRepName(type), varTypeMap.get(type));
	}

	@Override
	public ImmutableMap<Type, Set<IRVar>> getSnapShot() {
	  ImmutableMap.Builder<Type, Set<IRVar>> builder = 
	  		new ImmutableMap.Builder<Type, Set<IRVar>>().putAll(varTypeMap);
	  return builder.build();
	}
	
	@Override
	public void buildSnapShot() {
		// Don't bother to build snap shot for Burstall memory model
	}
	
	@Override
	public Type getRep(Node node) {
		return CType.getType(node);
	}

	/**
	 * Get the name of <code>type</code>
	 */
	@Override
	public String getRepName(Type type) {
		return loadTypeName(type);
	}

	/**
	 * Get the allocated region variable for <code>pVar</code>.
	 * @param pVar
	 * @param pType
	 * @param scopeName
	 * @return a region variable
	 */
	@Override
	public IRVar getAllocateElem(final Node node) {
		Type pType = getPointsToElem(node);
		final String scopeName = CType.getScopeName(node);
		Iterable<IRVar> vars = varTypeMap.get(pType);
		Iterable<IRVar> selectedVars = Iterables.filter(vars, new Predicate<IRVar>(){
			@Override
      public boolean apply(IRVar input) {
	      IRVarImpl var = (IRVarImpl) input;
	      return var.getScope().getQualifiedName().equals(scopeName) && var.hasNode() &&
	      		var.getNode().equals(node);
      }
		});
		
		try {
			return Iterables.getLast(selectedVars);
		} catch (NoSuchElementException e) {
			throw new ExpressionFactoryException("Cannot find allocated variable");
		}
	}

	private Map<Type, Collection<IRVar>> parseSymbolTable(SymbolTable _symbolTable) {
		Map<IRVar, Type> resMap = parseSymbolTableWithScope(_symbolTable.getCurrentScope());
		SetMultimap<Type, IRVar> map = Multimaps.invertFrom(
				Multimaps.forMap(resMap), 
				HashMultimap.<Type, IRVar> create());
		return map.asMap();
	}

	private Map<IRVar, Type> parseSymbolTableWithScope(Scope scope) {
		Map<IRVar, Type> resMap = Maps.newLinkedHashMap();
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
				IRVar var = IRVarImpl.create(name, type, info.getScope());
				if(type.resolve().isArray()) type = type.resolve().toArray().getType();
				resMap.put(var, type);
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

	/**
	 * Pre-processing: create a allocated variable in <code>rootVar</code>
	 * @param pVar
	 * @param srcNode
	 * @param ptr2Type
	 * @return
	 */
	private IRVarImpl createAllocVar(Node srcNode, Type ptr2Type, Scope srcScope) {
		String name = Identifiers.uniquify(Identifiers.REGION_VARIABLE_NAME);
		IRVarImpl var = IRVarImpl.createWithSrcNode(name, srcNode, ptr2Type, srcScope);
		updateVarMap(ptr2Type, var);
		return var;
	}

//	/**
//	 * Pre-processing: get a variable from <code>varCache</code>, if not contained,
//	 * just create a new one.
//	 * @param name
//	 * @param type
//	 * @param scope
//	 * @return a variable
//	 */
//	private IRVarImpl getVariable(String name, Type type, Scope scope) {
//		if(name.equals(Identifiers.CONSTANT)) return null; // skip constant
//				
//		try {
//			Scope scope_ = scope.isDefined(name) ? scope.lookupScope(name) : scope;
//			Type type_ = scope.isDefined(name) ? (Type) scope.lookup(name) : type;
//			IRVarImpl res = varCache.get(Triple.of(name, type_, scope_));
//			updateVarMap(type_, res);
//			return res;
//		} catch (ExecutionException e) {
//			throw new CacheException(e);
//		}
//	}

	private void updateVarMap(Type type, IRVar var) {
		if(varTypeMap.containsKey(type)) {
			Set<IRVar> srcVarSet = varTypeMap.get(type);
			srcVarSet.add(var);
			varTypeMap.put(type, srcVarSet);
		} else {
			varTypeMap.put(type, Sets.newHashSet(var));
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

	private static IRVarImpl loadVariable(String name, Type type, Scope scope) {
		return IRVarImpl.create(name, type, scope);
	}

	private static String loadTypeName(Type type) {
	    Preconditions.checkNotNull(type);
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
}
