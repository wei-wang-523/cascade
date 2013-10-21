package edu.nyu.cascade.c.preprocessor.typeanalysis;

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
import xtc.type.StructOrUnionT;
import xtc.type.Type;
import xtc.type.VariableT;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
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
  
  static private final LoadingCache<Triple<String, Type, Scope>, IRVarImpl> varCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Triple<String, Type, Scope>, IRVarImpl>(){
        @Override
        public IRVarImpl load(Triple<String, Type, Scope> triple) {
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
//		IOUtils.err().println("Preprocessing: " + stmt.toString());
		switch(stmt.getType()) {
		case CALL : break;
		case ASSUME : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			// Find all allocated(...) predicates
			Iterable<Node> allocated = findAllocatedFuncNode(srcNode);
			for(Node alloc : allocated) {
				Node ptrNode = alloc.getNode(1).getNode(0);
				Type ptrType = CType.getType(ptrNode);
				String ptrScopeName = CType.getScope(ptrNode);
				Scope ptrScope = symbolTable.getScope(ptrScopeName);
				
				String name = CType.getReferenceName(ptrType);	
				getVariable(name, ptrType, ptrScope);
				
				Type ptr2Type = getPtr2Type(ptrType);
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
			
			if(!(srcType.hasShape() && srcType.getShape().isConstant()))
				IOUtils.err().println("WARNING: pre-processing " + stmt);
			
			break;
		}
		case ALLOC : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			String srcScopeName = CType.getScope(srcNode);
			Scope srcScope = symbolTable.getScope(srcScopeName);
			
			String name = CType.getReferenceName(srcType);	
			getVariable(name, srcType, srcScope);
			
			Type ptr2Type = getPtr2Type(srcType);
			createAllocVar(srcNode, ptr2Type, srcScope);
			break;
		}
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
//		IOUtils.err().println(displaySnapShot());
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
	public IRVar getAllocVar(final Node node, Type pType, final String scopeName) {
		String typeName = getTypeName(pType);
		Iterable<IRVar> vars = varTypeMap.get(typeName);
		Iterable<IRVar> selectedVars = Iterables.filter(vars, new Predicate<IRVar>(){
			@Override
      public boolean apply(IRVar input) {
	      IRVarImpl var = (IRVarImpl) input;
	      return var.getScopeName().equals(scopeName) && var.hasNode() &&
	      		var.getNode().equals(node);
      }
		});
		
		try {
			return Iterables.getLast(selectedVars);
		} catch (NoSuchElementException e) {
			throw new ExpressionFactoryException("Cannot find allocated variable");
		}
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
			Scope scope_ = scope.isDefined(name) ? scope.lookupScope(name) : scope;
			Type type_ = scope.isDefined(name) ? (Type) scope.lookup(name) : type;
			IRVarImpl res = varCache.get(Triple.of(name, type_, scope_));
			updateVarMap(type_, res);
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
		
		if(type.resolve().isStruct() || type.resolve().isUnion()) {
			StructOrUnionT suType = type.resolve().toStructOrUnion();
			for(VariableT elem : suType.getMembers()) {
				String elemTypeName = new StringBuilder().append(typeName)
						.append(Identifiers.NAME_INFIX)
						.append(elem.getName()).toString();
				if(varTypeMap.containsKey(elemTypeName)) {
					Set<IRVar> srcVarSet = varTypeMap.get(elemTypeName);
					srcVarSet.add(var);
					varTypeMap.put(elemTypeName, srcVarSet);
				} else {
					varTypeMap.put(elemTypeName, Sets.newHashSet(var));
				}
			}
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
	
	private static IRVarImpl loadVariable(String name, Type type, Scope scope) {
		return IRVarImpl.create(name, type, scope);
	}
}
