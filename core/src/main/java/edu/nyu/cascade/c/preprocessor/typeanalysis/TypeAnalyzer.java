package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
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
import edu.nyu.cascade.util.Triple;

public class TypeAnalyzer implements IRPreProcessor {
	
  static private final LoadingCache<Pair<Type, Reference>, String> typeNameCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<Type, Reference>, String>(){
        public String load(Pair<Type, Reference> pair) {
          return CType.parseTypeName(pair.fst());
        }
      });
  
  static private final LoadingCache<Triple<String, Type, Scope>, IRVarImpl> varCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Triple<String, Type, Scope>, IRVarImpl>(){
        public IRVarImpl load(Triple<String, Type, Scope> triple) {
          return loadVariable(triple.fst(), triple.snd(), triple.thd());
        }
      });
  
  private Map<String, Set<IRVar>> varTypeMap;
  private SymbolTable symbolTable;
	
	private TypeAnalyzer(SymbolTable _symbolTable) {
		symbolTable = _symbolTable;
		varTypeMap = Maps.newLinkedHashMap();
	}
	
	public static TypeAnalyzer create(SymbolTable _symbolTable) {
		return new TypeAnalyzer(_symbolTable);
	}

	@Override
	public void analysis(IRStatement stmt) {
		IOUtils.err().println("Preprocessing: " + stmt.toString());
		switch(stmt.getType()) {
		case ALLOC : {
			IRExpression operand = stmt.getOperand(0);
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			String name = CType.getReferenceName(srcType);
			String srcScopeName = CType.getScope(srcNode);
			Scope srcScope = symbolTable.getScope(srcScopeName);
			
			if(srcType.hasShape() && srcType.getShape().hasField()) { 
				Reference srcRef = srcType.getShape();
				IRVarImpl srcVar = getVariable(name, srcRef.getBase(), srcScope).fst();
				String fieldName = srcType.getShape().getField();
				createAllocVarOfField(srcVar, srcType, fieldName, srcScope);
			} else {
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				Type ptr2Type = srcType.resolve().toPointer().getType();
				createAllocVar(srcVar, ptr2Type, srcScope);
			}
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
				Reference srcRef = srcType.getShape();
				IRVarImpl srcVar = getVariable(name, srcRef.getBase(), srcScope).fst();
				String fieldName = srcType.getShape().getField();
				freeAllocVarOfField(srcVar, fieldName, srcScope);
			} else {
				IRVarImpl srcVar = getVariable(name, srcType, srcScope);
				freeAllocVar(srcVar, srcScope);
			}			
			break;
		}
		default : {
			Iterable<IRExpression> operands = stmt.getOperands();
			for(IRExpression operand : operands) {
				Node srcNode = operand.getSourceNode();
				Type srcType = CType.getType(srcNode);
				String name = CType.getReferenceName(srcType);
				
				if(name.equals(Identifiers.CONSTANT)) continue; // skip constant
			    
				String srcScopeName = CType.getScope(srcNode);
				Scope srcScope = symbolTable.getScope(srcScopeName);
				getVariable(name, srcType, srcScope);
		  }
			break;			
		}
		}		
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
	
	public String getTypeName(Type type) {
		return loadTypeName(type);
	}

	public IREquivClosure getEquivClass(String name) {
	  return TypeEquivClosure.create(name, varTypeMap.get(name));
	}

	public ImmutableMap<String, Set<IRVar>> snapshot() {
	  ImmutableMap.Builder<String, Set<IRVar>> builder = 
	  		new ImmutableMap.Builder<String, Set<IRVar>>().putAll(varTypeMap);
	  return builder.build();
	}

	public IRVarImpl getAllocatedVar(IRVar rootVar, Type type, String scopeName) {
		IRVarImpl var = (IRVarImpl) rootVar;
		Scope scope = symbolTable.getScope(scopeName);
		IRVarImpl res;
		if(type.hasShape() && type.getShape() instanceof FieldReference) {
			String fieldName = type.getShape().getField();
			res = var.createAllocatedVarOfField(fieldName, scope);		
		} else {
			res = var.createAllocatedVar(scope);
		}
		updateVarMap(type, res);
		return res;
	}
	
	/**
	 * Get the allocated region variable for <code>pVar</code>,
	 * if it's not allocated yet, create a place holder for 
	 * later <code>allocated(...)</code> predicate
	 * to fill in.
	 * @param pVar
	 * @param pType
	 * @param scopeName
	 * @return a region variable
	 */
	public IRVarImpl getAllocVar(IRVar pVar, Type pType, String scopeName) {
		IRVarImpl var = (IRVarImpl) pVar;
		Scope scope = symbolTable.getScope(scopeName);
		
		try{
			if(pType.hasShape() && pType.getShape() instanceof FieldReference) {
				String fieldName = pType.getShape().getField();
				return Iterables.find(
						var.getAllocVarSetOutScopeOfField(fieldName, scope),
						Predicates.and(Predicates.not(IRVarImpl.isNullPredicate), 
								Predicates.not(IRVarImpl.isTouchedPredicate)));
			} else {
				return Iterables.find(
						var.getAllocVarSetOutScope(scope),
						Predicates.and(Predicates.not(IRVarImpl.isNullPredicate), 
								Predicates.not(IRVarImpl.isTouchedPredicate)));
			}
		} catch(NoSuchElementException e) {
			throw new ExpressionFactoryException(e);
		}
	}
	
	/**
	 * Get the variable stored in <code>varTypeMap</code>
	 * @param name
	 * @param type
	 * @param scopeName
	 * @return a variable
	 */
	public IRVarImpl getVariable(String name, Type type, String scopeName) {
		return getVariable(name, type, symbolTable.getScope(scopeName));
	}

	protected IRVarImpl createAllocVarOfField(IRVarImpl rootVar, Type type, String fieldName, Scope scope) {
		IRVarImpl var = rootVar.createAllocVarOfField(fieldName, scope);
		updateVarMap(type, var);
		return var;
	}

	protected IRVarImpl createAllocVar(IRVar pVar, Type type, Scope scope) {
		IRVarImpl var = ((IRVarImpl) pVar).createAllocVar(scope);
		updateVarMap(type, var);
		return var;
	}

	protected void freeAllocVar(IRVar pVar, Scope scope) {
		((IRVarImpl) pVar).freeAllocVar(scope);
	}
	
	protected void freeAllocVarOfField(IRVar rootVar, String fieldName, Scope scope) {
		((IRVarImpl) rootVar).freeAllocVarOfField(fieldName, scope);
	}

	protected IRVarImpl getAllocVar(IRVar pVar, Type pType, Scope scope) {
		IRVarImpl var = (IRVarImpl) pVar;
		
		if(pType.hasShape() && pType.getShape() instanceof FieldReference) {
			String fieldName = pType.getShape().getField();
			Iterable<IRVarImpl> res = Iterables.filter(
					var.getAllocVarSetOutScopeOfField(fieldName, scope), 
					Predicates.not(IRVarImpl.isFreePredicate));
			if(res == null || Iterables.isEmpty(res)) {
				return var.createNullAllocVarOfField(fieldName, scope);
			} else {
				return Iterables.getFirst(res, null);
			}
		} else {
			Iterable<IRVarImpl> res = Iterables.filter(
					var.getAllocVarSetOutScope(scope), 
					Predicates.not(IRVarImpl.isFreePredicate));
			assert res != null;
			if(Iterables.isEmpty(res)) {
				return var.createNullAllocVar(scope);
			} else {
				return Iterables.getFirst(res, null);
			}
		}
	}

	protected IRVarImpl getVariable(String name, Type type, Scope scope) {
		IRVarImpl res;
		if(type.hasShape()) {
			res = getVariable(name, type.getShape(), scope).fst();
		} else {
			try {
				Scope currentScope = scope;
				// scope and type of the root variable with name
				Scope scope_ = currentScope.isDefined(name) ? currentScope.lookupScope(name) : currentScope;
				Type type_ = currentScope.isDefined(name) ? (Type) currentScope.lookup(name) : type;
				// get the root variable
				res = varCache.get(Triple.of(name, type_, scope_));
			} catch (ExecutionException e) {
				throw new CacheException(e);
			}
		}
		
		if(res == null)
			throw new IllegalArgumentException("Cannot find vairable for " + name 
					+ " with type (" + getTypeName(type) + ')');
		
		updateVarMap(type, res);
		return res;
	}

	/**
	 * Get the base variable from <code>name</code> and <code>scope</code>, from the reference
	 * get the target variable. The references considered are indirect reference, field 
	 * reference, and address of reference. For field reference, return the base variable
	 * and field name for case analysis <code>(*s).f</code>, return the variable of <code>
	 * (*s)</code>, and field name <code>f</code>. For higher level analysis <code>(*(*s).f)</code>,
	 * get <code>(region_s, f)</code> from <code>(*s).f</code>, and thus get <code>region_s_f</code>
	 * for <code>(*(*s).f)</code>.
	 * 
	 * @param name
	 * @param ref
	 * @param scope
	 * @return a pair of variable and field name
	 */
	private Pair<IRVarImpl, String> getVariable(String name, Reference ref, Scope scope) {
		if(ref.isIndirect()) {
			Pair<IRVarImpl, String> pair = getVariable(name, ref.getBase(), scope);
			IRVarImpl baseVar = pair.fst();
			return Pair.of(getAllocVar(baseVar, ref.getType(), scope), null);
		} 
		
		if(ref instanceof FieldReference) {
			Pair<IRVarImpl, String> pair = getVariable(name, ref.getBase(), scope);
			assert pair.snd() == null;
			String fieldName = ref.getField();
			return Pair.of(pair.fst(), fieldName);
		}
		
		if(ref instanceof IndexReference) {
			Pair<IRVarImpl, String> pair = getVariable(name, ref.getBase(), scope);
			return pair;
		}
	
		if(ref instanceof AddressOfReference) {
			Pair<IRVarImpl, String> pair = getVariable(name, ref.getBase(), scope);
			assert pair.snd() == null;
			IRVarImpl res  = pair.fst().getRootVar();
			return Pair.of(res, null);
		}
	
		try {
			Scope currentScope = scope;
			// scope and type of the root variable with name
			Scope scope_ = currentScope.isDefined(name) ? currentScope.lookupScope(name) : currentScope;
			Type type_ = currentScope.isDefined(name) ? (Type) currentScope.lookup(name) : ref.getType();
			// get the root variable
			IRVarImpl res = varCache.get(Triple.of(name, type_, scope_));
			return Pair.of(res, null);
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
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
	  IRVarImpl res = IRVarImpl.create(name, type, scope);
	  return res;
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
}