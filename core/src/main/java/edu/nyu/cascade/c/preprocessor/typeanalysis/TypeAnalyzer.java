package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.Node;
import xtc.type.Reference;
import xtc.type.Type;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.IRPreProcessor;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.util.CacheException;
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
  
  static private final LoadingCache<Triple<String, Type, String>, IRVar> varCache = CacheBuilder
      .newBuilder().build(new CacheLoader<Triple<String, Type, String>, IRVar>(){
        public IRVar load(Triple<String, Type, String> triple) {
          return loadVariable(triple.fst(), triple.snd(), triple.thd());
        }
      });
  
  
  private Map<String, Set<IRVar>> varTypeMap;
  private SymbolTable symbolTable;
	
	private TypeAnalyzer(SymbolTable _symbolTable) {
		varTypeMap = Maps.newLinkedHashMap();
		symbolTable = _symbolTable;
	}
	
	public static TypeAnalyzer create(SymbolTable _symbolTable) {
		return new TypeAnalyzer(_symbolTable);
	}

	@Override
	public void analysis(IRStatement stmt) {
		Iterable<IRExpression> operands = stmt.getOperands();
		for(IRExpression operand : operands) {
			Node srcNode = operand.getSourceNode();
			Type srcType = CType.getType(srcNode);
			String name = CType.getReferenceName(srcType);
			
			if(name.equals(Identifiers.CONSTANT)) continue; // skip constant
		    
			String srcScope = CType.getScope(srcNode);
			Scope currentScope = symbolTable.getScope(srcScope);
			Scope scope_ = currentScope.isDefined(name) ? currentScope.lookupScope(name) : currentScope;
			
			String srcTypeName = getTypeName(srcType);
			IRVar srcVar = getVariable(name, srcType, scope_.getQualifiedName());
			Set<IRVar> srcVarSet = varTypeMap.get(srcTypeName);
			srcVarSet.add(srcVar);
			varTypeMap.put(srcTypeName, srcVarSet);
	  }
	}

	@Override
	public String displaySnapShot() {
		return varTypeMap.toString();
	}
	
  public IREquivClosure getEquivClass(String name) {
    return TypeEquivClosure.create(name, varTypeMap.get(name));
  }
	
	public ImmutableMap<String, Set<IRVar>> snapshot() {
    ImmutableMap.Builder<String, Set<IRVar>> builder = 
    		new ImmutableMap.Builder<String, Set<IRVar>>().putAll(varTypeMap);
    return builder.build();
	}
	
	public void addVariable(String name, Type type, String scope) {
		IRVar var = getVariable(name, type, scope);
		String typeName = getTypeName(type);
		Set<IRVar> varSet = varTypeMap.get(typeName);
		varSet.add(var);
		varTypeMap.put(typeName, varSet);
	}
	
	public String getTypeName(Type type) {
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

	private IRVar getVariable(String name, Type type, String scope) {
		try {
			return varCache.get(Triple.of(name, type, scope));
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}
	
	private static IRVar loadVariable(String name, Type type, String scope) {
	  return IRVarImpl.create(name, type, scope);
	} 
}
