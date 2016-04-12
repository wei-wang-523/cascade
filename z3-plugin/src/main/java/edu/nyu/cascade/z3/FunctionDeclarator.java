package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.FUNCTION;

import java.util.List;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.Identifiers;

class FunctionDeclarator extends ExpressionImpl
    implements FunctionExpression {
  
	static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>> funcCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>>(){
            public ConcurrentMap<String, FunctionDeclarator> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static FunctionDeclarator create(final ExpressionManagerImpl exprManager, String name,
      Iterable<? extends Type> args, Type range, boolean fresh) {
    try {
    	String funcName = fresh ? Identifiers.uniquify(name) : name;
    	
      if(funcCache.get(exprManager).containsKey(funcName)) 
        return funcCache.get(exprManager).get(funcName);
      
      Iterable<TypeImpl> argTypes = Iterables.transform(args,
          new Function<Type, TypeImpl>() {
            @Override
            public TypeImpl apply(Type t) {
              return exprManager.importType(t);
            }
      });
      
      TypeImpl rangeType = exprManager.importType(range);
      
      FunctionTypeImpl funcType = FunctionTypeImpl.create(exprManager, argTypes, rangeType);
      FunctionDeclarator func = new FunctionDeclarator(exprManager, funcName, funcType);
      funcCache.get(exprManager).put(funcName, func);
      return func;
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static FunctionDeclarator create(final ExpressionManagerImpl exprManager, String name,
	    FunctionType functionType, boolean fresh) {
	  try {
	  	
	  	String funcName = fresh ? Identifiers.uniquify(name) : name;
	  	
	    if(funcCache.get(exprManager).containsKey(funcName)) 
	      return funcCache.get(exprManager).get(funcName);
	    
	    Iterable<TypeImpl> argTypes1 = Iterables.transform(functionType.getArgTypes(),
	        new Function<Type, TypeImpl>() {
	          @Override
	          public TypeImpl apply(Type t) {
	            return exprManager.importType(t);
	          }
	    });
	    
	    TypeImpl rangeType = exprManager.importType(functionType.getRangeType());
	    
	    FunctionTypeImpl funcType = FunctionTypeImpl.create(exprManager, argTypes1, rangeType);
	    FunctionDeclarator func = new FunctionDeclarator(exprManager, funcName, funcType);
	    funcCache.get(exprManager).put(funcName, func);
	    return func;
	  } catch (ExecutionException e) {
	    throw new CacheException(e);
	  }
	}

	static FunctionDeclarator create(final ExpressionManagerImpl exprManager, FuncDecl func) {
    try {
      String name = func.toString();
      Sort[] argSorts = func.getDomain();
      List<TypeImpl> argTypes = Lists.newArrayList();
      for(Sort argSort : argSorts)
        argTypes.add(exprManager.toType(argSort));
      TypeImpl rangeType = exprManager.toType(func.getRange());
      FunctionTypeImpl funcType = FunctionTypeImpl.create(exprManager, argTypes, rangeType);
      return new FunctionDeclarator(exprManager, name, funcType, func);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  static FunctionExpression valueOf(ExpressionManagerImpl exprManager,
	    ExpressionImpl e) {
    if (e instanceof FunctionDeclarator) {
      return (FunctionDeclarator) e;
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
	}

	private final ImmutableList<? extends Type> argTypes;
  private final Type rangeType;
  private final String fname;
  private final FuncDecl func;
  
  private FunctionDeclarator(final ExpressionManagerImpl exprManager, String fname,
  		FunctionTypeImpl functionType, FuncDecl func) {
  	super(exprManager, FUNCTION, functionType);
    this.argTypes = functionType.getArgTypes();
    this.rangeType = functionType.getRangeType();
    this.fname = fname;
    this.func = func;
  }
  
  private FunctionDeclarator(final ExpressionManagerImpl exprManager, String fname,
  		FunctionTypeImpl functionType) {
  	super(exprManager, FUNCTION, functionType);
    this.argTypes = functionType.getArgTypes();
    this.rangeType = functionType.getRangeType();
    this.fname = fname;
    try {
      this.func = exprManager.getTheoremProver().getZ3Context().mkFuncDecl(fname, 
          Iterables.toArray(Iterables.transform(functionType.getArgTypes(), 
          		new Function<Type, Sort>() {
            @Override
            public Sort apply(Type type) {
              return exprManager.importType(type).getZ3Type();
            }
          }), Sort.class), 
          exprManager.importType(functionType.getRangeType()).getZ3Type());
      
      TheoremProverImpl.z3FileCommand(func.toString().trim());
    } catch (Z3Exception e) {
    	throw new TheoremProverException(e);
    }
  }
  
  FuncDecl getFunc() {
	  return func;
	}

	@Override
  public int hashCode() {
  	return func.hashCode();
  }
  
  @Override
  public FunctionTypeImpl getType() {
  	return (FunctionTypeImpl) super.getType();
  }

  @Override
  public ExpressionImpl apply(Iterable<? extends Expression> args) {
    return ExpressionImpl.mkFunApply(getExpressionManager(), this, args);
  }

  @Override
  public ExpressionImpl apply(Expression arg1, Expression... otherArgs) {
    Preconditions.checkArgument(getArity() == otherArgs.length + 1);
    return ExpressionImpl.mkFunApply(getExpressionManager(), this,
        Lists.asList(arg1, otherArgs));
  }

  @Override
  public ImmutableList<? extends Type> getArgTypes() {
    return argTypes;
  }

  @Override
  public int getArity() {
    return argTypes.size();
  }

  @Override
  public String getName() {
    return fname;
  }

	@Override
  public Type getRange() {
	  return rangeType;
  }
	
	@Override
  public boolean equals(Object obj) {
    if (!(obj instanceof FunctionDeclarator)) return false; 
    
    FunctionDeclarator that = (FunctionDeclarator) obj;
    return fname.equals(that.getName()) && func.equals(that.getFunc());
  }
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(fname).append(": (");
		
		int index = 0;
		for(Type argType : argTypes) {
			sb.append(argType);
			if(index + 1 < getArity()) sb.append(',');
			index++;
		}
		
		sb.append(") -> ").append(rangeType);
		return sb.toString();
	}
}
