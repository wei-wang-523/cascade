package edu.nyu.cascade.z3;

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
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.IOUtils;

public class FunctionDeclarator extends TypeImpl
    implements FunctionType {
  
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>> funcCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>>(){
            public ConcurrentMap<String, FunctionDeclarator> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static FunctionDeclarator create(final ExpressionManagerImpl exprManager, String name,
      Iterable<? extends Type> argTypes, Type range) {
    try {
      if(funcCache.get(exprManager).containsKey(name)) 
        return funcCache.get(exprManager).get(name);
      
      Iterable<TypeImpl> argTypes1 = Iterables.transform(argTypes,
          new Function<Type, TypeImpl>() {
            @Override
            public TypeImpl apply(Type t) {
              return exprManager.importType(t);
            }
      });
      
      TypeImpl rangeType = exprManager.importType(range);

      FuncDecl funcDecl = exprManager.getTheoremProver().getZ3Context().MkFuncDecl(name, 
          Iterables.toArray(Iterables.transform(argTypes, new Function<Type, Sort>() {
        @Override
        public Sort apply(Type type) {
          return exprManager.importType(type).getZ3Type();
        }
      }), Sort.class), rangeType.getZ3Type());
      
      if(IOUtils.debugEnabled())
        TheoremProverImpl.debugCommand(funcDecl.toString().trim());
      if(IOUtils.tpFileEnabled())
        TheoremProverImpl.z3FileCommand(funcDecl.toString().trim());
      
      FunctionDeclarator func = new FunctionDeclarator(exprManager, name, argTypes1, rangeType, funcDecl);
      funcCache.get(exprManager).put(name, func);
      return func;
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static FunctionDeclarator create(final ExpressionManagerImpl exprManager, FuncDecl func) {
    try {
      String name = func.toString();
      Sort[] argSorts = func.Domain();
      List<TypeImpl> argTypes = Lists.newArrayList();
      for(Sort argSort : argSorts)
        argTypes.add(exprManager.toType(argSort));
      TypeImpl rangeType = exprManager.toType(func.Range());
      return new FunctionDeclarator(exprManager, name, argTypes, rangeType, func);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  static FunctionDeclarator valueOf(
      ExpressionManagerImpl exprManager, Type t) {
    if (t instanceof FunctionDeclarator) {
      return (FunctionDeclarator) t;
    } else {
      return create(exprManager, ((FunctionType) t).getName(), ((FunctionType) t).getArgTypes(),
          ((FunctionType) t).getRangeType());
    }
  }
  
  private final ImmutableList<TypeImpl> argTypes;
  private final TypeImpl rangeType;
  public FuncDecl getFunc() {
    return func;
  }

  private final String fname;
  private final FuncDecl func;
  
  private FunctionDeclarator(final ExpressionManagerImpl exprManager, String fname,
      Iterable<? extends TypeImpl> argTypes, TypeImpl range, FuncDecl funcDecl) {
    super(exprManager);
    this.argTypes = ImmutableList.copyOf(argTypes);
    this.rangeType = range;
    this.fname = fname;
    this.func = funcDecl;
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
  public Type getArgTypeAtIndex(int index) {
    return argTypes.get(index);
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
  public Type getRangeType() {
    return rangeType;
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.FUNCTION;
  }

  @Override
  public String getName() {
    return fname;
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

	@Override
  public VariableExpressionImpl variable(String name, boolean fresh) {
		throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

	@Override
	public Expression apply(FunctionExpression fun,
			Iterable<? extends Expression> args) {
  	throw new UnsupportedOperationException("z3 does not support it.");
	}

	@Override
	public Expression apply(FunctionExpression fun, Expression arg1,
			Expression... otherArgs) {
  	throw new UnsupportedOperationException("z3 does not support it.");
	}

	@Override
	protected ExpressionImpl create(Expr res, Expression oldExpr,
			Iterable<? extends ExpressionImpl> children) {
		throw new UnsupportedOperationException();
	}
}
