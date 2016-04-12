package edu.nyu.cascade.cvc4;

import java.io.PrintStream;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.IOUtils;

final class FunctionDeclarator extends ExpressionImpl implements FunctionExpression {

	static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>> funcCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, FunctionDeclarator>>(){
            public ConcurrentMap<String, FunctionDeclarator> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static FunctionDeclarator create(
      ExpressionManagerImpl exprManager, String name, Iterable<? extends Type> argTypes, Type range, boolean fresh) {
  	
	  try {
	  	
	  	if(!fresh && funcCache.get(exprManager).containsKey(name)) {
	  		return funcCache.get(exprManager).get(name);
	  	}
	  	
	    FunctionTypeImpl type = FunctionTypeImpl.create(exprManager, argTypes, range);
	    FunctionDeclarator res = new FunctionDeclarator(exprManager, name, type,fresh);
	    funcCache.get(exprManager).put(res.getName(), res);
	    return res;
	  } catch (ExecutionException e) {
	    throw new CacheException(e);
	  }
  }

  static FunctionDeclarator create(
      ExpressionManagerImpl exprManager, 
      String name, FunctionType type, boolean fresh) {
	  try {
	  	
	  	if(!fresh && funcCache.get(exprManager).containsKey(name)) {
	  		return funcCache.get(exprManager).get(name);
	  	}
  	
	  	FunctionDeclarator res = new FunctionDeclarator(exprManager, name, type, fresh);
	  	funcCache.get(exprManager).put(res.getName(), res);
	  	return res;
	  } catch (ExecutionException e) {
	    throw new CacheException(e);
	  }
  }
  
  private FunctionDeclarator(ExpressionManagerImpl exprManager, String name, final FunctionType ftype,boolean fresh) {
    super(exprManager, new VariableConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, String name, edu.nyu.acsys.CVC4.Type type)
          throws Exception {
      	PrintStream debugStream = IOUtils.debugStream();
      	PrintStream tpFileStream = IOUtils.tpFileStream();
      	
      	debugStream.append("(declare-fun ").append(name).append("(");
      	tpFileStream.append("(declare-fun ").append(name).append("(");
      	
      	edu.nyu.acsys.CVC4.FunctionType funcType = (edu.nyu.acsys.CVC4.FunctionType) type;
      	edu.nyu.acsys.CVC4.vectorType argTypes = funcType.getArgTypes();
      	for(int i = 0; i < argTypes.size(); i++) {
      		argTypes.get(i).toStream(debugStream); debugStream.append(" ");
      		argTypes.get(i).toStream(tpFileStream); tpFileStream.append(" ");
      	}
      	debugStream.append(") ");
      	funcType.getRangeType().toStream(debugStream);
      	debugStream.append(")");
      	
      	tpFileStream.append(") ");
      	funcType.getRangeType().toStream(tpFileStream);
      	tpFileStream.append(")");
      	
      	debugStream.append('\n').flush();
      	tpFileStream.append('\n').flush();
      	
        Expr op = em.mkVar(name, type);
        
        IOUtils.debug().pln(op.toString());        
        return op;
      }
    }, name, ftype, fresh);
  }

  @Override
  public FunctionTypeImpl getType() {
    return (FunctionTypeImpl) super.getType();
  }

  @Override
  public ExpressionImpl apply(Expression arg1, Expression... rest) {
    Preconditions.checkArgument(getType().getArity() == rest.length + 1);
    return apply(Lists.asList(arg1, rest));
  }

  @Override
  public ExpressionImpl apply(Iterable<? extends Expression> args) {
    Preconditions.checkArgument(getType().getArity() == Iterables.size(args));
    return ExpressionImpl.mkFunApply(getExpressionManager(), this, args);
  }

  @Override
  public ImmutableList<? extends Type> getArgTypes() {
    return getType().getArgTypes();
  }

  @Override
  public Type getRange() {
    return getType().getRangeType();
  }
  
  @Override
  public String getName() {
  	return super.getName();
  }
}
