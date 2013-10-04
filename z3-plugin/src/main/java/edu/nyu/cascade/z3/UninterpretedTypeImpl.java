package edu.nyu.cascade.z3;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;

import edu.nyu.cascade.prover.CacheException;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.util.IOUtils;

public final class UninterpretedTypeImpl extends TypeImpl implements UninterpretedType {
  private final String name;
  
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, UninterpretedTypeImpl>> typeCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, UninterpretedTypeImpl>>(){
            public ConcurrentMap<String, UninterpretedTypeImpl> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static UninterpretedTypeImpl create(ExpressionManagerImpl em, String name) {
    try {
      if(typeCache.get(em).containsKey(name))
        return typeCache.get(em).get(name);
      else {
        UninterpretedTypeImpl res = new UninterpretedTypeImpl(em, name);
        typeCache.get(em).put(name, res);
        return res;
      }
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static UninterpretedTypeImpl valueOf(
      ExpressionManagerImpl exprManager, Type type) {
    Preconditions.checkArgument(type.isUninterpreted());
    if (type instanceof UninterpretedTypeImpl) {
      return (UninterpretedTypeImpl) type;
    } else {
      UninterpretedType uninterType = type.asUninterpreted();
      return create(exprManager, uninterType.getName());
    }
  }

  private UninterpretedTypeImpl(ExpressionManagerImpl exprManager, String name) {
    super(exprManager);
    this.name = name;
    
    try {
      TheoremProverImpl.debugCall("uninterpretedType");
      setZ3Type(exprManager.getTheoremProver().getZ3Context().MkUninterpretedSort(name));
      exprManager.addToTypeCache(this);
      if(IOUtils.debugEnabled())
        TheoremProverImpl.debugCommand("(declare-sort " + name + " 0)");
      if(IOUtils.tpFileEnabled())
        TheoremProverImpl.z3FileCommand("(declare-sort " + name + " 0)");
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public UninterpretedVariableImpl variable(String name, boolean fresh) {
    return UninterpretedVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public String toString() {
    return "UNINTERPRETED" + " OF "+ name ;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.UNINTERPRETED;
  }
}
