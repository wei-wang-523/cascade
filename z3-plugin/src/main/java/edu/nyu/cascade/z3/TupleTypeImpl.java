package edu.nyu.cascade.z3;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public final class TupleTypeImpl extends TypeImpl implements TupleType {
  
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, TupleTypeImpl>> typeCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, TupleTypeImpl>>(){
            public ConcurrentMap<String, TupleTypeImpl> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static TupleTypeImpl create(ExpressionManagerImpl em, String name, Type firstType,
      Type... otherTypes) {
    TupleTypeImpl res = null;    
    try {
      if(typeCache.get(em).containsKey(name))
        res = typeCache.get(em).get(name);
      else {
        res = new TupleTypeImpl(em, name, Lists.asList(firstType, otherTypes));
        typeCache.get(em).put(name, res);
        return res;
      }
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return res;
  }

  static TupleTypeImpl create(ExpressionManagerImpl em, String name,
      Iterable<? extends Type> types) {
    TupleTypeImpl res = null;
    try {
      if(typeCache.get(em).containsKey(name))
        res = typeCache.get(em).get(name);
      else {
        res = new TupleTypeImpl(em, name, types);
        typeCache.get(em).put(name, res);
      }
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return res;
  }

  static TupleTypeImpl valueOf(ExpressionManagerImpl em, Type t) {
    if (t instanceof TupleTypeImpl) {
      return (TupleTypeImpl) t;
    } else {
      return create(em, ((TupleType) t).getName(), ((TupleType) t).getElementTypes());
    }
  }

  private final ImmutableList<Type> elementTypes;
  private final String typeName;

  private TupleTypeImpl(ExpressionManagerImpl em, String name, Iterable<? extends Type> types) {
    super(em);
    this.elementTypes = ImmutableList.copyOf(types);
    this.typeName = name;
    
    StringBuilder sb = new StringBuilder();
    sb.append("() ( (" + typeName + "\n                          (mk-" + typeName); // Type parameter
    
    try {
      Context z3_context = em.getTheoremProver().getZ3Context();
      Symbol tname = z3_context.MkSymbol(typeName);
      Sort[] z3Types = new Sort[Iterables.size(types)];
      Symbol[] symbols = new Symbol[Iterables.size(types)];
      for (int i = 0; i < Iterables.size(types); i++) {
        z3Types[i] = em.toZ3Type(Iterables.get(types, i));
        symbols[i] = z3_context.MkSymbol(typeName + "@" + i);
        sb.append(" \n                             (" + symbols[i] + " " + z3Types[i] + ")");
      }
      setZ3Type(z3_context.MkTupleSort(tname, symbols, z3Types));
      sb.append(")))");
      em.addToTypeCache(this);
      if(IOUtils.debugEnabled())
        TheoremProverImpl.debugCommand("(declare-datatypes " + sb.toString() + ")");
      if(IOUtils.tpFileEnabled())
        TheoremProverImpl.z3FileCommand("(declare-datatypes " + sb.toString() + ")");
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ImmutableList<Type> getElementTypes() {
    return elementTypes;
  }

  @Override
  public int size() {
    return elementTypes.size();
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.TUPLE;
  }

  @Override
  public TupleVariableImpl variable(String name, boolean fresh) {
    return TupleVariableImpl.create(getExpressionManager(), name, this, fresh);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(typeName).append('(');
    for(Type elemType : elementTypes) sb.append(elemType).append(", ");
    sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",") + 1, ")");
    return sb.toString();
  }

  @Override
  public String getName() {
    return typeName;
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

}
