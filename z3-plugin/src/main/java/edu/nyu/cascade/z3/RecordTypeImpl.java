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
import com.microsoft.z3.Constructor;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

public final class RecordTypeImpl extends TypeImpl implements RecordType {
  
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, RecordTypeImpl>> typeCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, RecordTypeImpl>>(){
            public ConcurrentMap<String, RecordTypeImpl> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  static RecordTypeImpl create(ExpressionManagerImpl em, String name, 
      Iterable<String> elemNames, Iterable<? extends Type> elemTypes) {
    RecordTypeImpl res = null;
    try {
      if(typeCache.get(em).containsKey(name))
        res = typeCache.get(em).get(name);
      else {
        res = new RecordTypeImpl(em, name, elemNames, elemTypes);
        typeCache.get(em).put(name, res);
      }
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return res;
  }

  static RecordTypeImpl create(ExpressionManagerImpl em, String name, String elemName, Type elemType) {
    RecordTypeImpl res = null;
    try {
      if(typeCache.get(em).containsKey(name))
        res = typeCache.get(em).get(name);
      else {
        res = new RecordTypeImpl(em, name, Lists.newArrayList(elemName), Lists.newArrayList(elemType));
        typeCache.get(em).put(name, res);
      }
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return res;
  }
  
  static RecordTypeImpl create(ExpressionManagerImpl em, String tname) {
    ImmutableList<String> elemNames = ImmutableList.of();
    ImmutableList<? extends Type> elemTypes = ImmutableList.of();
    return new RecordTypeImpl(em, tname, elemNames, elemTypes);
  }

  static RecordTypeImpl valueOf(ExpressionManagerImpl em, Type t) {
    if (t instanceof RecordTypeImpl) {
      return (RecordTypeImpl) t;
    } else {
      return create(em, ((RecordType) t).getName(), 
          ((RecordType) t).getElementNames(), ((RecordType) t).getElementTypes());
    }
  }

  private final ImmutableList<Type> elementTypes;
  private final ImmutableList<String> elementNames;
  private final String typeName;

  private RecordTypeImpl(ExpressionManagerImpl em, String name, 
      Iterable<String> elemNames, Iterable<? extends Type> elemTypes) {
    super(em);
    this.elementTypes = ImmutableList.copyOf(elemTypes);
    this.typeName = Identifiers.uniquify(name);
    this.elementNames = ImmutableList.copyOf(elemNames);
    
    StringBuilder sb = new StringBuilder();
    sb.append("() ( (" + typeName + "\n                          (mk-" + typeName); // Type parameter
    
    try {
      Context z3_context = em.getTheoremProver().getZ3Context();
      Sort[] z3Types = new Sort[Iterables.size(elemTypes)];
      String[] symbols = Iterables.toArray(elemNames, String.class);
      int[] refs = new int[Iterables.size(elemTypes)];
      for (int i = 0; i < Iterables.size(elemTypes); i++) {
        z3Types[i] = em.toZ3Type(Iterables.get(elemTypes, i));
        refs[i] = 0;
        sb.append(" \n                             (" + Iterables.get(elemNames, i) + " " + z3Types[i] + ")");
      }
      Constructor[] cons = new Constructor[]{
          z3_context.MkConstructor("mk-" + typeName, "is-" + typeName, symbols, z3Types, refs)};
      setZ3Type(z3_context.MkDatatypeSort(typeName, cons));
      sb.append(")))");
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
  public ImmutableList<String> getElementNames() {
    return elementNames;
  }

  @Override
  public int size() {
    return elementTypes.size();
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.RECORD;
  }

  @Override
  public RecordVariableImpl variable(String name, boolean fresh) {
    return RecordVariableImpl.create(getExpressionManager(), name, this, fresh);
  }

  @Override
  public String toString() {
    return new StringBuilder().append(typeName).append('(')
        .append(elementTypes).append(')').toString();
  }

  @Override
  public String getName() {
    return typeName;
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

  @Override
  public Type select(String fieldName) {
    int i = elementNames.indexOf(fieldName);
    return elementTypes.get(i);
  }
}
