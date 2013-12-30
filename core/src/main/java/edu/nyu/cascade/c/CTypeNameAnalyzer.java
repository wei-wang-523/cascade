package edu.nyu.cascade.c;

import java.util.concurrent.ExecutionException;

import xtc.type.Reference;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;

import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.Pair;

/**
 * Type name analyzer for Burstall style memory model
 * 
 * @author Wei
 *
 */

public class CTypeNameAnalyzer {
	
  /** In xtc.type.WrappedT, the equals just forwards the method invocation to the wrapped type
   * Here, shape should be involved to determine equivalence, and thus we use pair.
   */
  static private final LoadingCache<Pair<xtc.type.Type, xtc.type.Reference>, String> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<xtc.type.Type, xtc.type.Reference>, String>(){
        public String load(Pair<xtc.type.Type, xtc.type.Reference> pair) {
          return CType.parseTypeName(pair.fst());
        }
      });
  
  public static String getTypeName(xtc.type.Type type) {
    Preconditions.checkNotNull(type);
    if(type.hasConstant() && type.getConstant().isReference()) {
      Reference ref = type.getConstant().refValue();
      if(ref.getType().isBoolean())
        return "$BoolT";
    }
    try {
      return cache.get(Pair.of(type, type.getShape()));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }  
}
