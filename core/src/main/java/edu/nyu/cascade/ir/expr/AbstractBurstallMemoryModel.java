package edu.nyu.cascade.ir.expr;

import java.util.concurrent.ExecutionException;

import xtc.type.Reference;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.util.Pair;

/**
 * Burstall memory model, multiple memory arrays for various type.
 * These arrays types map pointer type to cell type. The state of 
 * memory is a record with multiple arrays for various types.
 * 
 * @author Wei
 *
 */

public abstract class AbstractBurstallMemoryModel extends AbstractMemoryModel {
  protected AbstractBurstallMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  }
  
  /** In xtc.type.WrappedT, the equals just forwards the method invocation to the wrapped type
   * Here, shape should be involved to determine equivalence, and thus we use pair.
   */
  private final LoadingCache<Pair<xtc.type.Type, xtc.type.Reference>, String> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<xtc.type.Type, xtc.type.Reference>, String>(){
        public String load(Pair<xtc.type.Type, xtc.type.Reference> pair) {
          return CType.parseTypeName(pair.fst());
        }
      });
  
  protected String getTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    if(type.hasConstant() && type.getConstant().isReference()) {
      Reference ref = type.getConstant().refValue();
      if(ref.getType().isBoolean())
        return "$BoolT";
    }
    try {
      return cache.get(Pair.of(type, type.getShape()));
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  public abstract void setStateType(TupleType stateType) ;
  
  @Override
  public abstract TupleType getStateType();
  
}
