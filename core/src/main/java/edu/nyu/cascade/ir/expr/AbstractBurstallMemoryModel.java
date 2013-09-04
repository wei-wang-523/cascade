package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.concurrent.ExecutionException;

import xtc.type.Reference;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

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
  
  private final LoadingCache<xtc.type.Type, String> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<xtc.type.Type, String>(){
        public String load(xtc.type.Type type) {
          return CType.parseTypeName(type);
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
      return cache.get(type);
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  public Expression combinePreMemoryStates(BooleanExpression guard, 
      RecordExpression mem_1, RecordExpression mem_0) {    
    
    RecordType memType_1 = mem_1.getType();
    Iterable<String> elemNames_1 = Iterables.transform(memType_1.getElementNames(),
        new Function<String, String>() {
      @Override
      public String apply(String elemName) {
        return elemName.substring(elemName.indexOf('@')+1);
      }
    });
    
    RecordType memType_0 = mem_0.getType();
    final Iterable<String> elemNames_0 = Iterables.transform(memType_0.getElementNames(),
        new Function<String, String>() {
      @Override
      public String apply(String elemName) {
        return elemName.substring(elemName.indexOf('@')+1);
      }
    });
    
    Iterable<String> commonElemNames = Iterables.filter(elemNames_1, 
        new Predicate<String>(){
      @Override
      public boolean apply(String elemName) {
        return Iterables.contains(elemNames_0, elemName);
      }
    });
    
    List<Expression> elems = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    List<Type> elemTypes = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    
    ExpressionManager em = getExpressionManager();
    final String typeName_1 = memType_1.getName();
    final String typeName_0 = memType_0.getName();
    
    for(String elemName : commonElemNames) {
      String elemName_1 = typeName_1 + '@' + elemName;
      String elemName_0 = typeName_0 + '@' + elemName;
      Expression elem = em.ifThenElse(guard, mem_1.select(elemName_1), mem_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    final String typeName = Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME);
    Iterable<String> elemNames = Iterables.transform(commonElemNames, 
        new Function<String, String>(){
      @Override
      public String apply(String elemName) {
        return elemName + '@' + typeName;
      }
    });
    
    RecordType recordType = em.recordType(Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME), 
        elemNames, elemTypes);
    Expression res = em.record(recordType, elems);
    
    return res;
  }
  
  public abstract void setStateType(TupleType stateType) ;
  
  @Override
  public abstract TupleType getStateType();
  
  public abstract TupleExpression getUpdatedState(Expression state, Expression... elemPrime) ;
  
}
