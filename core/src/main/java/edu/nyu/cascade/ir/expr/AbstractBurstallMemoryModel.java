package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.concurrent.ExecutionException;

import xtc.type.AnnotatedT;
import xtc.type.FieldReference;
import xtc.type.Reference;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

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

  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_ALLOC_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";
  protected static final String TEST_VAR = "TEST_VAR";
  
  protected enum CellKind {
    SCALAR, POINTER, TEST_VAR
  }
  
  private final LoadingCache<xtc.type.Type, String> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<xtc.type.Type, String>(){
        public String load(xtc.type.Type type) {
          return parseTypeName(type);
        }
      });
  
  protected xtc.type.Type unwrapped(xtc.type.Type type) {
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type;
  }
  
  protected CellKind getCellKind(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    type = unwrapped(type);
    if(type.isInteger())
      return CellKind.SCALAR;
    if(type.isPointer())
      return CellKind.POINTER;
    if(type.isLabel() && TEST_VAR.equals(type.toLabel().getName()))
      return CellKind.TEST_VAR;
    throw new IllegalArgumentException("Unknown type " + type);
  }
  
  protected String getTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    try {
      return cache.get(type);
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
  private String parseTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);     
    StringBuffer sb =  new StringBuffer();
    if(type.isPointer()) {
      xtc.type.Type pType = type.toPointer().getType();
      sb.append('$').append("PointerT").append(parseTypeName(pType));
    } else if(type.isArray()) {
      xtc.type.Type aType = type.toArray().getType();
      sb.append('$').append("ArrayT").append(parseTypeName(aType));
    } else if(type.isStruct()) {
      sb.append('$').append(type.getName());
    } else if(type.isUnion()) {
      sb.append('$').append(type.getName());
    } else if(type.isAnnotated()){
      AnnotatedT annoType = type.toAnnotated();
      if(annoType.hasShape()) {
        Reference ref = annoType.getShape();
        if(ref instanceof FieldReference) {
          String fieldName = ((FieldReference) ref).toString();
          fieldName = fieldName.replace('.', '#');
          sb.append(fieldName);
        } else {
          sb.append(parseTypeName(ref.getType()));
        }
      } else {
        sb.append(parseTypeName(annoType.getType()));
      }
    } else if(type.isAlias()) {
      xtc.type.Type aliasType = type.toAlias().getType();
      sb.append(parseTypeName(aliasType));
    } else if(type.isVariable()) {
      xtc.type.Type varType = type.toVariable().getType();
      sb.append(parseTypeName(varType));
    } else if(type.isInteger()){
      String kindName = type.toInteger().getKind().name();
      sb.append('$').append(kindName);
    } else if(type.isLabel()){
      sb.append('$').append(type.toLabel().getName());
    } else {
      throw new IllegalArgumentException("Cannot parse type " + type.getName());
    }
    return sb.toString();
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
