package edu.nyu.cascade.ir.expr;

//import java.util.List;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.c.preprocessor.TypeCastAnalysis;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public abstract class AbstractMemoryModel implements MemoryModel {
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_ALLOC_VARIABLE_NAME = "size";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_ALLOC_STATE_TYPE = "sizeType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";
  protected static final String ARRAY_MEM_PREFIX = "mem";
  protected static final String ARRAY_ALLOC_PREFIX = "size";
  protected static final Map<String, String> elemArrScopeMap = Maps.newHashMap();
  
  private final ExpressionEncoding encoding;
  
  protected AbstractMemoryModel(ExpressionEncoding encoding) {
    this.encoding = encoding;
  }
  
  @Override
  public Expression freshState() {
    return (Expression) getExpressionManager().variable(DEFAULT_MEMORY_VARIABLE_NAME,
        getStateType(), true);
    }

  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    return ImmutableSet.of();
  }

  @Override
  public ExpressionEncoding getExpressionEncoding() {
    return encoding;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return encoding.getExpressionManager();
  }

  @Override
  public Expression initialState() {
    return freshState();
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression memory) {
        return expr
            .subst(ImmutableList.of(memoryVar), ImmutableList.of(memory));
      }

      @Override
      public Type getOutputType() {
        return expr.getType();
      }

      @Override
      public Type getInputType() {
        return memoryVar.getType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return expr.getExpressionManager();
      }
    };
  }
  
  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {};
  
  @Override
  public void setTypeCastAnalyzer(TypeCastAnalysis analyzer) {};
  
  @Override
  public Expression combineRecordStates(BooleanExpression guard, 
      RecordExpression rec_1, RecordExpression rec_0) {    
    if(rec_1.equals(rec_0))	return rec_0;
    
    Map<String, ArrayExpression> elemMap_0 = getRecordElems(rec_0);
    Map<String, ArrayExpression> elemMap_1 = getRecordElems(rec_1);
    
    final Set<String> elemNames_1 = elemMap_1.keySet();
    final Set<String> elemNames_0 = elemMap_0.keySet();
    
    Iterable<String> commonElemNames = Iterables.filter(elemNames_1, 
        new Predicate<String>(){
      @Override
      public boolean apply(String elemName) {
        return elemNames_0.contains(elemName);
      }
    });
    
    List<Expression> elems = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    List<Type> elemTypes = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    
    ExpressionManager exprManager = getExpressionManager();
    
    for(String elemName : commonElemNames) {
    	Expression elem_1 = elemMap_1.get(elemName);
    	Expression elem_0 = elemMap_0.get(elemName);
    	Expression elem = null;
    	if(elem_1.equals(elem_0)) 
    		elem = elem_0;
    	else
    		elem = exprManager.ifThenElse(guard, elem_1, elem_0);
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    String recordStateName = rec_0.getType().getName();
    
    String typeName = null;
    if(recordStateName.startsWith(DEFAULT_MEMORY_STATE_TYPE)) {
    	typeName = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
    } else if(recordStateName.startsWith(DEFAULT_ALLOC_STATE_TYPE)) {
    	typeName = Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
    } else {
    	throw new IllegalArgumentException("Unknown record name " + recordStateName);
    }
    
    Iterable<String> elemNames = recomposeFieldNames(typeName, commonElemNames);   
    RecordType recordType = exprManager.recordType(typeName, elemNames, elemTypes);
    Expression res = exprManager.record(recordType, elems);
    
    return res;
  }  
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  @Override
  public final TupleExpression getUpdatedState(Expression state, Expression... elems) {
  	return getUpdatedState(state, Arrays.asList(elems));
  }
  
  @Override
  public final TupleExpression getUpdatedState(Expression state, Iterable<Expression> elems) {
  	Preconditions.checkArgument(state != null && state.isTuple());
    
    Function<Expression, Type> func = new Function<Expression, Type>(){
    	@Override
    	public Type apply(Expression elem) {
    		return elem.getType();
    	}
    };
    
    Iterable<Type> elemTypes = Iterables.transform(elems, func);
    Iterable<? extends Type> stateElemTypes = state.getType().asTuple().getElementTypes();
    
    boolean areEqual = true;
    if(Iterables.size(elemTypes) != Iterables.size(stateElemTypes)) {
    	areEqual = false;
    } else {
    	Iterator<Type> thisItr = elemTypes.iterator();
    	Iterator<? extends Type> thatItr = stateElemTypes.iterator();
    	
    	while(thisItr.hasNext() && thatItr.hasNext()) {
    		if(!thisItr.next().equals(thatItr.next())) {
    			areEqual = false; break;
    		}
    	}
    }
    
    ExpressionManager exprManager = getExpressionManager();
    Type stateTypePrime = state.getType();
    
    if(!areEqual) {
    	stateTypePrime = exprManager.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), elemTypes);
    }
    return exprManager.tuple(stateTypePrime, elems);
  }
  
	protected final RecordType getRecordTypeFromMap(String typeName, 
			final Map<String, ArrayExpression> map) {
		Preconditions.checkArgument(map != null);
	  Iterable<Type> elemTypes = Iterables.transform(map.values(), 
	      new Function<Expression, Type>(){
	    @Override
	    public Type apply(Expression expr) {
	      return expr.getType();
	    }
	  });
	  Iterable<String> elemNames = recomposeFieldNames(typeName, map.keySet());
	  
	  ExpressionManager exprManager = getExpressionManager();
	  RecordType currentMemType = exprManager.recordType(typeName, elemNames, elemTypes);
	
	  return currentMemType;
	}

	protected Map<String, ArrayExpression> getRecordElems(Expression recordState) {
	  Preconditions.checkArgument(recordState.isRecord());
	  Map<String, ArrayExpression> resMap = Maps.newLinkedHashMap();
	  RecordExpression mem = recordState.asRecord();
	  Iterable<String> elemNames = mem.getType().getElementNames();
	  Iterable<String> fieldNames = pickFieldNames(elemNames);
	  assert(Iterables.size(elemNames) == Iterables.size(fieldNames));
	  Iterator<String> elemNameItr = elemNames.iterator();
	  Iterator<String> fieldNameItr = fieldNames.iterator();
	  while(elemNameItr.hasNext() && fieldNameItr.hasNext()) {
	    String elemName = elemNameItr.next();
	    String fieldName = fieldNameItr.next();
	    Expression value = mem.select(elemName);
	    resMap.put(fieldName, value.asArray());
	  }
	  return resMap;
	}
	
  protected String getMemArrElemName(AliasVar var) {
  	StringBuilder sb = new StringBuilder()
  		.append(ARRAY_MEM_PREFIX)
    	.append(Identifiers.ARRAY_NAME_INFIX)
    	.append(var.getName())
    	.append(Identifiers.ARRAY_NAME_INFIX)
    	.append(var.getScope());
  	String res = Identifiers.toValidId(sb.toString());
  	elemArrScopeMap.put(res, var.getScope());
  	return res;
  }
  
  protected String getAllocArrElemName(AliasVar var) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_ALLOC_PREFIX)
    	.append(Identifiers.ARRAY_NAME_INFIX)
    	.append(var.getName())
    	.append(Identifiers.ARRAY_NAME_INFIX)
    	.append(var.getScope());
  	String res = Identifiers.toValidId(sb.toString());
  	elemArrScopeMap.put(res, var.getScope());
  	return res;
  }

	private Iterable<String> pickFieldNames(Iterable<String> fieldsName){
	  return Iterables.transform(fieldsName, 
	      new Function<String, String>(){
	    @Override
	    public String apply(String elemName) {
	      int index = elemName.indexOf(Identifiers.RECORD_SELECT_NAME_INFIX);
	      return elemName.substring(index+1);
	    }
	  });
	}

	private Iterable<String> recomposeFieldNames(final String arrName, Iterable<String> fieldsName){
	  return Iterables.transform(fieldsName, 
	      new Function<String, String>(){
	    @Override
	    public String apply(String elemName) {
	      int index = elemName.indexOf(Identifiers.RECORD_SELECT_NAME_INFIX);
	      StringBuilder sb = new StringBuilder().append(arrName)
	          .append(Identifiers.RECORD_SELECT_NAME_INFIX)
	          .append(elemName.substring(index+1));
	      return sb.toString();
	    }
	  });
	}
}
