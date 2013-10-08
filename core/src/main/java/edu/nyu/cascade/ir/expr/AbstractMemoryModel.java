package edu.nyu.cascade.ir.expr;

//import java.util.List;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.TypeCastAnalysis;
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
  protected static final String TYPE = xtc.Constants.TYPE;
  protected static final String SCOPE = xtc.Constants.SCOPE;
  
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
    
    RecordType memType_1 = rec_1.getType();
    Iterable<String> elemNames_1 = pickFieldNames(memType_1.getElementNames());
    
    RecordType memType_0 = rec_0.getType();
    final Iterable<String> elemNames_0 = pickFieldNames(memType_0.getElementNames());
    
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
    final String arrName_1 = memType_1.getName();
    final String arrName_0 = memType_0.getName();
    
    Iterable<String> elemNames_1_prime = recomposeFieldNames(arrName_1, commonElemNames);
    Iterable<String> elemNames_0_prime = recomposeFieldNames(arrName_0, commonElemNames);
    Iterator<String> elemNames_1_prime_itr = elemNames_1_prime.iterator();
    Iterator<String> elemNames_0_prime_itr = elemNames_0_prime.iterator();
    
    while(elemNames_1_prime_itr.hasNext() && elemNames_0_prime_itr.hasNext()) {
      String elemName_1 = elemNames_1_prime_itr.next();
      String elemName_0 = elemNames_0_prime_itr.next();
      Expression elem = em.ifThenElse(guard, rec_1.select(elemName_1), rec_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    Preconditions.checkArgument(memType_0.getName().startsWith(DEFAULT_MEMORY_STATE_TYPE)
    		|| memType_0.getName().startsWith(DEFAULT_ALLOC_STATE_TYPE));
    String typeName = memType_0.getName().startsWith(DEFAULT_MEMORY_STATE_TYPE) ?
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE) :
    			Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
    Iterable<String> elemNames = recomposeFieldNames(typeName, commonElemNames);   
    RecordType recordType = em.recordType(typeName, elemNames, elemTypes);
    Expression res = em.record(recordType, elems);
    
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
			final Map<String, Expression> map) {
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

	protected Map<String, Expression> getRecordElems(Expression recordState) {
	  Preconditions.checkArgument(recordState.isRecord());
	  Map<String, Expression> resMap = Maps.newLinkedHashMap();
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
	    resMap.put(fieldName, value);
	  }
	  return resMap;
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
