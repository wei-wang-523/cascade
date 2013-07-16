package edu.nyu.cascade.ir.expr;

/** A path factory which extends states along a path using function expressions.
 * Given an ExpressionEncoding which encode program states as an Expression,
 * the path is a program state.
 */

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

public class DynamicPathEncoding extends AbstractPathEncoding {
  public static <Mem extends Expression> DynamicPathEncoding create(
      ExpressionEncoder encoder) {
    return new DynamicPathEncoding(encoder);
  }

  private Expression stateVal;
  private Type stateType;
  private static final String DEFAULT_PATH_STATE = "pathState";
  private static final String DEFAULT_MEMORY_VARIABLE_NAME = "memoryState";
  
  private DynamicPathEncoding(ExpressionEncoder encoder) {
    super(encoder);
    stateVal = null;
    stateType = null;
  }

  @Override
  public Expression assign(Expression pre,
      ExpressionClosure var, ExpressionClosure val) {
    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    MemoryModel mm = getMemoryModel();
    Expression memPrime = mem;
    if(mm instanceof SimpleMemoryModel) {
      memPrime = ((SimpleMemoryModel) mm).updateState(mem);
    }
    memPrime = mm.assign(memPrime, var.eval(memPrime), val.eval(memPrime));
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }

  @Override
  public Expression assume(Expression pre,
      ExpressionClosure expr) {
    BooleanEncoding<?> booleanEncoding = getExpressionEncoding().getBooleanEncoding();
    Preconditions.checkArgument(booleanEncoding.getType().equals(expr.getOutputType()));

    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    MemoryModel mm = getMemoryModel();
    Expression memPrime = mem;
    if(mm instanceof SimpleMemoryModel) {
      memPrime = ((SimpleMemoryModel) mm).updateState(mem);
    }
    
    Expression pcPrime = exprManager.ifThenElse(pc, expr.eval(memPrime).asBooleanExpression(), 
        exprManager.ff());
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pcPrime.getType());
    return exprManager.tuple(stateType, memPrime, pcPrime);
  }
  
  @Override
  public Expression check(Expression pre, ExpressionClosure expr) {
    return pre;
  }

  @Override
  protected BooleanExpression assertionToBoolean(Expression pre,
      ExpressionClosure bool) {
    Preconditions.checkArgument( bool.getOutputType().isBoolean() );
    
    ExpressionManager exprManager = getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    BooleanExpression memorySafe = exprManager.and(getMemoryModel().getAssumptions(mem));
    return exprManager.implies(pc, memorySafe.implies(bool.eval(mem)));
  }

  @Override
  public Expression emptyPath() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memState = getMemoryModel().initialState();
    Expression pcState = getExpressionManager().tt();
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memState.getType(), pcState.getType());
    stateVal = exprManager.tuple(stateType, memState, pcState);
    return stateVal;
  }

  @Override
  public Type getPathType() {
    return stateType;
  }

  @Override
  protected BooleanExpression pathToBoolean(Expression pre) {
    Expression pc = pre.asTuple().getChild(1);
    return pc.asBooleanExpression();
  }
  
  @Override
  public Expression alloc(Expression pre, ExpressionClosure lval,
      ExpressionClosure rval) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    ExpressionManager exprManager = getExpressionManager();
    
    Expression memPrime = getMemoryModel().alloc(mem, lval.eval(mem), rval.eval(mem));
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression declareStruct(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    ExpressionManager exprManager = getExpressionManager();
    
    Expression memPrime = getMemoryModel().declareStruct(mem, ptr.eval(mem), size.eval(mem));
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression declareArray(Expression pre, ExpressionClosure ptr,
      ExpressionClosure size) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    ExpressionManager exprManager = getExpressionManager();
    
    Expression memPrime = getMemoryModel().declareArray(mem, ptr.eval(mem), size.eval(mem));
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }
  
  @Override
  public Expression free(Expression pre, ExpressionClosure ptr) {
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    ExpressionManager exprManager = getExpressionManager();
    
    Expression memPrime = getMemoryModel().free(mem, ptr.eval(mem));
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }

  @Override
  public Expression fieldAssign(Expression pre, ExpressionClosure lval,
      String field, ExpressionClosure rval) {
    ExpressionManager exprManager =  getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression pcPrime = pc;
    if(getMemoryModel() instanceof ReachMemoryModel) {
      ReachMemoryModel mm = (ReachMemoryModel) getMemoryModel();
      Expression memAssume = mm.fieldAssign(mem, lval.eval(mem), field, rval.eval(mem));
      pcPrime = exprManager.ifThenElse(pc, memAssume, exprManager.ff());
    }
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, mem.getType(), pcPrime.getType());
    return exprManager.tuple(stateType, mem, pcPrime);
  }
  
  @Override
  public Expression havoc(Expression pre, ExpressionClosure lval) {
    ExpressionManager exprManager =  getExpressionManager();
    Expression mem = pre.asTuple().getChild(0);
    Expression pc = pre.asTuple().getChild(1);
    
    Expression memPrime = getMemoryModel().havoc(mem, lval.eval(mem));
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, memPrime.getType(), pc.getType());
    return exprManager.tuple(stateType, memPrime, pc);
  }
  
  private Expression getITEExpression(Iterable<? extends Expression> exprs, 
      Iterable<? extends Expression> guards) {
    Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(guards));
    ExpressionManager exprManager = getExpressionManager();
    Expression resExpr = null;
    // have first case as default case
    for(int i = 1; i < Iterables.size(guards); i++) {
      BooleanExpression guard = Iterables.get(guards, i).asBooleanExpression();
      if(i == 1) {
        Expression case_0 = Iterables.get(exprs, 0);
        Expression case_1 = Iterables.get(exprs, 1);
        resExpr = exprManager.ifThenElse(guard, case_1, case_0);
      } else {
        Expression case_1 = Iterables.get(exprs, i);
        resExpr = exprManager.ifThenElse(guard, case_1, resExpr);
      }
    }
    return resExpr;
  }

  @Override
  public Expression noop(Iterable<? extends Expression> prefixes,
      Iterable<? extends Expression> preGuards) {
    Preconditions.checkArgument(Iterables.size(prefixes) == Iterables.size(preGuards));
    ExpressionManager exprManager = getExpressionManager();   
    
    Expression resMemState = null;
    Type memType = prefixes.iterator().next().asTuple().getChild(0).getType();
    if(memType.isTuple()) {
      TupleType tupleType = getMemoryModel().getStateType().asTuple();
      int size = tupleType.getElementTypes().size();
      List<Expression> stateElem = Lists.newArrayListWithCapacity(size);
      for(int i = 0; i < size; i++) {
        List<Expression> mem = Lists.newArrayList();
        for(Expression prefix : prefixes) {
          mem.add(prefix.asTuple().getChild(0).asTuple().getChild(i));   
        }
        stateElem.add(getITEExpression(mem, preGuards));
      }
      resMemState = exprManager.tuple(getMemoryModel().getStateType(), stateElem);
    } else {
      Iterable<RecordExpression> records = Iterables.transform(prefixes, 
          new Function<Expression, RecordExpression>(){
        @Override
        public RecordExpression apply(Expression prefix) {
          return prefix.asTuple().getChild(0).asRecord();
        }
      });
      
      Map<String, List<Expression>> recordMap = Maps.newLinkedHashMap();
      
      /* Initialize record map by the first record */
      RecordExpression firstRecord = records.iterator().next();
      for(int i = 0; i < firstRecord.getType().size(); i++) {
        String elemName = firstRecord.getType().getElementNames().get(i);
        List<Expression> elemExprs = Lists.newArrayList(firstRecord.getChild(i));
        recordMap.put(elemName, elemExprs);
      }
      
      /* Collect record element expressions */
      for(RecordExpression record : records) {
        if(record == firstRecord)  continue;
        for(int i = 0; i < record.getType().size(); i++) {
          String elemName = record.getType().getElementNames().get(i);
          if(recordMap.containsKey(elemName)) {
            List<Expression> elemExprs = recordMap.get(elemName);
            elemExprs.add(record.getChild(i));
            recordMap.put(elemName, elemExprs);
          }
        }
      }
      
      int size = Iterables.size(records);
      List<String> elemNames = Lists.newArrayList();
      List<Expression> elemExprs = Lists.newArrayList();
      /* Filter record map */
      for(Entry<String, List<Expression>> entry : recordMap.entrySet()) {
        if(entry.getValue().size() == size) {
          elemNames.add(entry.getKey());
          elemExprs.add(getITEExpression(entry.getValue(), preGuards));
        }
      }
      
      assert(!elemNames.isEmpty() && !elemExprs.isEmpty());
      Iterable<Type> elemTypes = Iterables.transform(elemExprs, 
          new Function<Expression, Type>() {
        @Override
        public Type apply(Expression expr) {
          return expr.getType();
        }
      });
      
      RecordType type = exprManager.recordType(DEFAULT_MEMORY_VARIABLE_NAME, elemNames, elemTypes);
      resMemState = exprManager.record(type, elemExprs);
    }
    
    List<Expression> pc = Lists.newArrayList();
    for(Expression prefix : prefixes) {
      pc.add(prefix.asTuple().getChild(1));
    }
    Expression resPC = getITEExpression(pc, preGuards); 
    
    stateType = exprManager.tupleType(DEFAULT_PATH_STATE, resMemState.getType(), resPC.getType());
    return exprManager.tuple(stateType, resMemState, resPC);
  }
}
