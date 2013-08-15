package edu.nyu.cascade.ir.expr;

//import java.util.List;

import java.util.concurrent.ExecutionException;

import xtc.type.*;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractMemoryModel implements MemoryModel {
  private static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  
  private final LoadingCache<xtc.type.Type, String> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<xtc.type.Type, String>(){
        public String load(xtc.type.Type type) {
          return parseTypeName(type);
        }
      });
  
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
  public Expression castConstant(int value, xtc.type.Type type) {
    return encoding.integerConstant(value);
  }
  
  @Override
  public Expression castExpression(Expression src, xtc.type.Type type) {
    return src;
  }
  
  @Override
  public int getSizeofType(xtc.type.Type t) {
    if (t.isInteger()) {
      return 1;
    } else if (t.isPointer()) {
      return 1;
    } else if (t.isStruct()) {
      int res = 0;
      for(VariableT elem : t.toStruct().getMembers()) {
        res += getSizeofType(elem.getType());
      }
      return res;
    } else if(t.isUnion()) {
      int res = 0;
      for(VariableT elem : t.toUnion().getMembers()) {
        res = Math.max(res, getSizeofType(elem.getType()));
      }
      return res;
    } else if(t.isArray()) {
      ArrayT array = t.toArray();
      return (int) (array.getLength()) * getSizeofType(array.getType());
    } else if(t.isAlias() || t.isVariable()) {
      return getSizeofType(t.resolve());
    } else if(t.isAnnotated()) {
      return getSizeofType(t.deannotate());
    } else {
      throw new IllegalArgumentException("Unknown type.");
    }
  }
  
  public String getTypeName(xtc.type.Type type) {
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
          xtc.type.Type baseType = ref.getBase().getType();
          String fieldName = ref.getField();
          sb.append(parseTypeName(baseType)).append('#').append(fieldName);
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
      sb.append('$').append("IntegerT");
    } else if(type.isLabel()){
      sb.append('$').append(type.toLabel().getName());
    } else {
      throw new IllegalArgumentException("Cannot parse type " + type.getName());
    }
    return sb.toString();
  }
}
