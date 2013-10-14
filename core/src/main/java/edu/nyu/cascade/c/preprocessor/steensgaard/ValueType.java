package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.util.EqualsUtil;

public final class ValueType {
  
  enum ValueTypeKind {
    LOCATION,
    FUNCTION,
    BOTTOM
  };
  
  private final ValueTypeKind kind;
  private final ImmutableList<ECR> operands;
  
  protected ValueType(ValueTypeKind _kind, ECR ... args) {
    kind = _kind;
    operands = ImmutableList.copyOf(args);
  }
  
  protected ValueType(ValueTypeKind _kind, List<ECR> args) {
    kind = _kind;
    operands = ImmutableList.copyOf(args);
  }  
  
  protected ValueTypeKind getKind() {
    return kind;
  }
  
  protected ECR getOperand(int i) {
    Preconditions.checkArgument(i >=0 && i < operands.size());
    return operands.get(i);
  }
  
  protected Iterable<ECR> getOperands() {
    return operands;
  }
  
  protected int getOperandSize() {
    Preconditions.checkArgument(operands != null);
    return operands.size();
  }
  
  protected static ValueType bottom() {
    ValueType v = new ValueType(ValueTypeKind.BOTTOM);
    return v;
  }
  
  protected static ValueType function(ValueType function, List<ECR> args, ECR retValues) {
    List<ECR> operands;
    if(args == null){
      operands = ImmutableList.<ECR> builder().add(retValues).build();
    } else {
      operands = ImmutableList.<ECR> builder().add(retValues).addAll(args).build();
    }
    ValueType v = new ValueType(ValueTypeKind.FUNCTION, operands);
    return v;
  }
  
  protected static ValueType location(ECR function, ECR location) {
    ValueType v = new ValueType(ValueTypeKind.LOCATION, function, location);
    return v;
  }
  
  @Override
  public boolean equals(Object t) {
    if(!(t instanceof ValueType))   return false;
    ValueType vt = (ValueType) t;
    if(!kind.equals(vt.getKind()))  return false;
    return EqualsUtil.areEqual(operands, vt.getOperands());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    switch(kind) {
    case BOTTOM: {
      sb.append("BOTTOM");
      break;
    }
    case LOCATION: {
      sb.append("REF ( ")
        .append(getOperand(0).toStringShort())
        .append(" * ")
        .append(getOperand(1).toStringShort())
        .append(" )");
      break;
    }
    case FUNCTION: {
      sb.append("LAM ( ");
      for(int i = 0; i < operands.size()-1; i++) {
        sb.append(operands.get(i).toStringShort());
      }
      sb.append(") (").append(operands.get(operands.size()-1)).append(")");
      break;
    }
    default:
      break;
    }
    
    return sb.toString();
  }
}
