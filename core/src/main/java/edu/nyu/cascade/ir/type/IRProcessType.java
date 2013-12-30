package edu.nyu.cascade.ir.type;


public final class IRProcessType extends IRType {
  private static final IRProcessType unparameterized = new IRProcessType();
  
  public static IRProcessType unparameterized() {
    return unparameterized;
  }
  
  public static IRProcessType create(String parameter, IRRangeType<?> parameterType) {
    return new IRProcessType(parameter, parameterType);
  }
  
  private final String parameter;
  private final IRRangeType<?> parameterType;

  private IRProcessType() {
    this.parameter = null;
    this.parameterType = null;
  }
  
  private IRProcessType(String parameter, IRRangeType<?> parameterType) {
    this.parameter = parameter;
    this.parameterType = parameterType;
  }

  @Override
  public Kind getKind() {
    return Kind.PROCESS;
  }

  public String getParameter() {
    return parameter;
  }

  public IRRangeType<?> getParameterType() {
    return parameterType;
  }

  public boolean isParameterized() {
    return parameter!=null;
  }
  
  @Override
  public String toString() {
    if (parameter == null) {
      return "process";
    } else {
      return "process(" + parameter + ":" + parameterType + ")";
    }
  }
}
