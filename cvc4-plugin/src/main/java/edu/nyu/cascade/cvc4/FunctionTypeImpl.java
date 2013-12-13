package edu.nyu.cascade.cvc4;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public final class FunctionTypeImpl extends TypeImpl
    implements FunctionType {
  static FunctionTypeImpl create(final ExpressionManagerImpl exprManager,
      Iterable<? extends Type> argTypes, Type range) {
    Iterable<TypeImpl> argTypes1 = Iterables.transform(argTypes,
        new Function<Type, TypeImpl>() {
          @Override
          public TypeImpl apply(Type t) {
            return exprManager.importType(t);
          }
        });
    return new FunctionTypeImpl(exprManager,argTypes1,exprManager.importType(range));
  }
  
  static FunctionTypeImpl valueOf(
      ExpressionManagerImpl exprManager, Type t) {
    if (t instanceof FunctionTypeImpl) {
      return (FunctionTypeImpl) t;
    } else {
      return create(exprManager, ((FunctionType) t).getArgTypes(),
          ((FunctionType) t).getRangeType());
    }
  }
  
  private final ImmutableList<TypeImpl> argTypes;
  private final TypeImpl rangeType;
  
  private FunctionTypeImpl(final ExpressionManagerImpl exprManager,
      Iterable<? extends TypeImpl> argTypes, TypeImpl range) {
    super(exprManager);
    this.argTypes = ImmutableList.copyOf(argTypes);
    this.rangeType = range;
    try {
      vectorType argTypes1 = new vectorType();
      for(TypeImpl argType : argTypes) {
        argTypes1.add(exprManager.toCvc4Type(argType));
      }
      edu.nyu.acsys.CVC4.Type rangeType1 = exprManager.toCvc4Type(rangeType);
      setCVC4Type(exprManager.getTheoremProver().getCvc4ExprManager().mkFunctionType(argTypes1,
                rangeType1));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }  
  
  @Override
  public String getName() {
    return "(" + Joiner.on(",").join(argTypes) + ") -> " + rangeType.getName();
  }
  
  @Override
  public ExpressionImpl apply(FunctionExpression fun,
      Iterable<? extends Expression> args) {
    return ExpressionImpl.mkFunApply(getExpressionManager(),fun,args);
  }
  
  @Override
  public ExpressionImpl apply(FunctionExpression fun, 
  		Expression arg1, Expression... otherArgs) {
    Preconditions.checkArgument(getArity() == otherArgs.length + 1);
    return ExpressionImpl.mkFunApply(getExpressionManager(), fun,
        Lists.asList(arg1, otherArgs));
  }
  
  @Override
  public Type getArgTypeAtIndex(int index) {
    return argTypes.get(index);
  }

  @Override
  public ImmutableList<? extends Type> getArgTypes() {
    return argTypes;
  }

  @Override
  public int getArity() {
    return argTypes.size();
  }

  @Override
  public Type getRangeType() {
    return rangeType;
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.FUNCTION;
  }

  @Override
  public FunctionVariableImpl variable(String name, boolean fresh) {
    return FunctionVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public FunctionBoundVariableImpl boundVariable(String name, boolean fresh) {
    return FunctionBoundVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public Expression apply(Expression arg1, Expression... rest) {
    throw new UnsupportedOperationException("cvc4 does not support it.");
  }

  @Override
  public Expression apply(Iterable<? extends Expression> args) {
  	throw new UnsupportedOperationException("cvc4 does not support it.");
  }
}
