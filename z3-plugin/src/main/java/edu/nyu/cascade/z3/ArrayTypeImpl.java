package edu.nyu.cascade.z3;

import com.google.common.collect.ComputationException;
import com.google.inject.internal.Preconditions;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public final class ArrayTypeImpl extends TypeImpl implements ArrayType {
  private final Type indexType;
  private final Type elementType;

  static ArrayTypeImpl create(
      ExpressionManagerImpl exprManager, Type index, Type elem) {
    return new ArrayTypeImpl(exprManager, index, elem);
  }
  
  static ArrayTypeImpl valueOf(
      ExpressionManagerImpl exprManager, Type type) {
    Preconditions.checkArgument(type.isArrayType());
    if (type instanceof ArrayTypeImpl) {
      return (ArrayTypeImpl) type;
    } else {
      ArrayType arrayType = type.asArrayType();
      return create(exprManager, arrayType.getIndexType(),
          arrayType.getElementType());
    }
  }

  private ArrayTypeImpl(ExpressionManagerImpl exprManager, Type index, Type elem) {
    super(exprManager);
    this.indexType = index;
    this.elementType = elem;
    try {
      Sort indexZ3Type = exprManager.toZ3Type(indexType);
      Sort elementZ3Type = exprManager.toZ3Type(elementType);
      TheoremProverImpl.debugCall("arrayType(%s,%s)", indexZ3Type, elementZ3Type);
      setZ3Type(exprManager.getTheoremProver().getZ3Context().MkArraySort(indexZ3Type, elementZ3Type));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.ARRAY;
  }

  @Override
  public ArrayVariableImpl variable(String name, boolean fresh) {
    try {
      return ArrayVariableImpl.create(getExpressionManager(),name,this,fresh);
    } catch (Z3Exception e) {
      throw new ComputationException(e);
    }
  }

  @Override
  public Type getElementType() {
    return elementType;
  }


  @Override
  public Type getIndexType() {
    return indexType;
  }

  @Override
  public String toString() {
    return "ARRAY " + getIndexType() + " OF "+ getElementType() ;
  }

  @Override
  public String getName() {
    return toString();
  }

  @Override
  public ExpressionImpl index(Expression array,
      Expression index) {
    return ExpressionImpl.mkArrayIndex(getExpressionManager(),array, index);
  }

  @Override
  public ExpressionImpl importExpression(
      Expression expression) {
    switch( expression.getKind() ) {
/*    case ARRAY_INDEX:
      assert( expression.getArity() == 2);
      return index((IExpression) expression.getChild(0),
          (IExpression) expression.getChild(1));*/
      
    case ARRAY_UPDATE:
      assert( expression.getArity() == 3 );
      return update((Expression) expression.getChild(0),
          (Expression) expression.getChild(1), (Expression) expression
              .getChild(2));
    
    default:
      return super.importExpression(expression);
    }
  }

  @Override
  public ArrayExpressionImpl update(Expression array,
      Expression index, Expression value) {
    return ArrayExpressionImpl.mkUpdate(getExpressionManager(), array, index, value);
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }
}