package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

final class ArrayTypeImpl extends TypeImpl implements ArrayType {
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
      edu.nyu.acsys.CVC4.Type indexCvc4Type = exprManager.toCvc4Type(indexType);
      edu.nyu.acsys.CVC4.Type elementCvc4Type = exprManager.toCvc4Type(elementType);
      setCVC4Type(exprManager.getTheoremProver().getCvc4ExprManager().mkArrayType(indexCvc4Type, 
                elementCvc4Type));
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
    return ArrayVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public ArrayBoundVariableImpl boundVar(String name, boolean fresh) {
    return new ArrayBoundVariableImpl(getExpressionManager(), name, this, fresh);
  }

  @Override
	public ArrayExpression boundExpression(String name, int index, boolean fresh) {
  	return boundVar(name, fresh);
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
  public ExpressionImpl importExpression(
      Expression expression) {
    switch( expression.getKind() ) {
/*    case ARRAY_INDEX:
      assert( expression.getArity() == 2);
      return index((IExpression) expression.getChild(0),
          (IExpression) expression.getChild(1));*/
      
    case ARRAY_UPDATE:
      assert( expression.getArity() == 3 );
      return ArrayExpressionImpl.mkUpdate(getExpressionManager(), (Expression) expression.getChild(0),
          (Expression) expression.getChild(1), (Expression) expression
              .getChild(2));
    
    default:
      return super.importExpression(expression);
    }
  }

	@Override
  public Expression index(Expression array, Expression index) {
	  return ArrayExpressionImpl.mkArrayIndex(getExpressionManager(), array, index);
  }

	@Override
  public ArrayExpression update(Expression array, Expression index,
      Expression value) {
	  return ArrayExpressionImpl.mkUpdate(getExpressionManager(), array, index, value);
  }

	@Override
  public ArrayExpression storeAll(Expression expr, ArrayType arrayType) {
	  return ArrayExpressionImpl.mkStoreAll(getExpressionManager(), expr, arrayType);
  }

	@Override
	ArrayExpressionImpl createExpression(Expr res, Expression e, Kind kind,
			Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isArray());
		return ArrayExpressionImpl.create(getExpressionManager(), kind, 
				res, e.getType().asArrayType(), children);
	}
}
