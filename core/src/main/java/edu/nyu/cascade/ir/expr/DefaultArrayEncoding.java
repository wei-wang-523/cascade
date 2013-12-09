package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.EqualsUtil;
import edu.nyu.cascade.util.HashCodeUtil;

public class DefaultArrayEncoding implements ArrayEncoding<ArrayExpression> {
  private final ExpressionManager exprManager;
  
  public DefaultArrayEncoding(ExpressionManager exprManager) {
    this.exprManager = exprManager;
  }

  @Override
  public Instance<ArrayExpression> getInstance(
      TypeEncoding<?> indexEncoding, TypeEncoding<?> elementEncoding) {
    return new DefaultArrayInstance(exprManager, indexEncoding, elementEncoding);
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    return x.isArray();
/*    List<TypeEncoding<?>> subEncodings = x.isArray();
    if( subEncodings.size() != 2 ) {
      return false;
    }
    TypeEncoding<?> indexEncoding = subEncodings.get(0);
    TypeEncoding<?> elementEncoding = subEncodings.get(1);
    return getInstance(indexEncoding, elementEncoding).equals(x.getTypeEncoding());
*/  }

  @Override
  public ArrayExpression ofExpression(Expression expr) {
    Preconditions.checkArgument(expr.isArray());
    return expr.asArray();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return exprManager;
  }

  @Override
  public Expression index(ArrayExpression array, Expression i) {
    return array.index(i);
  }

  @Override
  public ArrayExpression update(ArrayExpression array, Expression index,
      Expression elem) {
    return array.update(index, elem);
  }

/*  @Override
  public DefaultArrayInstance<?,?> getInstance(Type indexType,
      Type<E> elemType) {
    return new DefaultArrayInstance<I,E>(exprManager, indexType, elemType);
  }
*/   
}

class DefaultArrayInstance implements ArrayEncoding.Instance<ArrayExpression> {
  private final ExpressionManager exprManager;
  private final TypeEncoding<?> indexEncoding, elementEncoding;

  public DefaultArrayInstance(ExpressionManager exprManager, TypeEncoding<?> indexEncoding, TypeEncoding<?> elementEncoding) {
    this.exprManager = exprManager;
    this.indexEncoding = indexEncoding;
    this.elementEncoding = elementEncoding;
  }

  @Override
  public BooleanExpression eq(ArrayExpression lhs, ArrayExpression rhs) {
    return lhs.eq(rhs);
  }
  
  public boolean equals(Object obj) {
    if( this == obj ) { 
      return true;
    }
    if( !(obj instanceof DefaultArrayInstance) ) {
      return false;
    }
    DefaultArrayInstance instance = (DefaultArrayInstance)obj;
    return EqualsUtil.areEqual(exprManager, instance.exprManager)
        && EqualsUtil.areEqual(indexEncoding, instance.indexEncoding)
        && EqualsUtil.areEqual(elementEncoding, instance.elementEncoding);
  }

  @Override
  public TypeEncoding<?> getElementEncoding() {
    return elementEncoding;
  }

  public ExpressionManager getExpressionManager() {
    return exprManager;
  }

  @Override
  public TypeEncoding<?> getIndexEncoding() {
    return indexEncoding;
  }

  @Override
  public ArrayType getType() {
    return exprManager.arrayType(getIndexEncoding().getType(), getElementEncoding().getType());
  }

  @Override
  public int hashCode() {
    int hash = HashCodeUtil.SEED;
    HashCodeUtil.hash(hash, exprManager);
    HashCodeUtil.hash(hash, indexEncoding);
    HashCodeUtil.hash(hash, elementEncoding);
    return hash;
  }

  @Override
  public Expression index(ArrayExpression array, Expression index) {
//    Preconditions.checkArgument( indexEncoding.isEncodingFor(index) );
//    return mkValue(getElementEncoding(), array.index(index.getValue()));
    return array.index(index);
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    if( !x.isArray() ) {
      return false;
    }
    ArrayExpression ax = x.asArray();
    return ax.getIndexType().equals( indexEncoding.getType() ) &&
      ax.getElementType().equals( elementEncoding.getType() );
  }

/*  private EncodingValue mkEncodingValue(Expression<?> x) {
    return new EncodingValueImpl(x,this);
  }
  
  private <T> EncodingValue mkValue(TypeEncoding<T> encoding, Expression<?> element) {
    return encoding.toEncodingValue( encoding.ofExpression(element) );
  }*/

  @Override
  public ArrayExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isArray());
    return x.asArray();
  }
  
  @Override
  public ArrayExpression symbolicConstant(String name, boolean fresh) {
    return variable(name, fresh);
  }

  @Override
  public ArrayExpression toArrayExpression(ArrayExpression array) {
    return array;
  }

/*  @Override
  public EncodingValue toEncodingValue(ArrayExpression x) {
    return mkEncodingValue(x);
  }
*/
/*  @Override
  public Expression<?> toExpression(ArrayExpression x) {
    return x;
  }
*/
  @Override
  public VariableExpression toVariable(ArrayExpression x) {
    Preconditions.checkArgument(x.isVariable());
    return x.asVariable();
  }

  @Override
  public ArrayExpression update(ArrayExpression array,
      Expression index, Expression val) {
/*    Preconditions.checkArgument( indexEncoding.isEncodingFor(index) );
    Preconditions.checkArgument( elementEncoding.isEncodingFor(val) );
*/    
    return array.update(index, val);
  }

  @Override
  public ArrayExpression variable(String name, boolean fresh) {
    return exprManager.arrayVar(name, getIndexEncoding().getType(), getElementEncoding().getType(), fresh);
  }
}
