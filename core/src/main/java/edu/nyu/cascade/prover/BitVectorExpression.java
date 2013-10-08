package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.BitVectorType;


public interface BitVectorExpression extends Expression {
  BitVectorExpression and(Expression a) ;
  BitVectorExpression concat(Expression a) ;

  BitVectorExpression extract(int i, int j) ;

  int getSize();
  @Override BitVectorType getType();
  
  /**
   * Returns a new Boolean expression that represents an unsigned greater than  
   * (>) over this expression and a given bit vector <code>e</code>. 
   * @param e expression to compare to
   * @return the greater than expression
   */
  BooleanExpression greaterThan(Expression e) ;
  
  /**
   * Returns a new Boolean expression that represents an unsigned greater than or equal
   * comparison (>=) over this expression and a given bit vector expression <code>e</code>. 
   * @param e expression to compare to
   * @return the greater than or equal expression
   */
  BooleanExpression greaterThanOrEqual(Expression e) ;

  /**
   * Returns a new Boolean expression that represents an unsigned less than comparison 
   * (<) over this expression and a given bit vector expression <code>e</code>. 
   * @param e expression to compare to
   * @return the less than expression
   */
  BooleanExpression lessThan(Expression e) ;

  /**
   * Returns a new Boolean expression that represents an unsigned less than or equal
   * comparison (<=) over this expression and a given bit vector expression <code>e</code>. 
   * @param e expression to compare to
   * @return the less than expression
   */
  BooleanExpression lessThanOrEqual(Expression e) ;
  
  BitVectorExpression minus(Expression a) ;
  BitVectorExpression nand(Expression a) ;
  BitVectorExpression nor(Expression a) ;
  BitVectorExpression not() ;
  BitVectorExpression or(Expression a) ;
  BitVectorExpression plus(int size, Expression a);
  BitVectorExpression plus(int size, 
      Expression... args);
  BitVectorExpression plus(int size, Iterable<? extends Expression> args);
  
  BitVectorExpression times(int size, Expression a) ;
  
  BitVectorExpression divides(Expression a);
  BitVectorExpression signedDivides(Expression a);
  BitVectorExpression rems(Expression a);
  BitVectorExpression signedRems(Expression a);
  BitVectorExpression xnor(Expression a) ;
  BitVectorExpression xor(Expression a) ;
  BitVectorExpression lshift(Expression a);
  BitVectorExpression rshift(Expression a);
  BitVectorExpression zeroExtend(int size);
  BitVectorExpression signExtend(int size);
  BitVectorExpression uminus();
}
