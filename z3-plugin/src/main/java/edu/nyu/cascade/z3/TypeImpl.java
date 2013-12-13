package edu.nyu.cascade.z3;

import java.util.List;

import com.google.common.base.Preconditions;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.UninterpretedSort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.AddableType;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.ComparableType;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.MultiplicativeType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;

public abstract class TypeImpl implements Type {
  static interface BinaryConstructionStrategy {
    Sort apply(Context Ctx, Expr arg1, Expr arg2);
  }
  static interface UnaryConstructionStrategy {
    Sort apply(Context Ctx, Expr arg);
  }
  
  private Sort z3_type = null;
  private Sort z3_unresolved_datatype = null;
  private ExpressionManagerImpl em = null;
//  private ExpressionImpl typeExpression;

  protected TypeImpl(ExpressionManagerImpl em, BinaryConstructionStrategy strategy,
      Expression expr1, Expression expr2) {
    this.em = em;
    Expr z3Expr1 = em.importExpression(expr1).getZ3Expression();
    Expr z3Expr2 = em.importExpression(expr2).getZ3Expression();

    try {
      this.z3_type = strategy.apply(em.getTheoremProver().getZ3Context(),
          z3Expr1, z3Expr2);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  protected TypeImpl(ExpressionManagerImpl em, UnaryConstructionStrategy strategy,
      Expression expr) {
    this.em = em;
    Expr z3Expr = em.importExpression(expr).getZ3Expression();

    try {
      this.z3_type = strategy.apply(em.getTheoremProver().getZ3Context(),
        z3Expr);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  protected TypeImpl(ExpressionManagerImpl em) {
    this.em = em;
  }

  @Override
  public boolean equals(Object obj) {
    if(obj instanceof FunctionDeclarator) {
      if(!(this instanceof FunctionDeclarator)) return false;
      
      FunctionDeclarator thisF = (FunctionDeclarator) this;
      FunctionDeclarator thatF = (FunctionDeclarator) obj;
      
      if(thisF.getName().equals(thatF.getName()) && 
          thisF.getArgTypes().equals(thatF.getArgTypes()) &&
            thisF.getRangeType().equals(thatF.getRangeType()))
        return true;
      else
        return false;
    }
    
    if (obj instanceof TypeImpl) {
      if(getZ3Type() != null)
        return getZ3Type().equals(((TypeImpl) obj).getZ3Type());
      else
        return getZ3UnresolvedDatatype().equals(((TypeImpl) obj).getZ3UnresolvedDatatype());
    }
    return super.equals(obj);
  }

  public Sort getZ3Type() {
    return z3_type;
  }
  
  public Sort getZ3UnresolvedDatatype() {
    return z3_unresolved_datatype;
  }

  public abstract String getName();
  
  @Override
  public ExpressionManagerImpl getExpressionManager() {
    return em;
  }

/*  @Override
  public ExpressionImpl getTypeExpression() {
    return typeExpression;
  }*/
  
  @Override
  public int hashCode() {
    return getZ3Type().hashCode();
  }
  
  /** {@inheritDoc}
   * 
   * This implementation handles variable expressions only. Other
   * kinds of expressions should be handled by their respective 
   * concrete types, which can call this method as a default case.
   */
  @Override
  public ExpressionImpl importExpression(Expression expression) {
    final int arity = expression.getArity();
    switch( expression.getKind() ) {  
    case SUBST:
      assert( arity % 2 == 1 );
      Expression orig = (Expression) expression.getChild(0);
      List<? extends Expression> oldVars = expression
          .getChildren()
          .subList(1, arity / 2 + 1);
      List<? extends Expression> newVars = expression
          .getChildren()
          .subList(arity / 2 + 1, arity);
      return ExpressionImpl.mkSubst(getExpressionManager(),orig,oldVars,newVars);
      
    case VARIABLE:
      assert( arity == 0 );
      return VariableExpressionImpl.valueOf(getExpressionManager(),expression);
    default:
      throw new IllegalArgumentException("Unexpected kind: "
          + expression + "{ " + expression.getKind() + "}");
    }
  }

  protected void setZ3Type(Sort z3_type) {
    this.z3_type = z3_type;
  }
  
  protected void setZ3UnresolvedDatatype(UninterpretedSort z3_unresolved_datatype) {
    this.z3_unresolved_datatype = z3_unresolved_datatype;
  }

/*  protected void setTypeExpression(ExpressionImpl typeExpression) {
    this.typeExpression = typeExpression;
  }*/
  
  @Override 
  public String toString() {
    return getZ3Type().toString();
  }
  
  @Override
  public abstract VariableExpressionImpl variable(String name, boolean fresh);

  @Override
  public FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars, Expression body) {
    throw new UnsupportedOperationException("lambda expression is not supported in z3");
  }

  @Override
  public FunctionExpression
   lambda(
      VariableExpression var,
      Expression body) {
    throw new UnsupportedOperationException("lambda expression is not supported in z3");
  }
  
  TypeImpl subType(ExpressionManagerImpl exprManager, Expr expr) {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isAddableType() {
    return this instanceof AddableType;
  }

  @Override
  public AddableType asAddableType() {
    Preconditions.checkState(isAddableType());
    return (AddableType)this;
  }

  @Override
  public boolean isComparableType() {
    return this instanceof ComparableType;
  }

  @Override
  public ComparableType asComparableType() {
    Preconditions.checkState(isComparableType());
    return (ComparableType)this;
  }

  @Override
  public boolean isMultiplicativeType() {
    return this instanceof MultiplicativeType;
  }

  @Override
  public MultiplicativeType asMultiplicativeType() {
    Preconditions.checkState(isMultiplicativeType());
    return (MultiplicativeType)this;
  }

  @Override
  public boolean isBitVectorType() {
    return this instanceof BitVectorType;
  }

  @Override
  public BitVectorType asBitVectorType() {
    Preconditions.checkState(isBitVectorType());
    return (BitVectorType)this;
  }

  @Override
  public boolean isBoolean() {
    return this instanceof BooleanType;
  }

  @Override
  public BooleanType asBooleanType() {
    Preconditions.checkState(isBoolean());
    return (BooleanType)this;
  }

  @Override
  public boolean isArrayType() {
    return this instanceof ArrayType;
  }

  @Override
  public ArrayType asArrayType() {
    Preconditions.checkState(isArrayType());
    return (ArrayType)this;
  }
  
  @Override
  public boolean isInductive() {
    return this instanceof InductiveType;
  }

  @Override
  public InductiveType asInductive() {
    Preconditions.checkState(isInductive());
    return (InductiveType)this;
  }

  @Override
  public boolean isFunction() {
    return this instanceof FunctionType;
  }

  @Override
  public FunctionType asFunction() {
    Preconditions.checkState(isFunction());
    return (FunctionType)this;
  }

  @Override
  public boolean isInteger() {
    return this instanceof IntegerType;
  }

  @Override
  public IntegerType asInteger() {
    Preconditions.checkState(isInteger());
    return (IntegerType)this;
  }
  
  @Override
  public boolean isRational() {
    return this instanceof RationalType;
  }

  @Override
  public RationalType asRational() {
    Preconditions.checkState(isRational());
    return (RationalType)this;
  }
  
  @Override
  public boolean isTuple() {
    return this instanceof TupleType;
  }
  
  @Override
  public TupleType asTuple() {
    Preconditions.checkState(isTuple());
    return (TupleType)this;
  }
  
  @Override
  public boolean isRecord() {
    return this instanceof RecordType;
  }
  
  @Override
  public RecordType asRecord() {
    Preconditions.checkState(isRecord());
    return (RecordType)this;
  }
  
  @Override
  public UninterpretedType asUninterpreted() {
    Preconditions.checkState(isUninterpreted());
    return (UninterpretedType)this;
  }
  
  @Override
  public boolean isUninterpreted() {
    return this instanceof UninterpretedType;
  }
  
  abstract ExpressionImpl create(Expr res, Expression oldExpr, 
  		Iterable<? extends ExpressionImpl> children) ;
}
