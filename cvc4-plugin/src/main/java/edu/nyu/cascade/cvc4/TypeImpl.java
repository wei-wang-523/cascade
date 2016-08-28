package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.DatatypeUnresolvedType;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
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
import edu.nyu.cascade.prover.type.ScalarType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;

abstract class TypeImpl implements Type {
	static interface BinaryConstructionStrategy {
		edu.nyu.acsys.CVC4.Type apply(ExprManager em, Expr arg1, Expr arg2);
	}

	static interface UnaryConstructionStrategy {
		edu.nyu.acsys.CVC4.Type apply(ExprManager em, Expr arg);
	}

	private edu.nyu.acsys.CVC4.Type cvc4_type = null;
	private DatatypeUnresolvedType cvc4_unresolved_datatype = null;
	private ExpressionManagerImpl em = null;

	protected TypeImpl(ExpressionManagerImpl em,
			BinaryConstructionStrategy strategy, Expression expr1, Expression expr2) {
		this.em = em;
		Expr cvc4Expr1 = em.importExpression(expr1).getCvc4Expression();
		Expr cvc4Expr2 = em.importExpression(expr2).getCvc4Expression();

		this.cvc4_type = strategy.apply(em.getTheoremProver().getCvc4ExprManager(),
				cvc4Expr1, cvc4Expr2);
	}

	protected TypeImpl(ExpressionManagerImpl em,
			UnaryConstructionStrategy strategy, Expression expr) {
		this.em = em;
		Expr cvc4Expr = em.importExpression(expr).getCvc4Expression();

		this.cvc4_type = strategy.apply(em.getTheoremProver().getCvc4ExprManager(),
				cvc4Expr);
	}

	protected TypeImpl(ExpressionManagerImpl em) {
		this.em = em;
	}

	abstract String getName();

	abstract ExpressionImpl createExpression(Expr res, Expression e, Kind subst,
			Iterable<ExpressionImpl> importExpressions);

	edu.nyu.acsys.CVC4.Type getCVC4Type() {
		return cvc4_type;
	}

	DatatypeUnresolvedType getCVC4UnresolvedDatatype() {
		return cvc4_unresolved_datatype;
	}

	void setCVC4Type(edu.nyu.acsys.CVC4.Type cvc4_type) {
		this.cvc4_type = cvc4_type;
	}

	void setCVC4UnresolvedDatatype(
			DatatypeUnresolvedType cvc4_unresolved_datatype) {
		this.cvc4_unresolved_datatype = cvc4_unresolved_datatype;
	}

	/**
	 * Construct the type given a sub-type.
	 * 
	 * @param em
	 *          the validity checker
	 * @param subType
	 *          sub-type to use for construction
	 * @return the type @ TODO
	 */
	/*
	 * protected TypeMut construct(ExprManager em, TypeMut subType) { throw new
	 * TheoremProverException("Type construction of this kind is not supported.");
	 * }
	 */

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof TypeImpl) {
			if (getCVC4Type() != null)
				return getCVC4Type().equals(((TypeImpl) obj).getCVC4Type());
			else
				return getCVC4UnresolvedDatatype()
						.equals(((TypeImpl) obj).getCVC4UnresolvedDatatype());
		}
		return super.equals(obj);
	}

	@Override
	public ExpressionManagerImpl getExpressionManager() {
		return em;
	}

	/*
	 * @Override public ExpressionImpl getTypeExpression() { return
	 * typeExpression; }
	 */

	@Override
	public int hashCode() {
		return getCVC4Type().hashCode();
	}

	/**
	 * {@inheritDoc}
	 * 
	 * This implementation handles variable expressions only. Other kinds of
	 * expressions should be handled by their respective concrete types, which can
	 * call this method as a default case.
	 */
	@Override
	public ExpressionImpl importExpression(Expression expression) {
		final int arity = expression.getArity();
		switch (expression.getKind()) {
		// case CONSTANT:

		case SUBST:
			assert (arity % 2 == 1);
			Expression orig = (Expression) expression.getChild(0);
			List<? extends Expression> oldVars = expression.getChildren().subList(1,
					arity / 2 + 1);
			List<? extends Expression> newVars = expression.getChildren()
					.subList(arity / 2 + 1, arity);
			return ExpressionImpl.mkSubst(getExpressionManager(), orig, oldVars,
					newVars);

		case VARIABLE:
			assert (arity == 0);
			return VariableExpressionImpl.valueOf(getExpressionManager(), expression);
		default:
			throw new IllegalArgumentException(
					"Unexpected kind: " + expression + "{ " + expression.getKind() + "}");
		}
	}

	@Override
	public String toString() {
		return getCVC4Type().toString();
	}

	@Override
	public boolean isAddableType() {
		return this instanceof AddableType;
	}

	@Override
	public AddableType asAddableType() {
		Preconditions.checkState(isAddableType());
		return (AddableType) this;
	}

	@Override
	public boolean isComparableType() {
		return this instanceof ComparableType;
	}

	@Override
	public ComparableType asComparableType() {
		Preconditions.checkState(isComparableType());
		return (ComparableType) this;
	}

	@Override
	public boolean isScalarType() {
		return this instanceof ScalarType;
	}

	@Override
	public ScalarType asScalarType() {
		Preconditions.checkState(isScalarType());
		return (ScalarType) this;
	}

	@Override
	public boolean isMultiplicativeType() {
		return this instanceof MultiplicativeType;
	}

	@Override
	public MultiplicativeType asMultiplicativeType() {
		Preconditions.checkState(isMultiplicativeType());
		return (MultiplicativeType) this;
	}

	@Override
	public boolean isBitVectorType() {
		return this instanceof BitVectorType;
	}

	@Override
	public BitVectorType asBitVectorType() {
		Preconditions.checkState(isBitVectorType());
		return (BitVectorType) this;
	}

	@Override
	public boolean isBoolean() {
		return this instanceof BooleanType;
	}

	@Override
	public BooleanType asBooleanType() {
		Preconditions.checkState(isBoolean());
		return (BooleanType) this;
	}

	@Override
	public boolean isArrayType() {
		return this instanceof ArrayType;
	}

	@Override
	public ArrayType asArrayType() {
		Preconditions.checkState(isArrayType());
		return (ArrayType) this;
	}

	@Override
	public boolean isInductive() {
		return this instanceof InductiveType;
	}

	@Override
	public InductiveType asInductive() {
		Preconditions.checkState(isInductive());
		return (InductiveType) this;
	}

	@Override
	public boolean isFunction() {
		return this instanceof FunctionType;
	}

	@Override
	public FunctionType asFunction() {
		Preconditions.checkState(isFunction());
		return (FunctionType) this;
	}

	@Override
	public boolean isInteger() {
		return this instanceof IntegerType;
	}

	@Override
	public IntegerType asInteger() {
		Preconditions.checkState(isInteger());
		return (IntegerType) this;
	}

	@Override
	public boolean isRational() {
		return this instanceof RationalType;
	}

	@Override
	public RationalType asRational() {
		Preconditions.checkState(isRational());
		return (RationalType) this;
	}

	@Override
	public boolean isTuple() {
		return this instanceof TupleType;
	}

	@Override
	public TupleType asTuple() {
		Preconditions.checkState(isTuple());
		return (TupleType) this;
	}

	@Override
	public boolean isRecord() {
		return this instanceof RecordType;
	}

	@Override
	public RecordType asRecord() {
		Preconditions.checkState(isRecord());
		return (RecordType) this;
	}

	@Override
	public boolean isUninterpreted() {
		return this instanceof UninterpretedType;
	}

	@Override
	public UninterpretedType asUninterpreted() {
		Preconditions.checkState(isUninterpreted());
		return (UninterpretedType) this;
	}
}
