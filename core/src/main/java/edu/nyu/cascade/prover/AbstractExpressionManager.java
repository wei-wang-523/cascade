package edu.nyu.cascade.prover;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractExpressionManager implements ExpressionManager {

	@Override
	public void addTrigger(Expression e, Expression p) {
		Preconditions.checkArgument(e.isBoolean());
		e.asBooleanExpression().addTrigger(p);
	}

	@Override
	public BooleanExpression and(Expression first, Expression rest) {
		Preconditions.checkArgument(first.isBoolean());
		Preconditions.checkArgument(rest.isBoolean());
		return booleanType().and(first, rest);
	}

	@Override
	public BooleanExpression and(Iterable<? extends Expression> subExpressions) {
		return booleanType().and(subExpressions);
	}

	@Override
	public BooleanExpression and(Expression first, Expression... rest) {
		return and(Lists.asList(first, rest));
	}

	@Override
	public BitVectorExpression bitVectorOne(int size) {
		Preconditions.checkArgument(size > 0);
		return bitVectorConstant(1, size);
	}

	@Override
	public BitVectorExpression bitVectorZero(int size) {
		Preconditions.checkArgument(size > 0);
		return bitVectorConstant(0, size);
	}

	@Override
	public BitVectorExpression bitVectorMinus(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().subtract(a, b);
	}

	@Override
	public BitVectorExpression bitVectorMult(int size, Expression a,
	    Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().mult(size, a, b);
	}

	@Override
	public BitVectorExpression bitVectorPlus(int size, Expression a,
	    Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().add(size, a, b);
	}

	@Override
	public BitVectorExpression bitwiseAnd(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseAnd(a, b);
	}

	@Override
	public BitVectorExpression bitwiseNand(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseNand(a, b);
	}

	@Override
	public BitVectorExpression bitwiseNor(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseNor(a, b);
	}

	@Override
	public BitVectorExpression bitwiseNot(Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseNot(a);
	}

	@Override
	public BitVectorExpression bitwiseOr(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseOr(a, b);
	}

	@Override
	public BitVectorExpression bitwiseXnor(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseXnor(a, b);
	}

	@Override
	public BitVectorExpression bitwiseXor(Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Type type = a.getType();
		return type.asBitVectorType().bitwiseXor(a, b);
	}

	@Override
	public BitVectorExpression concat(Expression left, Expression right) {
		Preconditions.checkArgument(left.isBitVector());
		Type type = left.getType();
		return type.asBitVectorType().concat(left, right);
	}

	@Override
	public InductiveExpression construct(Constructor constructor,
	    Expression... args) {
		return constructor.apply(args);
	}

	@Override
	public InductiveExpression construct(Constructor constructor,
	    Iterable<? extends Expression> args) {
		return constructor.apply(args);
	}

	@Override
	public Expression divide(Expression numerator, Expression denominator) {
		Type type = numerator.getType();
		Preconditions.checkArgument(type.isMultiplicativeType());
		return type.asMultiplicativeType().divide(numerator, denominator);
	}

	@Override
	public BitVectorExpression signedDivide(Expression numerator,
	    Expression denominator) {
		Preconditions.checkArgument(numerator.isBitVector());
		Type type = numerator.getType();
		return type.asBitVectorType().signedDivide(numerator, denominator);
	}

	@Override
	public BitVectorExpression rem(Expression numerator, Expression denominator) {
		Preconditions.checkArgument(numerator.isBitVector());
		Type type = numerator.getType();
		return type.asBitVectorType().rem(numerator, denominator);
	}

	@Override
	public BitVectorExpression signedRem(Expression numerator,
	    Expression denominator) {
		Preconditions.checkArgument(numerator.isBitVector());
		Type type = numerator.getType();
		return type.asBitVectorType().signedRem(numerator, denominator);
	}

	@Override
	public BooleanExpression exists(Expression var, Expression body) {
		return exists(ImmutableList.of(var), body);
	}

	@Override
	public BooleanExpression exists(Expression var, Expression body,
	    Iterable<? extends Expression> patterns) {
		return exists(ImmutableList.of(var), body, patterns);
	}

	@Override
	public BooleanExpression exists(Expression var, Expression body,
	    Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return exists(ImmutableList.of(var), body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression body) {
		return exists(ImmutableList.of(var1, var2), body);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression body, Iterable<? extends Expression> patterns) {
		return exists(ImmutableList.of(var1, var2), body, patterns);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return exists(ImmutableList.of(var1, var2), body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression var3, Expression body) {
		return exists(ImmutableList.of(var1, var2, var3), body);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression var3, Expression body,
	    Iterable<? extends Expression> patterns) {
		return exists(ImmutableList.of(var1, var2, var3), body, patterns);
	}

	@Override
	public BooleanExpression exists(Expression var1, Expression var2,
	    Expression var3, Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return exists(ImmutableList.of(var1, var2, var3), body, patterns,
		    noPatterns);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
	    Expression body) {
		return exists(vars, body);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
	    Expression body, Iterable<? extends Expression> patterns) {
		return exists(vars, body, patterns);
	}

	@Override
	public BooleanExpression exists(Iterable<? extends Expression> vars,
	    Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return exists(vars, body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression forall(Expression var, Expression body,
	    Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return forall(ImmutableList.of(var), body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression forall(Expression var, Expression body) {
		return forall(ImmutableList.of(var), body);
	}

	@Override
	public BooleanExpression forall(Expression var, Expression body,
	    Iterable<? extends Expression> patterns) {
		return forall(ImmutableList.of(var), body, patterns);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression body) {
		return forall(ImmutableList.of(var1, var2), body);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression body, Iterable<? extends Expression> patterns) {
		return forall(ImmutableList.of(var1, var2), body, patterns);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return forall(ImmutableList.of(var1, var2), body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression var3, Expression body) {
		return forall(ImmutableList.of(var1, var2, var3), body);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression var3, Expression body,
	    Iterable<? extends Expression> patterns) {
		return forall(ImmutableList.of(var1, var2, var3), body, patterns);
	}

	@Override
	public BooleanExpression forall(Expression var1, Expression var2,
	    Expression var3, Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return forall(ImmutableList.of(var1, var2, var3), body, patterns,
		    noPatterns);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
	    Expression body, Iterable<? extends Expression> patterns,
	    Iterable<? extends Expression> noPatterns) {
		return booleanType().forall(vars, body, patterns, noPatterns);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
	    Expression body) {
		return booleanType().forall(vars, body);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars,
	    Expression body, Iterable<? extends Expression> patterns) {
		return booleanType().forall(vars, body, patterns);
	}

	@Override
	public FunctionType functionType(Type argType1, Type argType2, Type... rest) {
		List<Type> argTypes = Lists.newArrayList(argType1);
		Type range = argType2;

		if (rest.length > 0) {
			argTypes.add(argType2);
			for (int i = 0; i < rest.length - 1; i++) {
				argTypes.add(rest[i]);
			}
			range = rest[rest.length - 1];
		}
		return functionType(argTypes, range);
	}

	@Override
	public FunctionType functionType(Type argType, Type range) {
		List<Type> argTypes = Lists.newArrayList(argType);
		return functionType(argTypes, range);
	}

	@Override
	public BooleanExpression iff(Expression left, Expression right) {
		return booleanType().iff(left, right);
	}

	@Override
	public Expression ifThenElse(Expression cond, Expression tt, Expression ff) {
		return booleanType().ifThenElse(cond, tt, ff);
	}

	@Override
	public BooleanExpression implies(Expression left, Expression right) {
		return booleanType().implies(left, right);
	}

	@Override
	public Expression index(Expression array, Expression index) {
		Preconditions.checkArgument(array.isArray());
		return array.getType().asArrayType().index(array, index);
	}

	@Override
	public Expression index(Expression tuple, int index) {
		Preconditions.checkArgument(tuple.isTuple());
		return tuple.getType().asTuple().index(tuple, index);
	}

	@Override
	public BooleanExpression greaterThanOrEqual(Expression left,
	    Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().geq(left, right);
	}

	@Override
	public BooleanExpression signedGreaterThanOrEqual(Expression left,
	    Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().sgeq(left, right);
	}

	@Override
	public BooleanExpression greaterThan(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().gt(left, right);
	}

	@Override
	public BooleanExpression signedGreaterThan(Expression left,
	    Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().sgt(left, right);
	}

	@Override
	public BooleanExpression lessThanOrEqual(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().leq(left, right);
	}

	@Override
	public BooleanExpression signedLessThanOrEqual(Expression left,
	    Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().sleq(left, right);
	}

	@Override
	public BooleanExpression lessThan(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().lt(left, right);
	}

	@Override
	public BooleanExpression signedLessThan(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isComparableType());
		return type.asComparableType().slt(left, right);
	}

	@Override
	public Expression minus(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isAddableType());
		return type.asAddableType().subtract(left, right);
	}

	@Override
	public Expression mult(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isMultiplicativeType());
		return type.asMultiplicativeType().mult(left, right);
	}

	@Override
	public Expression mult(List<? extends Expression> children) {
		if (children.isEmpty()) {
			throw new IllegalArgumentException("No operands in mult");
		} else {
			Expression child = children.get(0);
			Type type = child.getType();
			Preconditions.checkArgument(type.isMultiplicativeType());
			return type.asMultiplicativeType().mult(children);
		}
	}

	@Override
	public Expression negate(Expression a) {
		Type type = a.getType();
		Preconditions.checkArgument(type.isAddableType());
		return type.asAddableType().negate(a);
	}

	@Override
	public IntegerExpression negativeOne() {
		return constant(-1);
	}

	@Override
	public BooleanExpression neq(Expression arg0, Expression arg1) {
		return not(eq(arg0, arg1));
	}

	@Override
	public IntegerExpression one() {
		return constant(1);
	}

	@Override
	public Expression plus(Expression left, Expression right) {
		Type type = left.getType();
		Preconditions.checkArgument(type.isAddableType());
		return type.asAddableType().add(left, right);
	}

	@Override
	public Expression plus(Expression first, Expression... rest) {
		return plus(Lists.asList(first, rest));
	}

	@Override
	public Expression plus(Iterable<? extends Expression> children) {
		if (Iterables.isEmpty(children)) {
			throw new IllegalArgumentException("No addends in plus");
		} else {
			Expression child = Iterables.get(children, 0);
			Type type = child.getType();
			Preconditions.checkArgument(type.isAddableType());
			return type.asAddableType().add(children);
		}
	}

	@Override
	public BitVectorExpression bitVectorPlus(int size, Expression first,
	    Expression... rest) {
		return bitVectorPlus(size, Lists.asList(first, rest));
	}

	@Override
	public BitVectorExpression bitVectorPlus(int size,
	    Iterable<? extends Expression> args) {
		Preconditions.checkArgument(Iterables.size(args) >= 1);
		Expression first = Iterables.get(args, 0);
		Preconditions.checkArgument(first.isBitVector());
		return first.getType().asBitVectorType().add(size, args);
	}

	@Override
	public VariableExpression variable(String name, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isScalarType());
		return type.asScalarType().variable(name, fresh).asVariable();
	}

	@Override
	public Expression boundVar(String name, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isScalarType());
		return type.asScalarType().boundVar(name, fresh);
	}

	@Override
	public Expression boundExpression(String name, int index, Type type,
	    boolean fresh) {
		Preconditions.checkArgument(type.isScalarType());
		return type.asScalarType().boundExpression(name, index, fresh);
	}

	@Override
	public IntegerExpression zero() {
		return constant(0);
	}

	@Override
	public BooleanExpression ff() {
		return booleanType().ff();
	}

	@Override
	public BooleanExpression rewriteRule(Iterable<? extends Expression> vars,
	    Expression guard, Expression rule) {
		return booleanType().rewriteRule(vars, guard, rule);
	}

	@Override
	public BooleanExpression rrRewrite(Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return booleanType().rrRewrite(head, body, triggers);
	}

	@Override
	public BooleanExpression rrRewrite(Expression head, Expression body) {
		return booleanType().rrRewrite(head, body);
	}

	@Override
	public BooleanExpression rrReduction(Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return booleanType().rrReduction(head, body, triggers);
	}

	@Override
	public BooleanExpression rrReduction(Expression head, Expression body) {
		return booleanType().rrReduction(head, body);
	}

	@Override
	public BooleanExpression rrDeduction(Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return booleanType().rrDeduction(head, body, triggers);
	}

	@Override
	public BooleanExpression rrDeduction(Expression head, Expression body) {
		return booleanType().rrDeduction(head, body);
	}

	@Override
	public Expression pow(Expression x, Expression n) {
		Type type = x.getType();
		Preconditions.checkArgument(type.isMultiplicativeType());
		return type.asMultiplicativeType().pow(x, n);
	}

	@Override
	public RationalExpression rationalConstant(int numerator, int denominator) {
		return rationalType().constant(numerator, denominator);
	}

	@Override
	public BooleanExpression not(Expression expr) {
		return booleanType().not(expr);
	}

	@Override
	public BooleanExpression or(Expression... subExpressions) {
		return booleanType().or(subExpressions);
	}

	@Override
	public BooleanExpression or(Expression left, Expression right) {
		return booleanType().or(left, right);
	}

	@Override
	public BooleanExpression or(Iterable<? extends Expression> subExpressions) {
		return booleanType().or(subExpressions);
	}

	@Override
	public RationalExpression ratOne() {
		return rationalType().one().asRationalExpression();
	}

	@Override
	public RationalExpression ratZero() {
		return rationalType().zero().asRationalExpression();
	}

	@Override
	public Expression select(Selector selector, Expression val) {
		return selector.apply(val);
	}

	@Override
	public BitVectorExpression signedExtend(int size, Expression bv) {
		Preconditions.checkArgument(bv.isBitVector());
		Type type = bv.getType();
		return type.asBitVectorType().signedExtend(size, bv);
	}

	@Override
	public BitVectorExpression zeroExtend(int size, Expression bv) {
		Preconditions.checkArgument(bv.isBitVector());
		Type type = bv.getType();
		return type.asBitVectorType().zeroExtend(size, bv);
	}

	@Override
	public Expression subst(Expression e, Iterable<? extends Expression> oldExprs,
	    Iterable<? extends Expression> newExprs) {
		return e.subst(oldExprs, newExprs);
	}

	@Override
	public BooleanExpression testConstructor(Constructor constructor,
	    Expression val) {
		Preconditions.checkArgument(val.isInductive());
		Type type = val.getType();
		return type.asInductive().test(constructor, val);
	}

	@Override
	public BooleanExpression tt() {
		return booleanType().tt();
	}

	@Override
	public ArrayExpression update(Expression array, Expression index,
	    Expression value) {
		Preconditions.checkArgument(array.isArray());
		Type type = array.getType();
		return type.asArrayType().update(array, index, value);
	}

	@Override
	public TupleExpression update(Expression tuple, int i, Expression value) {
		Preconditions.checkArgument(tuple.isTuple());
		Type type = tuple.getType();
		return type.asTuple().update(tuple, i, value);
	}

	@Override
	public BooleanExpression xor(Expression left, Expression right) {
		return booleanType().xor(left, right);
	}

	@Override
	public RecordExpression update(Expression record, String fieldName,
	    Expression value) {
		Preconditions.checkArgument(record.isRecord());
		Type type = record.getType();
		return type.asRecord().update(record, fieldName, value);
	}

	@Override
	public ArrayExpression storeAll(Expression expr, Type type) {
		Preconditions.checkArgument(type.isArrayType());
		return type.asArrayType().storeAll(expr, type.asArrayType());
	}

	@Override
	public Expression applyExpr(Expression fun,
	    Iterable<? extends Expression> args) {
		return fun.asFunctionExpression().apply(args);
	}

	@Override
	public Expression applyExpr(Expression fun, Expression first,
	    Expression... rest) {
		return fun.asFunctionExpression().apply(first, rest);
	}

	@Override
	public BitVectorExpression extract(Expression bv, int low, int high) {
		Preconditions.checkArgument(bv.isBitVector());
		Type type = bv.getType();
		return type.asBitVectorType().extract(bv, high, low);
	}

	@Override
	public BooleanExpression distinct(Expression first, Expression second,
	    Expression... rest) {
		return booleanType().distinct(first, second, rest);
	}

	@Override
	public BooleanExpression distinct(Iterable<? extends Expression> args) {
		return booleanType().distinct(args);
	}

	@Override
	public BooleanExpression eq(Expression lhs, Expression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(rhs.getType()));
		return booleanType().eq(lhs, rhs);
	}
}
