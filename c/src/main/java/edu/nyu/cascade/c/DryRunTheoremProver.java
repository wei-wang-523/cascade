package edu.nyu.cascade.c;

import java.util.LinkedHashSet;
import java.util.List;

import org.apache.commons.cli.Option;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.RationalVariableExpression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverFactory.Capability;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.UninterpretedExpression;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;

/**
 * An <code>ITheoremProver</code> implementation that delegates to an underlying
 * theorem prover for everything except satisfiability/validity queries. Useful
 * for testing.
 */
final class DryRunTheoremProver implements TheoremProver {
  private static class DryRunExpressionManager implements ExpressionManager {
    private final DryRunTheoremProver theoremProver;;
    private final ExpressionManager exprManager;
    private final LinkedHashSet<VariableExpression> variableSet;

    DryRunExpressionManager(DryRunTheoremProver theoremProver,
        ExpressionManager exprManager) {
      this.theoremProver = theoremProver;
      this.exprManager = exprManager;
      variableSet = Sets.newLinkedHashSet();
    }

    @Override
    public void addTrigger(Expression e, Expression p) {
      exprManager.addTrigger(e, p);
    }

    @Override
    public BooleanExpression and(Expression first, Expression... rest) {
      return exprManager.and(first, rest);
    }

    public BooleanExpression and(Expression left, Expression right) {
      return exprManager.and(left, right);
    }

    @Override
    public BooleanExpression and(Iterable<? extends Expression> subExpressions) {
      return exprManager.and(subExpressions);
    }

    @Override
    public Expression applyExpr(FunctionType fun, Expression arg,
        Expression... rest) {
      return exprManager.applyExpr(fun, arg, rest);
    }

    @Override
    public Expression applyExpr(FunctionType fun, Iterable<? extends Expression> args) {
      return exprManager.applyExpr(fun, args);
    }
    
    @Override
    public Expression applyExpr(Expression fun, Expression arg,
        Expression... rest) {
      return exprManager.applyExpr(fun, arg, rest);
    }

    @Override
    public Expression applyExpr(Expression fun, Iterable<? extends Expression> args) {
      return exprManager.applyExpr(fun, args);
    }

    @Override
    public ArrayType arrayType(Type index, Type elem) {
      return exprManager.arrayType(index, elem);
    }

    @Override
    public ArrayVariableExpression arrayVar(String name, Type index, Type elem,
        boolean fresh) {
      return exprManager.arrayVar(name, index, elem, fresh);
    }

    @Override
    public VariableExpression arrayBoundVar(String name, Type index, Type elem,
        boolean fresh) {
      return exprManager.arrayBoundVar(name, index, elem, fresh);
    }
    
    @Override
    public ArrayType asArrayType(Type type) {
      return exprManager.asArrayType(type);
    }

    @Override
    public BitVectorExpression asBitVector(Expression expression) {
      return exprManager.asBitVector(expression);
    }

    @Override
    public BitVectorType asBitVectorType(Type t) {
      return exprManager.asBitVectorType(t);
    }

    @Override
    public BooleanExpression asBooleanExpression(Expression expression) {
      return exprManager.asBooleanExpression(expression);
    }

    @Override
    public FunctionExpression asFunctionExpression(Expression expression) {
      return exprManager.asFunctionExpression(expression);
    }

    @Override
    public FunctionType asFunctionType(Type t) {
      return exprManager.asFunctionType(t);
    }

    @Override
    public IntegerExpression asIntegerExpression(Expression expression) {
      return exprManager.asIntegerExpression(expression);
    }

    @Override
    public IntegerVariableExpression asIntegerVariable(Expression expression) {
      return exprManager.asIntegerVariable(expression);
    }

    @Override
    public RationalExpression asRationalExpression(Expression expression) {
      return exprManager.asRationalExpression(expression);
    }

    @Override
    public RationalVariableExpression asRationalVariable(Expression expression) {
      return exprManager.asRationalVariable(expression);
    }

    public TupleExpression asTuple(Expression e) {
      return exprManager.asTuple(e);
    }

    @Override
    public TupleType asTupleType(Type t) {
      return exprManager.asTupleType(t);
    }

    @Override
    public VariableExpression asVariable(Expression var) {
      return exprManager.asVariable(var);
    }

    @Override
    public BitVectorExpression bitVectorConstant(int n, int size) {
      return exprManager.bitVectorConstant(n, size);
    }

    @Override
    public BitVectorExpression bitVectorConstant(String rep) {
      return exprManager.bitVectorConstant(rep);
    }

    public BitVectorExpression bitVectorMinus(Expression a, Expression b) {
      return exprManager.bitVectorMinus(a, b);
    }

    @Override
    public BitVectorExpression bitVectorOne(int size) {
      return exprManager.bitVectorOne(size);
    }

    @Override
    public BitVectorExpression bitVectorPlus(int size,
        Iterable<? extends Expression> args) {
      return exprManager.bitVectorPlus(size, args);
    }
    
    @Override
    public BitVectorExpression bitVectorMult(int size,
        Iterable<? extends Expression> args) {
      return exprManager.bitVectorMult(size, args);
    }

    @Override
    public BitVectorType bitVectorType(int size) {
      return exprManager.bitVectorType(size);
    }

    @Override
    public BitVectorExpression bitVectorZero(int size) {
      return exprManager.bitVectorZero(size);
    }

    @Override
    public BitVectorExpression bitwiseAnd(Expression a, Expression b) {
      return exprManager.bitwiseAnd(a, b);
    }

    @Override
    public BitVectorExpression bitwiseNand(Expression a, Expression b) {
      return exprManager.bitwiseNand(a, b);
    }

    @Override
    public BitVectorExpression bitwiseNor(Expression a, Expression b) {
      return exprManager.bitwiseNor(a, b);
    }

    @Override
    public BitVectorExpression bitwiseNot(Expression a) {
      return exprManager.bitwiseNot(a);
    }

    @Override
    public BitVectorExpression bitwiseOr(Expression a, Expression b) {
      return exprManager.bitwiseOr(a, b);
    }

    @Override
    public BitVectorExpression bitwiseXnor(Expression a, Expression b) {
      return exprManager.bitwiseXnor(a, b);
    }

    @Override
    public BitVectorExpression bitwiseXor(Expression a, Expression b) {
      return exprManager.bitwiseXor(a, b);
    }

    @Override
    public BooleanType booleanType() {
      return exprManager.booleanType();
    }

    @Override
    public VariableExpression booleanVar(String name, boolean fresh) {
      return exprManager.booleanVar(name, fresh);
    }
    
    @Override
    public VariableExpression booleanBoundVar(String name, boolean fresh) {
      return exprManager.booleanBoundVar(name, fresh);
    }

    @Override
    public BitVectorExpression concat(Expression left, Expression right) {
      return exprManager.concat(left, right);
    }

    @Override
    public IntegerExpression constant(int c) {
      return exprManager.constant(c);
    }

    @Override
    public InductiveExpression construct(Constructor constructor,
        Expression... args) {
      return exprManager.construct(constructor, args);
    }

    @Override
    public InductiveExpression construct(Constructor constructor,
        Iterable<? extends Expression> args) {
      return exprManager.construct(constructor, args);
    }

    @Override
    public Constructor constructor(String name, Selector... selectors) {
      return exprManager.constructor(name, selectors);
    }

    @Override
    public InductiveType dataType(String name, Constructor... constructors) {
      return exprManager.dataType(name, constructors);
    }

    @Override
    public ImmutableList<? extends InductiveType> dataTypes(List<String> names,
        List<? extends Constructor>... constructorLists) {
      return exprManager.dataTypes(names, constructorLists);
    }

    @Override
    public BooleanExpression distinct(Expression first, Expression second,
        Expression... rest) {
      return exprManager.distinct(first, second, rest);
    }

    @Override
    public BooleanExpression distinct(Iterable<? extends Expression> args) {
      return exprManager.distinct(args);
    }

    @Override
    public BitVectorExpression divide(Expression numerator,
        Expression denominator) {
      return exprManager.divide(numerator, denominator);
    }
    
    @Override
    public BitVectorExpression signedDivide(Expression numerator,
        Expression denominator) {
      return exprManager.signedDivide(numerator, denominator);
    }
    
    @Override
    public BitVectorExpression rem(Expression numerator,
        Expression denominator) {
      return exprManager.rem(numerator, denominator);
    }
    
    @Override
    public BitVectorExpression signedRem(Expression numerator,
        Expression denominator) {
      return exprManager.signedRem(numerator, denominator);
    }

    @Override
    public BooleanExpression eq(Expression left, Expression right) {
      return exprManager.eq(left, right);
    }

    @Override
    public BooleanExpression exists(
        Iterable<? extends Expression> vars, Expression body) {
      return exprManager.exists(vars, body);
    }

    @Override
    public BooleanExpression exists(Expression var, Expression body) {
      return exprManager.exists(var, body);
    }

    @Override
    public BooleanExpression exists(Expression var1,
        Expression var2, Expression body) {
      return exprManager.exists(var1, var2, body);
    }

    @Override
    public BooleanExpression exists(Expression var,
        Expression var2, Expression var3, Expression body) {
      return exprManager.exists(var, var2, var3, body);
    }

    @Override
    public BooleanExpression exists(Expression var, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.exists(var, body, patterns);
    }

    @Override
    public BooleanExpression exists(Expression var, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.exists(var, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression exists(Expression var1,
        Expression var2, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.exists(var1, var2, body, patterns);
    }

    @Override
    public BooleanExpression exists(Expression var1,
        Expression var2, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.exists(var1, var2, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression exists(Expression var1,
        Expression var2, Expression var3, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.exists(var1, var2, var3, body, patterns);
    }

    @Override
    public BooleanExpression exists(Expression var1,
        Expression var2, Expression var3, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.exists(var1, var2, var3, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression exists(
        Iterable<? extends Expression> vars, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.exists(vars, body, patterns);
    }

    @Override
    public BooleanExpression exists(
        Iterable<? extends Expression> vars, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.exists(vars, body, patterns, noPatterns);
    }

    @Override
    public BitVectorExpression extract(Expression bv, int i, int j) {
      return exprManager.extract(bv, i, j);
    }

    @Override
    public BooleanExpression ff() {
      return exprManager.ff();
    }

    @Override
    public BooleanExpression forall(
        Iterable<? extends Expression> vars, Expression body) {
      return exprManager.forall(vars, body);
    }

    @Override
    public BooleanExpression forall(
        Iterable<? extends Expression> vars, Expression body,
        Iterable<? extends Expression> triggers) {
      return exprManager.forall(vars, body, triggers);
    }

    @Override
    public BooleanExpression forall(Expression var, Expression body) {
      return exprManager.forall(var, body);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression body) {
      return exprManager.forall(var1, var2, body);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression var3, Expression body) {
      return exprManager.forall(var1, var2, var3, body);
    }
    
    @Override
    public BooleanExpression forall(Expression var, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.forall(var, body, patterns);
    }

    @Override
    public BooleanExpression forall(Expression var, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.forall(var, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.forall(var1, var2, body, patterns);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.forall(var1, var2, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression var3, Expression body,
        Iterable<? extends Expression> patterns) {
      return exprManager.forall(var1, var2, var3, body, patterns);
    }

    @Override
    public BooleanExpression forall(Expression var1,
        Expression var2, Expression var3, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.forall(var1, var2, var3, body, patterns, noPatterns);
    }

    @Override
    public BooleanExpression forall(
        Iterable<? extends Expression> vars, Expression body,
        Iterable<? extends Expression> patterns,
        Iterable<? extends Expression> noPatterns) {
      return exprManager.forall(vars, body, patterns, noPatterns);
    }
    
    @Override
    public BooleanExpression rewriteRule(Iterable<? extends VariableExpression> vars, 
        Expression guard, Expression rule) {
      return exprManager.rewriteRule(vars, guard, rule);
    }
    
    @Override
    public BooleanExpression rrRewrite(Expression head, Expression body, Iterable<? extends Expression> triggers) {
      return exprManager.rrRewrite(head, body, triggers);
    }
    
    @Override
    public BooleanExpression rrRewrite(Expression head, Expression body) {
      return exprManager.rrRewrite(head, body);
    }
    
    @Override
    public BooleanExpression rrReduction(Expression head, Expression body, Iterable<? extends Expression> triggers) {
      return exprManager.rrReduction(head, body, triggers);
    }
    
    @Override
    public BooleanExpression rrReduction(Expression head, Expression body) {
      return exprManager.rrReduction(head, body);
    }
    
    @Override
    public BooleanExpression rrDeduction(Expression head, Expression body, Iterable<? extends Expression> triggers) {
      return exprManager.rrDeduction(head, body, triggers);
    }
    
    @Override
    public BooleanExpression rrDeduction(Expression head, Expression body) {
      return exprManager.rrDeduction(head, body);
    }

    @Override
    public FunctionType functionType(String fname, Iterable<? extends Type> domains,
        Type range) {
      return exprManager.functionType(fname, domains, range);
    }

    @Override
    public FunctionType functionType(String fname, Type argType1, Type argType2, Type... rest) {
      return exprManager.functionType(fname, argType1, argType2, rest);
    }

    @Override
    public ImmutableList<Option> getOptions() {
      return exprManager.getOptions();
    }

    @Override
    public DryRunTheoremProver getTheoremProver() {
      return theoremProver;
    }

    @Override
    public BooleanExpression greaterThan(Expression lhs, Expression rhs) {
      return exprManager.greaterThan(lhs, rhs);
    }
    
    @Override
    public BooleanExpression signedGreaterThan(Expression lhs, Expression rhs) {
      return exprManager.signedGreaterThan(lhs, rhs);
    }

    @Override
    public BooleanExpression greaterThanOrEqual(Expression left,
        Expression right) {
      return exprManager.greaterThanOrEqual(left, right);
    }
    
    @Override
    public BooleanExpression signedGreaterThanOrEqual(Expression left,
        Expression right) {
      return exprManager.signedGreaterThanOrEqual(left, right);
    }

    @Override
    public BooleanExpression hasType(Expression expr, Type type) {
      return exprManager.hasType(expr, type);
    }

    @Override
    public BooleanExpression iff(Expression left, Expression right) {
      return exprManager.iff(left, right);
    }

    @Override
    public Expression ifThenElse(Expression cond, Expression tt, Expression ff) {
      return exprManager.ifThenElse(cond, tt, ff);
    }

    @Override
    public BooleanExpression implies(Expression left, Expression right) {
      return exprManager.implies(left, right);
    }

    @Override
    public Expression importExpression(Expression expression) {
      return exprManager.importExpression(expression);
    }

    @Override
    public Type importType(Type type) {
      return exprManager.importType(type);
    }

    @Override
    public Expression index(Expression array, Expression index) {
      return exprManager.index(array, index);
    }

    @Override
    public Expression index(Expression tuple, int index) {
      return exprManager.index(tuple, index);
    }

    @Override
    public InductiveType inductiveType(String name) {
      return exprManager.inductiveType(name);
    }

    @Override
    public IntegerExpression integerPow(Expression x, Expression n) {
      return exprManager.integerPow(x, n);
    }

    @Override
    public IntegerType integerRangeType(Expression lBound, Expression uBound) {
      return exprManager.integerRangeType(lBound, uBound);
    }

    @Override
    public IntegerType integerType() {
      return exprManager.integerType();
    }

    @Override
    public IntegerVariableExpression integerVar(String name, boolean fresh) {
      return exprManager.integerVar(name, fresh);
    }

    @Override
    public VariableExpression integerBoundVar(String name, boolean fresh) {
      return exprManager.integerBoundVar(name, fresh);
    }

    @Override
    public FunctionExpression lambda(
        Iterable<? extends VariableExpression> vars, Expression expr) {
      return exprManager.lambda(vars, expr);
    }

    @Override
    public FunctionExpression lambda(VariableExpression var, Expression expr) {
      return exprManager.lambda(var, expr);
    }

    @Override
    public FunctionExpression lambda(VariableExpression var1,
        VariableExpression var2, Expression expr) {
      return exprManager.lambda(var1, var2, expr);
    }

    @Override
    public BooleanExpression lessThan(Expression left, Expression right) {
      return exprManager.lessThan(left, right);
    }
    
    @Override
    public BooleanExpression signedLessThan(Expression left, Expression right) {
      return exprManager.signedLessThan(left, right);
    }

    @Override
    public BooleanExpression lessThanOrEqual(Expression left, Expression right) {
      return exprManager.lessThanOrEqual(left, right);
    }
    
    @Override
    public BooleanExpression signedLessThanOrEqual(Expression left, Expression right) {
      return exprManager.signedLessThanOrEqual(left, right);
    }

    @Override
    public Expression minus(Expression a, Expression b) {
      return exprManager.minus(a, b);
    }

    @Override
    public Expression mult(Expression left, Expression right) {
      return exprManager.mult(left, right);
    }

    @Override
    public BitVectorExpression mult(int size, Expression a, Expression b) {
      return exprManager.mult(size, a, b);
    }

    @Override
    public Expression mult(List<? extends Expression> children) {
      return exprManager.mult(children);
    }

    @Override
    public Expression negate(Expression e) {
      return exprManager.negate(e);
    }

    @Override
    public IntegerExpression negativeOne() {
      return exprManager.negativeOne();
    }

    @Override
    public BooleanExpression neq(Expression arg0, Expression arg1) {
      return exprManager.neq(arg0, arg1);
    }

    @Override
    public BooleanExpression not(Expression expr) {
      return exprManager.not(expr);
    }
    
    @Override
    public Expression nullExpression() {
      return exprManager.nullExpression();
    }

    @Override
    public IntegerExpression one() {
      return exprManager.one();
    }

    @Override
    public BooleanExpression or(Expression... subExpressions) {
      return exprManager.or(subExpressions);
    }

    @Override
    public BooleanExpression or(Expression left, Expression right) {
      return exprManager.or(left, right);
    }

    @Override
    public BooleanExpression or(Iterable<? extends Expression> subExpressions) {
      return exprManager.or(subExpressions);
    }

    @Override
    public Expression plus(Expression first, Expression... rest) {
      return exprManager.plus(first, rest);
    }

    @Override
    public Expression plus(Expression left, Expression right) {
      return exprManager.plus(left, right);
    }

    @Override
    public BitVectorExpression plus(int size, Expression first,
        Expression... rest) {
      return exprManager.plus(size, first, rest);
    }

    @Override
    public BitVectorExpression plus(int size, Expression a, Expression b) {
      return exprManager.plus(size, a, b);
    }

    @Override
    public BitVectorExpression plus(int size,
        Iterable<? extends Expression> args) {
      return exprManager.plus(size, args);
    }

    @Override
    public Expression plus(Iterable<? extends Expression> children) {
      return exprManager.plus(children);
    }

    @Override
    public RationalExpression rationalConstant(int numerator, int denominator) {
      return exprManager.rationalConstant(numerator, denominator);
    }

    @Override
    public RationalExpression rationalPow(Expression x, Expression n) {
      return exprManager.rationalPow(x, n);
    }

    @Override
    public RationalType rationalRangeType(Expression lBound, Expression uBound) {
      return exprManager.rationalRangeType(lBound, uBound);
    }

    @Override
    public RationalType rationalType() {
      return exprManager.rationalType();
    }

    @Override
    public RationalVariableExpression rationalVar(String name, boolean fresh) {
      return exprManager.rationalVar(name, fresh);
    }
    
    @Override
    public VariableExpression rationalBoundVar(String name, boolean fresh) {
      return exprManager.rationalBoundVar(name, fresh);
    }

    @Override
    public RationalExpression ratOne() {
      return exprManager.ratOne();
    }

    @Override
    public RationalExpression ratZero() {
      return exprManager.ratZero();
    }

    @Override
    public Expression select(Selector selector, Expression val) {
      return exprManager.select(selector, val);
    }

    @Override
    public Selector selector(String name, Type type, int ref) {
      return exprManager.selector(name, type, ref);
    }
    
    @Override
    public Selector selector(String name, Type type) {
      return exprManager.selector(name, type);
    }

    @Override
    public void setPreferences() {
      exprManager.setPreferences();
    }

    @Override
    public void setTriggers(Expression e,
        Iterable<? extends Expression> triggers) {
      exprManager.setTriggers(e, triggers);
    }

    @Override
    public BitVectorExpression signExtend(Expression bv, int size) {
      return exprManager.signExtend(bv, size);
    }

    @Override
    public Expression subst(Expression e,
        Iterable<? extends Expression> oldExprs,
        Iterable<? extends Expression> newExprs) {
      return exprManager.subst(e, oldExprs, newExprs);
    }

    @Override
    public Expression succ(Expression op) {
      return exprManager.succ(op);
    }

    @Override
    public BooleanExpression testConstructor(Constructor constructor,
        Expression val) {
      return exprManager.testConstructor(constructor, val);
    }

    @Override
    public BooleanExpression tt() {
      return exprManager.tt();
    }

    @Override
    public TupleExpression tuple(Type tupleType, Expression first, Expression... rest) {
      return exprManager.tuple(tupleType, first, rest);
    }

    @Override
    public TupleExpression tuple(Type tupleType, Iterable<? extends Expression> elements) {
      return exprManager.tuple(tupleType, elements);
    }

    @Override
    public TupleType tupleType(String tupleName, Iterable<? extends Type> elementTypes) {
      return exprManager.tupleType(tupleName, elementTypes);
    }

    @Override
    public TupleType tupleType(String tupleName, Type firstType, Type... elementTypes) {
      return exprManager.tupleType(tupleName, firstType, elementTypes);
    }

    @Override
    public Type universalType() {
      return exprManager.universalType();
    }

    @Override
    public ArrayExpression update(Expression array, Expression index,
        Expression value) {
      return exprManager.update(array, index, value);
    }

    @Override
    public TupleExpression update(Expression tuple, int i, Expression val) {
      return exprManager.update(tuple, i, val);
    }

    @Override
    public VariableExpression variable(String name, Type type, boolean fresh) {
      return exprManager.variable(name, type, fresh);
    }

    @Override
    public BooleanExpression xor(Expression left, Expression right) {
      return exprManager.xor(left, right);
    }

    @Override
    public IntegerExpression zero() {
      return exprManager.zero();
    }

    @Override
    public BitVectorExpression zeroExtend(Expression bv, int size) {
      return exprManager.zeroExtend(bv, size);
    }

    @Override
    public ArrayExpression asArray(Expression e) {
      return exprManager.asArray(e);
    }

    @Override
    public ArrayExpression storeAll(Expression expr, Type type) {
      return exprManager.storeAll(expr, type);
    }

    @Override
    public int valueOfIntegerConstant(Expression expr) {
      return exprManager.valueOfIntegerConstant(expr);
    }

    @Override
    public boolean valueOfBooleanConstant(Expression expr) {
      return exprManager.valueOfBooleanConstant(expr);
    }

    @Override
    public LinkedHashSet<VariableExpression> getVariables() {
      return variableSet;
    }

    @Override
    public Expression applyExpr(FunctionType func, Expression arg) {
      return exprManager.applyExpr(func, arg);
    }

    @Override
    public FunctionType functionType(String fname, Type argType, Type range) {
      return exprManager.functionType(fname, argType, range);
    }

    @Override
    public VariableExpression functionVar(String fname, FunctionType func,
        boolean fresh) {
      return exprManager.functionVar(fname, func, fresh);
    }

    @Override
    public VariableExpression functionBoundVar(String fname, FunctionType func,
        boolean fresh) {
      return exprManager.functionBoundVar(fname, func, fresh);
    }

    @Override
    public Expression boundExpression(int index, Type type) {
      return exprManager.boundExpression(index, type);
    }

    @Override
    public UninterpretedType uninterpretedType(String name) {
      return exprManager.uninterpretedType(name);
    }

    @Override
    public RecordExpression record(Type type, Iterable<? extends Expression> args) {
      return exprManager.record(type, args);
    }

    @Override
    public RecordExpression record(Type type, Expression arg) {
      return exprManager.record(type, arg);
    }

    @Override
    public RecordType recordType(String tname, Iterable<String> names,
        Iterable<? extends Type> elementTypes) {
      return exprManager.recordType(tname, names, elementTypes);
    }

    @Override
    public RecordType recordType(String tname, String name, Type elementType) {
      return exprManager.recordType(tname, name, elementType);
    }

    @Override
    public RecordExpression update(Expression record, String fieldName,
        Expression val) {
      return exprManager.update(record, fieldName, val);
    }

    @Override
    public RecordType asRecordType(Type t) {
      return exprManager.asRecordType(t);
    }

    @Override
    public RecordExpression asRecord(Expression e) {
      return exprManager.asRecord(e);
    }

    @Override
    public InductiveExpression asInductive(Expression e) {
      return exprManager.asInductive(e);
    }

    @Override
    public UninterpretedExpression asUninterpreted(Expression e) {
      return exprManager.asUninterpreted(e);
    }

    @Override
    public RecordExpression record(Type type, Expression first,
        Expression... rest) {
      return exprManager.record(type, first, rest);
    }
  }

  public class Provider implements TheoremProver.Provider {
    private final TheoremProver.Provider baseProvider;
    
    public Provider(TheoremProver.Provider baseProvider) {
      this.baseProvider = baseProvider;
    }
    
    @Override
    public Iterable<Capability> getCapabilities() {
      return baseProvider.getCapabilities();
    }
    
    @Override
    public String getName() {
      return "dry-run:" + baseProvider.getName();
    }

    @Override
    public Iterable<Option> getOptions() {
      return baseProvider.getOptions();
    }

    @Override
    public DryRunTheoremProver create() {
      return new DryRunTheoremProver(baseProvider.create());
    }
  }
  
  private final TheoremProver theoremProver;
  private final DryRunExpressionManager exprManager;

  DryRunTheoremProver(TheoremProver theoremProver) {
    this.theoremProver = theoremProver;
    this.exprManager = new DryRunExpressionManager(this,
        theoremProver.getExpressionManager());
  }

  @Override
  public void assume(Expression first, Expression... rest) {
    theoremProver.assume(first, rest);
  }

  @Override
  public void assume(Iterable<? extends Expression> propositions) {
    theoremProver.assume(propositions);
  }

  /** Always returns UNSATISFIABLE. */
  @Override
  public SatResult<?> checkSat(Expression expr) {
    return SatResult.unsat(expr);
  }

  /** Always returns VALID. */
  @Override
  public ValidityResult<?> checkValidity(Expression bool) {
    return ValidityResult.valid(bool);
  }

  @Override
  public void clearAssumptions() {
    theoremProver.clearAssumptions();
  }
  
  @Override
  public ExpressionManager getExpressionManager() {
    return exprManager;
  }

  @Override
  public void setEffortLevel(int level) {
    theoremProver.setEffortLevel(level);
  }
  
  @Override
  public void setTimeLimit(int second) {
    theoremProver.setTimeLimit(second);
  }
  
  @Override
  public void setPreferences() {
    theoremProver.setPreferences();
  }

  @Override
  public String getProviderName() {
    return theoremProver.getProviderName();
  }
}
