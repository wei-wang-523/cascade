package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.ComparableType;

class BooleanExpressionImpl extends ExpressionImpl implements
    BooleanExpression {

	static BooleanExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.AND,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.AND, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> args) {
		return new BooleanExpressionImpl(exprManager, Kind.AND,
		    new NaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				    Expr result = null;
				    for (Expr arg : args) {
					    if (result == null)
						    result = arg;
					    else {
						    result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.AND, arg, result);
					    }
				    }
				    return result;
			    }
		    }, args);
	}

	// TODO: Give this method package scope (requires move of bv classes)
	static BooleanExpressionImpl mkBvGeq(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.GEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGE, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvSGeq(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.GEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGE, left,
		            right);
			    }
		    }, a, b);
	}

	// TODO: Give this method package scope (requires move of bv classes)
	static BooleanExpressionImpl mkBvGt(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.GT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_UGT, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvSGt(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.GT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SGT, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvLeq(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.LEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULE, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvSLeq(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.LEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLE, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvLt(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.LT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_ULT, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkBvSLt(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		Preconditions.checkArgument(a.isBitVector());
		Preconditions.checkArgument(b.isBitVector());
		if (a.asBitVector().getSize() > b.asBitVector().getSize()) {
			b = b.asBitVector().signExtend(a.asBitVector().getSize());
		} else if (a.asBitVector().getSize() < b.asBitVector().getSize()) {
			a = a.asBitVector().signExtend(b.asBitVector().getSize());
		}
		return new BooleanExpressionImpl(exprManager, Kind.LT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SLT, left,
		            right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkDistinct(ExpressionManagerImpl exprManager,
	    Expression first, Expression second, Expression... rest) {
		return mkDistinct(exprManager, Lists.asList(first, second, rest));
	}

	static BooleanExpressionImpl mkDistinct(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> subExpressions) {
		Preconditions.checkArgument(Iterables.size(subExpressions) > 1);
		return new BooleanExpressionImpl(exprManager, Kind.DISTINCT,
		    new NaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				    vectorExpr argList = new vectorExpr();
				    for (Expr arg : args)
					    argList.add(arg);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.DISTINCT, argList);
			    }
		    }, subExpressions);
	}

	static BooleanExpressionImpl mkEq(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.EQUAL,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.EQUAL, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkExists(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> vars, Expression body) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.EXISTS, new BinderConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> vars, Expr body)
		          throws Exception {
				    vectorExpr varList = new vectorExpr();
				    for (Expr var : vars)
					    varList.add(var);
				    Expr boundVarList = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.EXISTS, boundVarList,
		            body);
			    }
		    }, vars, body);
		if (vars != null)
			e.setBoundVars(vars);
		e.setBody(body.asBooleanExpression());
		return e;
	}

	static BooleanExpressionImpl mkExists(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> vars, Expression body,
	    Iterable<? extends Expression> triggers) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.EXISTS, new BinderTriggersConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> vars, Expr body,
		          List<Expr> triggers) throws Exception {
				    vectorExpr varList = new vectorExpr();
				    for (Expr var : vars)
					    varList.add(var);
				    Expr boundVarList = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
				    vectorExpr triggerList = new vectorExpr();
				    for (Expr trigger : triggers) {
					    Expr pat = em.mkExpr(edu.nyu.acsys.CVC4.Kind.INST_PATTERN,
		              trigger);
					    triggerList.add(pat);
				    }
				    Expr triggersPattern = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.INST_PATTERN_LIST, triggerList);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.EXISTS, boundVarList, body,
		            triggersPattern);
			    }
		    }, vars, body, triggers);
		if (triggers != null)
			e.setTriggers(triggers);
		if (vars != null)
			e.setBoundVars(vars);
		e.setBody(body.asBooleanExpression());
		return e;
	}

	static BooleanExpressionImpl mkFalse(ExpressionManagerImpl exprManager) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.CONSTANT, new NullaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em) throws Exception {
				    return em.mkConst(false);
			    }
		    });
		return e;
	}

	static BooleanExpressionImpl mkForall(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> vars, Expression body) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.FORALL, new BinderConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> vars, Expr body)
		          throws Exception {
				    vectorExpr varList = new vectorExpr();
				    for (Expr var : vars)
					    varList.add(var);
				    Expr boundVarList = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.FORALL, boundVarList,
		            body);
			    }
		    }, vars, body);
		if (vars != null)
			e.setBoundVars(vars);
		e.setBody(body.asBooleanExpression());
		return e;
	}

	static BooleanExpressionImpl mkForall(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> vars, Expression body,
	    Iterable<? extends Expression> triggers) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.FORALL, new BinderTriggersConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> vars, Expr body,
		          List<Expr> triggers) throws Exception {
				    vectorExpr varList = new vectorExpr();
				    for (Expr var : vars)
					    varList.add(var);
				    Expr boundVarList = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
				    vectorExpr triggerList = new vectorExpr();
				    for (Expr trigger : triggers) {
					    Expr pat = em.mkExpr(edu.nyu.acsys.CVC4.Kind.INST_PATTERN,
		              trigger);
					    triggerList.add(pat);
				    }
				    Expr triggersPattern = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.INST_PATTERN_LIST, triggerList);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.FORALL, boundVarList, body,
		            triggersPattern);
			    }
		    }, vars, body, triggers);
		if (triggers != null)
			e.setTriggers(triggers);
		if (vars != null)
			e.setBoundVars(vars);
		e.setBody(body.asBooleanExpression());
		return e;
	}

	static <T extends ComparableType> BooleanExpressionImpl mkGeq(
	    ExpressionManagerImpl exprManager, Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.GEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.GEQ, left, right);
			    }
		    }, a, b);
	}

	static <T extends ComparableType> BooleanExpressionImpl mkGt(
	    ExpressionManagerImpl exprManager, Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.GT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.GT, left, right);
			    }
		    }, a, b);
	}

	// FIXME: getTypePred is not supported in cvc4
	/*
	 * static BooleanExpressionImpl mkHasType(ExpressionManagerImpl exprManager,
	 * Expression expr, final Type type) { final TypeImpl type2 =
	 * exprManager.importType(type); if( !exprManager.integerType().equals( type2
	 * ) ) { throw new UnsupportedOperationException(
	 * "mkHasType on non-integer type:" + type); } return new
	 * BooleanExpressionImpl(exprManager, Kind.HAS_TYPE, new
	 * UnaryConstructionStrategy() {
	 * 
	 * @Override public Expr apply(ExprManager em, Expr arg) { return
	 * em.getTypePred(type2.getCVC4Type(), arg); } }, expr); }
	 */

	static BooleanExpressionImpl mkIff(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.IFF,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.IFF, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkImplies(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.IMPLIES,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.IMPLIES, left, right);
			    }
		    }, a, b);
	}

	static <T extends ComparableType> BooleanExpressionImpl mkLeq(
	    ExpressionManagerImpl exprManager, Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.LEQ,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.LEQ, left, right);
			    }
		    }, a, b);
	}

	static <T extends ComparableType> BooleanExpressionImpl mkLt(
	    ExpressionManagerImpl exprManager, Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.LT,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.LT, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkNot(ExpressionManagerImpl exprManager,
	    Expression arg) {
		return new BooleanExpressionImpl(exprManager, Kind.NOT,
		    new UnaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr arg) throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.NOT, arg);
			    }
		    }, arg);
	}

	static BooleanExpressionImpl mkOr(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.OR,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.OR, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkOr(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> args) {
		return new BooleanExpressionImpl(exprManager, Kind.OR,
		    new NaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> args) throws Exception {
				    Expr result = null;
				    for (Expr arg : args) {
					    if (result == null)
						    result = arg;
					    else {
						    result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.OR, arg, result);
					    }
				    }
				    return result;
			    }
		    }, args);
	}

	static BooleanExpressionImpl mkTrue(ExpressionManagerImpl exprManager) {
		BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager,
		    Kind.CONSTANT, new NullaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em) throws Exception {
				    return em.mkConst(true);
			    }
		    });
		return e;
	}

	static BooleanExpressionImpl mkXor(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
		return new BooleanExpressionImpl(exprManager, Kind.XOR,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr left, Expr right)
		          throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.XOR, left, right);
			    }
		    }, a, b);
	}

	static BooleanExpressionImpl mkRewriteRule(ExpressionManagerImpl exprManager,
	    Iterable<? extends Expression> vars, Expression guard, Expression rule) {
		return new BooleanExpressionImpl(exprManager, Kind.REWRITE_RULE,
		    new BinderGuardConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, List<Expr> vars, Expr guard,
		          Expr rule) throws Exception {
				    vectorExpr varList = new vectorExpr();
				    for (Expr var : vars)
					    varList.add(var);
				    Expr boundVarList = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.BOUND_VAR_LIST, varList);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.REWRITE_RULE, boundVarList,
		            guard, rule);
			    }
		    }, vars, guard, rule);
	}

	static BooleanExpressionImpl mkRRRewrite(ExpressionManagerImpl exprManager,
	    Expression head, Expression body) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_REWRITE,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr h, Expr b) throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_REWRITE, h, b);
			    }
		    }, head, body);
	}

	static BooleanExpressionImpl mkRRRewrite(ExpressionManagerImpl exprManager,
	    Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_REWRITE,
		    new BinderTriggersWithRewriteRuleConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr head, Expr body,
		          List<Expr> triggers) throws Exception {
				    vectorExpr triggerList = new vectorExpr();
				    for (Expr trigger : triggers) {
					    Expr pat = em.mkExpr(edu.nyu.acsys.CVC4.Kind.INST_PATTERN,
		              trigger);
					    triggerList.add(pat);
				    }
				    Expr triggersPattern = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.INST_PATTERN_LIST, triggerList);
				    vectorExpr argList = new vectorExpr();
				    argList.add(head);
				    argList.add(body);
				    argList.add(triggersPattern);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_REWRITE, argList);
			    }
		    }, head, body, triggers);
	}

	static BooleanExpressionImpl mkRRReduction(ExpressionManagerImpl exprManager,
	    Expression head, Expression body) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_REDUCTION,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr h, Expr b) throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_REDUCTION, h, b);
			    }
		    }, head, body);
	}

	static BooleanExpressionImpl mkRRReduction(ExpressionManagerImpl exprManager,
	    Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_REDUCTION,
		    new BinderTriggersWithRewriteRuleConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr head, Expr body,
		          List<Expr> triggers) throws Exception {
				    vectorExpr triggerList = new vectorExpr();
				    for (Expr trigger : triggers) {
					    Expr pat = em.mkExpr(edu.nyu.acsys.CVC4.Kind.INST_PATTERN,
		              trigger);
					    triggerList.add(pat);
				    }
				    Expr triggersPattern = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.INST_PATTERN_LIST, triggerList);
				    vectorExpr argList = new vectorExpr();
				    argList.add(head);
				    argList.add(body);
				    argList.add(triggersPattern);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_REDUCTION, argList);
			    }
		    }, head, body, triggers);
	}

	static BooleanExpressionImpl mkRRDeduction(ExpressionManagerImpl exprManager,
	    Expression head, Expression body) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_DEDUCTION,
		    new BinaryConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr h, Expr b) throws Exception {
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_DEDUCTION, h, b);
			    }
		    }, head, body);
	}

	static BooleanExpressionImpl mkRRDeduction(ExpressionManagerImpl exprManager,
	    Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		return new BooleanExpressionImpl(exprManager, Kind.RR_DEDUCTION,
		    new BinderTriggersWithRewriteRuleConstructionStrategy() {
			    @Override
			    public Expr apply(ExprManager em, Expr head, Expr body,
		          List<Expr> triggers) throws Exception {
				    vectorExpr triggerList = new vectorExpr();
				    for (Expr trigger : triggers) {
					    Expr pat = em.mkExpr(edu.nyu.acsys.CVC4.Kind.INST_PATTERN,
		              trigger);
					    triggerList.add(pat);
				    }
				    Expr triggersPattern = em.mkExpr(
		            edu.nyu.acsys.CVC4.Kind.INST_PATTERN_LIST, triggerList);
				    vectorExpr argList = new vectorExpr();
				    argList.add(head);
				    argList.add(body);
				    argList.add(triggersPattern);
				    return em.mkExpr(edu.nyu.acsys.CVC4.Kind.RR_DEDUCTION, argList);
			    }
		    }, head, body, triggers);
	}

	static BooleanExpressionImpl valueOf(ExpressionManagerImpl exprManager,
	    Expression e) {
		if (exprManager.equals(e.getExpressionManager())) {
			if (e instanceof BooleanExpressionImpl) {
				return (BooleanExpressionImpl) e;
			} else if (e instanceof ExpressionImpl) {
				return new BooleanExpressionImpl((ExpressionImpl) e);
			}
		}

		switch (e.getKind()) {
		default:
			throw new UnsupportedOperationException();
		}
	}

	private List<ImmutableList<? extends Expression>> triggers = Lists
	    .newArrayList();
	private ImmutableList<? extends Expression> boundVars = null;
	private BooleanExpression body = null;

	private BooleanExpressionImpl(ExpressionImpl e) {
		super(e);
	}

	/*
	 * private BooleanExpression(ExpressionManager exprManager, IExpression b) {
	 * super(exprManager,b); }
	 */
	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinaryConstructionStrategy strategy, Expression left, Expression right) {
		super(exprManager, kind, strategy, left, right);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    TernaryConstructionStrategy strategy, Expression a, Expression b,
	    Expression c) {
		super(exprManager, kind, strategy, a, b, c);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinderConstructionStrategy strategy, Iterable<? extends Expression> vars,
	    Expression body) {
		super(exprManager, kind, strategy, vars, body);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinderGuardConstructionStrategy strategy,
	    Iterable<? extends Expression> vars, Expression guard, Expression body) {
		super(exprManager, kind, strategy, vars, guard, body);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinderTriggersWithRewriteRuleConstructionStrategy strategy,
	    Expression head, Expression body,
	    Iterable<? extends Expression> triggers) {
		super(exprManager, kind, strategy, head, body, triggers);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    BinderTriggersConstructionStrategy strategy,
	    Iterable<? extends Expression> vars, Expression body,
	    Iterable<? extends Expression> triggers) {
		super(exprManager, kind, strategy, vars, body, triggers);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NaryConstructionStrategy construct,
	    Iterable<? extends Expression> subExpressions) {
		super(exprManager, kind, construct, subExpressions);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    NullaryConstructionStrategy strategy) {
		super(exprManager, kind, strategy);
		setType(exprManager.booleanType());
	}

	protected BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    UnaryConstructionStrategy strategy, Expression arg) {
		super(exprManager, kind, strategy, arg);
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager,
	    boolean value) {
		super(exprManager, Kind.CONSTANT, new NullaryConstructionStrategy() {
			@Override
			public Expr apply(ExprManager em) throws Exception {
				return em.mkConst(true);
			}
		});
		setType(exprManager.booleanType());
	}

	private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
	    Expr expr, BooleanType type,
	    Iterable<? extends ExpressionImpl> children) {
		super(exprManager, kind, expr, type);
	}

	static BooleanExpressionImpl create(ExpressionManagerImpl exprManager,
	    Kind kind, Expr expr, BooleanType type,
	    Iterable<? extends ExpressionImpl> children) {
		return new BooleanExpressionImpl(exprManager, kind, expr, type, children);
	}

	@Override
	public void addTrigger(Expression p) {
		triggers.add(ImmutableList.<Expression> of(p));
		/* internalSetTriggers(); */
	}

	@Override
	public BooleanExpressionImpl and(Expression e) {
		return mkAnd(getExpressionManager(), this, e);
	}

	@Override
	public BooleanExpressionImpl and(Iterable<? extends Expression> conjuncts) {
		List<Expression> conj2 = Lists.newArrayList(conjuncts);
		conj2.add(0, this);
		return mkAnd(getExpressionManager(), conj2);
	}

	@Override
	public BooleanExpressionImpl exists(Iterable<? extends Expression> vars) {
		return mkExists(getExpressionManager(), vars, this);
	}

	@Override
	public BooleanExpression forall(Iterable<? extends Expression> vars) {
		return mkForall(getExpressionManager(), vars, this);
	}

	@Override
	public ImmutableList<ImmutableList<? extends Expression>> getTriggers() {
		return ImmutableList.copyOf(triggers);
	}

	@Override
	public BooleanTypeImpl getType() {
		return getExpressionManager().booleanType();
	}

	@Override
	public BooleanExpressionImpl iff(Expression e) {
		return mkIff(getExpressionManager(), this, e);
	}

	@Override
	public BooleanExpressionImpl implies(Expression e) {
		return mkImplies(getExpressionManager(), this, e);
	}

	// FIXME: setMultiTrigger is not supported yet
	/*
	 * private void internalSetTriggers() { ExprManager em =
	 * getExpressionManager() .getTheoremProver().getCvc4ExprManager();
	 * 
	 * List<List<edu.nyu.acsys.CVC4.Expr>> cvc4Triggers =
	 * Lists.newArrayListWithCapacity(triggers.size()); for ( ImmutableList<?
	 * extends Expression> multiTrigger : triggers ) {
	 * List<edu.nyu.acsys.CVC4.Expr> cvc4MultiTrigger =
	 * Lists.newArrayListWithCapacity(multiTrigger.size()); for( Expression
	 * trigger : multiTrigger ) { cvc4MultiTrigger.add(
	 * getExpressionManager().toCvc4Expr(trigger) ); }
	 * cvc4Triggers.add(cvc4MultiTrigger); }
	 * em.setMultiTriggers(getCvc4Expression(), cvc4Triggers); }
	 */

	@Override
	public BooleanExpressionImpl not() {
		return mkNot(getExpressionManager(), this);
	}

	@Override
	public BooleanExpressionImpl or(Expression e) {
		return mkOr(getExpressionManager(), this, e);
	}

	@Override
	public BooleanExpression or(Iterable<? extends Expression> disjuncts) {
		List<Expression> disj2 = Lists.newArrayList(disjuncts);
		disj2.add(0, this);
		return mkOr(getExpressionManager(), disj2);
	}

	@Override
	public void setTriggers(Iterable<? extends Expression> triggers) {
		List<ImmutableList<? extends Expression>> multiTriggers = Lists
		    .newArrayList();
		for (Expression trigger : triggers) {
			multiTriggers.add(ImmutableList.<Expression> of(trigger));
		}
		this.triggers = multiTriggers;
		/* internalSetTriggers(); */
	}

	@Override
	public BooleanExpressionImpl xor(Expression e) {
		return mkXor(getExpressionManager(), this, e);
	}

	@Override
	public Expression ifThenElse(Expression thenPart, Expression elsePart) {
		return ExpressionImpl.mkIte(getExpressionManager(), this, thenPart,
		    elsePart);
	}

	@Override
	public void addMultiTrigger(Iterable<? extends Expression> multiTrigger) {
		triggers.add(ImmutableList.copyOf(multiTrigger));
		/* internalSetTriggers(); */
	}

	@Override
	public void setMultiTriggers(
	    Iterable<? extends Iterable<? extends Expression>> multiTriggers) {
		List<ImmutableList<? extends Expression>> multiTriggerList = Lists
		    .newArrayList();
		for (Iterable<? extends Expression> multiTrigger : multiTriggers) {
			ImmutableList.Builder<Expression> triggerList = ImmutableList.builder();
			for (Expression trigger : multiTrigger) {
				triggerList.add(trigger);
			}
			multiTriggerList.add(triggerList.build());
		}
		this.triggers = multiTriggerList;
		/* internalSetTriggers(); */
	}

	@Override
	public BooleanExpression exists(Expression firstVar,
	    Expression... otherVars) {
		return exists(Lists.asList(firstVar, otherVars));
	}

	@Override
	public BooleanExpression forall(Expression firstVar,
	    Expression... otherVars) {
		return forall(Lists.asList(firstVar, otherVars));
	}

	@Override
	public void setBoundVars(Iterable<? extends Expression> vars) {
		boundVars = ImmutableList.copyOf(vars);
	}

	@Override
	public ImmutableList<? extends Expression> getBoundVars() {
		return ImmutableList.copyOf(boundVars);
	}

	@Override
	public void setBody(BooleanExpression expr) {
		body = expr;
	}

	@Override
	public BooleanExpression getBody() {
		return body;
	}

}
