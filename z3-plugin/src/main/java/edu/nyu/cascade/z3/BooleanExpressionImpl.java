package edu.nyu.cascade.z3;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Pattern;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Symbol;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.ComparableType;
import edu.nyu.cascade.prover.type.Type;

final class BooleanExpressionImpl extends ExpressionImpl implements
    BooleanExpression {
  
  static BooleanExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBoolean());
    Preconditions.checkArgument(b.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.AND,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkAnd(new BoolExpr[]{(BoolExpr) left, (BoolExpr) right});
          }
        }, a, b);
  }

  static BooleanExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    return new BooleanExpressionImpl(exprManager, Kind.AND,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args)
              throws Z3Exception {
            BoolExpr[] bool_args = Arrays.copyOf(args, args.length, BoolExpr[].class);
            return ctx.mkAnd(bool_args);
          }
        }, args);
  }

  // TODO: Give this method package scope (requires move of bv classes)
  public static BooleanExpressionImpl mkBvGeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.GEQ,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkBVUGE((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }
  
  public static BooleanExpressionImpl mkBvSGeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.GEQ,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkBVSGE((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }

  // TODO: Give this method package scope (requires move of bv classes)
  public static BooleanExpressionImpl mkBvGt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.GT,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkBVUGT((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }
  
  public static BooleanExpressionImpl mkBvSGt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.GT,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkBVSGT((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }

  static BooleanExpressionImpl mkBvLeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.LEQ,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.mkBVULE((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BooleanExpressionImpl mkBvSLeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.LEQ,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.mkBVSLE((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkBvLt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.LT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.mkBVULT((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BooleanExpressionImpl mkBvSLt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    if(a.asBitVector().getSize() > b.asBitVector().getSize()) {
    	b = b.asBitVector().signExtend(a.asBitVector().getSize());
    } else if(a.asBitVector().getSize() < b.asBitVector().getSize()) {
    	a = a.asBitVector().signExtend(b.asBitVector().getSize());
    }
    return new BooleanExpressionImpl(exprManager, Kind.LT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.mkBVSLT((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static  BooleanExpressionImpl mkDistinct(
      ExpressionManagerImpl exprManager, Expression first,
      Expression second, Expression... rest) {
    return mkDistinct(exprManager, Lists.asList(first, second, rest));
  }

  static  BooleanExpressionImpl mkDistinct(
      ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> subExpressions) {
    Preconditions.checkArgument(Iterables.size(subExpressions) > 1);
    return new BooleanExpressionImpl(exprManager, Kind.DISTINCT,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
            return ctx.mkDistinct(args);
          }
        }, subExpressions);
  }

  static  BooleanExpressionImpl mkEq(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.EQUAL,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.mkEq(left, right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkExistsConst(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.EXISTS,
        new BinderTriggersConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] vars, Expr body, 
              Expr[] pattern, Expr[] noPattern, Symbol quantifierID, Symbol skolemID) {
            try {
              Pattern[] ptns = pattern != null ? new Pattern[] { ctx.mkPattern(pattern) } : null;
              return ctx.mkExists(vars, body, 1, ptns, noPattern, quantifierID, skolemID);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
    }, vars, body, triggers, noTriggers);
    if(triggers != null) e.setTriggers(triggers);
    if(noTriggers != null) e.setNoTriggers(noTriggers);
    if(vars != null) e.setBoundVars(vars);
    e.setBody(body.asBooleanExpression());
    return e;
  }
  
  static BooleanExpressionImpl mkExists(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.EXISTS,
        new BinderTriggersDeBruijnConstructionStrategy() {
					@Override
          public Expr apply(Context ctx, Sort[] sorts, Symbol[] names,
              Expr body, Expr[] pattern, Expr[] noPatter, Symbol quantifierID,
              Symbol skolemID) {
						try {
							Pattern[] ptns = pattern != null ? new Pattern[] { ctx.mkPattern(pattern) } : null;
              return ctx.mkExists(sorts, names, body, 1, ptns, noPatter, quantifierID, skolemID);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
    }, vars, body, triggers, noTriggers);
    if(triggers != null) e.setTriggers(triggers);
    if(noTriggers != null) e.setNoTriggers(noTriggers);
    if(vars != null) e.setBoundVars(vars);
    e.setBody(body.asBooleanExpression());
    return e;
  }

  static BooleanExpressionImpl mkFalse(ExpressionManagerImpl exprManager) {
  	return new BooleanExpressionImpl(exprManager, Kind.CONSTANT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            return ctx.mkFalse();
          }
  	});
  }
  
  static BooleanExpressionImpl mkForallConst(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers, 
      Iterable<? extends Expression> noTriggers) {
    
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.FORALL,
        new BinderTriggersConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] vars, Expr body, 
              Expr[] pattern, Expr[] noPatter, Symbol quantifierID, Symbol skolemID) {
            try {
              Pattern[] ptns = pattern != null ? new Pattern[] { ctx.mkPattern(pattern) } : null;
              return ctx.mkForall(vars, body, 1, ptns, noPatter, quantifierID, skolemID);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
        }, vars, body, triggers, noTriggers);
    if(triggers != null) e.setTriggers(triggers);
    if(noTriggers != null) e.setNoTriggers(noTriggers);
    if(vars != null) e.setBoundVars(vars);
    e.setBody(body.asBooleanExpression());
    return e;
  }
  
  static BooleanExpressionImpl mkForall(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.FORALL,
        new BinderTriggersDeBruijnConstructionStrategy() {
					@Override
          public Expr apply(Context ctx, Sort[] sorts, Symbol[] names,
              Expr body, Expr[] pattern, Expr[] noPatter, Symbol quantifierID,
              Symbol skolemID) {
						try {
							Pattern[] ptns = pattern != null ? new Pattern[] { ctx.mkPattern(pattern) } : null;
              return ctx.mkForall(sorts, names, body, 1, ptns, noPatter, quantifierID, skolemID);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
    }, vars, body, triggers, noTriggers);
    if(triggers != null) e.setTriggers(triggers);
    if(noTriggers != null) e.setNoTriggers(noTriggers);
    if(vars != null) e.setBoundVars(vars);
    e.setBody(body.asBooleanExpression());
    return e;
  }

  static <T extends ComparableType> BooleanExpressionImpl mkGeq(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.GEQ,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right)
              throws Z3Exception {
            return ctx.mkGe((ArithExpr) left, (ArithExpr) right);
          }
        }, a, b);
  }

  static <T extends ComparableType> BooleanExpressionImpl mkGt(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.GT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkGt((ArithExpr) left, (ArithExpr) right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkIff(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBoolean());
    Preconditions.checkArgument(b.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.IFF,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkIff((BoolExpr) left, (BoolExpr) right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkImplies(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBoolean());
    Preconditions.checkArgument(b.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.IMPLIES,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right)
              throws Z3Exception {
            return ctx.mkImplies((BoolExpr) left, (BoolExpr) right);
          }
        }, a, b);
  }

  static <T extends ComparableType> BooleanExpressionImpl mkLeq(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.LEQ,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkLe((ArithExpr) left, (ArithExpr) right);
      }
    }, a, b);
  }

  static <T extends ComparableType> BooleanExpressionImpl mkLt(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.LT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkLt((ArithExpr) left, (ArithExpr) right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkNot(ExpressionManagerImpl exprManager,
      Expression arg) {
    Preconditions.checkArgument(arg.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.NOT,
        new UnaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr arg) throws Z3Exception {
        return ctx.mkNot((BoolExpr) arg);
      }
    }, arg);
  }

  static BooleanExpressionImpl mkOr(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBoolean());
    Preconditions.checkArgument(b.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.OR,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.mkOr(new BoolExpr[] {(BoolExpr) left, (BoolExpr) right});
          }
        }, a, b);
  }

  static BooleanExpressionImpl mkOr(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    for(Expression arg : args) Preconditions.checkArgument(arg.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.OR,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
            BoolExpr [] boolArgs = Arrays.copyOf(args, args.length, BoolExpr[].class);
            return ctx.mkOr(boolArgs);
          }
        }, args);
  }
  
  static BooleanExpressionImpl mkOr(ExpressionManagerImpl exprManager,
      Expression first, Expression... rest) {
    Preconditions.checkArgument(first.isBoolean());
    for(Expression restElem : rest) Preconditions.checkArgument(restElem.isBoolean());
    ImmutableList<Expression> args = new ImmutableList.Builder<Expression>().add(first).add(rest).build();
    return mkOr(exprManager, args);
  }

  static BooleanExpressionImpl mkTrue(ExpressionManagerImpl exprManager) {
  	return new BooleanExpressionImpl(exprManager, Kind.CONSTANT,
  			new NullaryConstructionStrategy() {
  		@Override
  		public Expr apply(Context ctx) throws Z3Exception {
  			return ctx.mkTrue();
  		}
  	});
  }

  static BooleanExpressionImpl mkXor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.XOR,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right)
              throws Z3Exception {
            return ctx.mkXor((BoolExpr) left, (BoolExpr) right); 
          }
        }, a, b);
  }

  static BooleanExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      Expression e) {
    if( exprManager.equals( e.getExpressionManager() ) ) {
      if (e instanceof BooleanExpressionImpl) {
        return (BooleanExpressionImpl) e;
      } else if (e instanceof ExpressionImpl) {
        return new BooleanExpressionImpl((ExpressionImpl) e);
      }
    }
    
    switch( e.getKind() ) {
    default:
      throw new UnsupportedOperationException();
    }
  }

  private List<ImmutableList<? extends Expression>> triggers = Lists.newArrayList();
  private ImmutableList<? extends Expression> boundVars = null;
  private BooleanExpression body = null;

  private BooleanExpressionImpl(ExpressionImpl e) {
    super(e);
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right) {
    super(exprManager, kind, strategy, left, right);
    setType(exprManager.booleanType());
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      TernaryConstructionStrategy strategy, Expression a,
      Expression b, Expression c) {
    super(exprManager, kind, strategy, a, b, c);
    setType(exprManager.booleanType());
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinderTriggersConstructionStrategy strategy,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    super(exprManager, kind, strategy, vars, body, triggers, noTriggers);
    setType(exprManager.booleanType());
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinderTriggersDeBruijnConstructionStrategy strategy,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    super(exprManager, kind, strategy, vars, body, triggers, noTriggers);
    setType(exprManager.booleanType());
  }

  private  BooleanExpressionImpl(ExpressionManagerImpl exprManager,
      Kind kind, NaryConstructionStrategy construct,
      Iterable<? extends Expression> subExpressions) {
    super(exprManager, kind, construct, subExpressions);
    setType(exprManager.booleanType());
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy, Expression first,
      Expression[] rest) throws Z3Exception {
    super(exprManager, kind, strategy, first, rest);
  }

  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NullaryConstructionStrategy strategy) {
    super(exprManager, kind, strategy);
    setType(exprManager.booleanType());
  }

  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression arg) {
    super(exprManager, kind, strategy, arg);
    setType(exprManager.booleanType());
  }

  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, final boolean value) {
    super(exprManager, Kind.CONSTANT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            return ctx.mkBool(value);
          }
        });
    setType(exprManager.booleanType());
  }
  
  private BooleanExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, BooleanType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  static BooleanExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isBoolean());
    return new BooleanExpressionImpl(em, kind, expr, type.asBooleanType(), children);
  }

  @Override
  public void addTrigger(Expression p) {
    triggers.add(ImmutableList.<Expression>of(p));
  }

  @Override
  public BooleanExpressionImpl and(Expression e) {
    return mkAnd(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpressionImpl and(
      Iterable<? extends Expression> conjuncts) {
    List<Expression> conj2 = Lists.newArrayList(conjuncts);
    conj2.add(0, this);
    return mkAnd(getExpressionManager(), conj2);
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

  @Override
  public BooleanExpressionImpl not() {
    return mkNot(getExpressionManager(), this);
  }

  @Override
  public BooleanExpressionImpl or(Expression e) {
    return mkOr(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpression or(
      Iterable<? extends Expression> disjuncts) {
    List<Expression> disj2 = Lists.newArrayList(disjuncts);
    disj2.add(0, this);
    return mkOr(getExpressionManager(), disj2);
  }

  @Override
  public void setTriggers(Iterable<? extends Expression> triggers) {
    List<ImmutableList<? extends Expression>> multiTriggers = Lists.newArrayList();
    for( Expression trigger : triggers ) {
      multiTriggers.add( ImmutableList.<Expression>of(trigger) );
    }
    this.triggers = multiTriggers;
  }
  
  private void setNoTriggers(Iterable<? extends Expression> noTriggers) {
    List<ImmutableList<? extends Expression>> multiTriggers = Lists.newArrayList();
    for( Expression trigger : noTriggers ) {
      multiTriggers.add( ImmutableList.<Expression>of(trigger) );
    }
  }

  @Override
  public BooleanExpressionImpl xor(Expression e) {
    return mkXor(getExpressionManager(), this, e);
  }

  @Override
  public Expression ifThenElse(
      Expression thenPart, Expression elsePart) {
    return ExpressionImpl.mkIte(getExpressionManager(), this, thenPart, elsePart);
  }

  @Override
  public void addMultiTrigger(Iterable<? extends Expression> multiTrigger) {
    triggers.add(ImmutableList.copyOf(multiTrigger));
    /* internalSetTriggers(); */
  }

  @Override
  public void setMultiTriggers(
      Iterable<? extends Iterable<? extends Expression>> multiTriggers) {
    List<ImmutableList<? extends Expression>> multiTriggerList = Lists.newArrayList();
    for ( Iterable<? extends Expression> multiTrigger : multiTriggers ) {
      ImmutableList.Builder<Expression> triggerList = ImmutableList.builder();
      for( Expression trigger : multiTrigger ) {
        triggerList.add( trigger );
      }
      multiTriggerList.add(triggerList.build());
    }
    this.triggers = multiTriggerList;
  }  
  
  @Override
  public BooleanExpression exists(Iterable<? extends Expression> vars) {
    return getExpressionManager().booleanType().exists(vars, this);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars) {
    return getExpressionManager().booleanType().forall(vars, this);
  }

  @Override
  public BooleanExpression exists(Expression firstVar, Expression... otherVars) {
    return exists(Lists.asList(firstVar, otherVars));
  }

  @Override
  public BooleanExpression forall(Expression firstVar,Expression... otherVars) {
    return forall(Lists.asList(firstVar, otherVars));
  }
  
  @Override
  public void setBoundVars(Iterable<? extends Expression> vars) {
    boundVars = ImmutableList.copyOf(vars);
  }

  @Override
  public ImmutableList<? extends Expression> getBoundVars() {
    if(boundVars == null)   return null;
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
