package edu.nyu.cascade.z3;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
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
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ComparableType;

public class BooleanExpressionImpl extends ExpressionImpl implements
    BooleanExpression {
  
/*  private static final ConcurrentMap<ExpressionManager, ConcurrentMap<Boolean, BooleanExpression>> constantCache = new MapMaker()
      .makeComputingMap(new Function<ExpressionManager, ConcurrentMap<Boolean, BooleanExpression>>() {
        @Override
        public ConcurrentMap<Boolean, BooleanExpression> apply(
            final ExpressionManager exprManager) {
          return new MapMaker()
              .makeComputingMap(new Function<Boolean, BooleanExpression>() {
                @Override
                public BooleanExpression apply(Boolean value) {
                  return new BooleanExpression(exprManager, value);
                }
              });
        }
      });
*/  
  
  static BooleanExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBoolean());
    Preconditions.checkArgument(b.isBoolean());
    return new BooleanExpressionImpl(exprManager, Kind.AND,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.MkAnd(new BoolExpr[]{(BoolExpr) left, (BoolExpr) right});
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
            return ctx.MkAnd(bool_args);
          }
        }, args);
  }

  // TODO: Give this method package scope (requires move of bv classes)
  public static BooleanExpressionImpl mkBvGeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.GEQ,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.MkBVUGE((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }
  
  public static BooleanExpressionImpl mkBvSGeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.GEQ,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.MkBVSGE((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }

  // TODO: Give this method package scope (requires move of bv classes)
  public static BooleanExpressionImpl mkBvGt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.GT,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.MkBVUGT((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }
  
  public static BooleanExpressionImpl mkBvSGt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.GT,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            return ctx.MkBVSGT((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
  }

  static BooleanExpressionImpl mkBvLeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.LEQ,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVULE((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BooleanExpressionImpl mkBvSLeq(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.LEQ,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSLE((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkBvLt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return new BooleanExpressionImpl(exprManager, Kind.LT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVULT((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BooleanExpressionImpl mkBvSLt(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.LT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSLT((BitVecExpr) left, (BitVecExpr) right);
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
            return ctx.MkDistinct(args);
          }
        }, subExpressions);
  }

  static  BooleanExpressionImpl mkEq(
      ExpressionManagerImpl exprManager, Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.EQUAL,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkEq(left, right);
      }
    }, a, b);
  }

  static BooleanExpressionImpl mkExists(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers,
      Iterable<? extends Expression> noTriggers) {
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.EXISTS,
        new BinderTriggersConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] vars, Expr body, 
              Expr[] triggers, Expr[] noTriggers, Symbol pid, Symbol skid) {
            try {
              Pattern[] ptns = triggers != null ? new Pattern[] { ctx.MkPattern(triggers) } : null;
              boolean isBound = Iterables.all(Arrays.asList(vars), new Predicate<Expr>() {
                @Override public boolean apply(Expr expr) {
                  try {
                    return !expr.IsConst();
                  } catch (Z3Exception e) {
                    throw new TheoremProverException(e);
                  }
                }
              });
              if(!isBound) {
                Symbol[] symbols = new Symbol[vars.length];
                Sort[] types = new Sort[vars.length];
                Expr[] bounds = new Expr[vars.length];
                int i = 0;
                for(Expr var : vars) {
                  symbols[i] = ctx.MkSymbol(var.toString());
                  types[i] = var.Sort();
                  bounds[i] = ctx.MkBound(i, types[i]);
                  i++;
                }
                body = body.Substitute(vars, bounds);
                /* FIXME: Z3 with warning unknown attribute :skid, and take null for :qid and :skid
                 */
                return ctx.MkForall(types, symbols, body, 0, ptns, noTriggers, null, null);
              } else { 
                return ctx.MkForall(vars, body, 0, ptns, noTriggers, null, null);
              }
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
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.CONSTANT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            return ctx.MkFalse();
          }
        });
    e.setConstant(true);
    return e;
  }
  
  static BooleanExpressionImpl mkForall(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> vars, 
      Expression body, 
      Iterable<? extends Expression> triggers, 
      Iterable<? extends Expression> noTriggers) {
    
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.FORALL,
        new BinderTriggersConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] vars, Expr body, 
              Expr[] triggers, Expr[] noTriggers, Symbol pid, Symbol skid) {
            try {
              Pattern[] ptns = triggers != null ? new Pattern[] { ctx.MkPattern(triggers) } : null;
              boolean isBound = Iterables.all(Arrays.asList(vars), new Predicate<Expr>() {
                @Override public boolean apply(Expr expr) {
                  try {
                    return !expr.IsConst();
                  } catch (Z3Exception e) {
                    throw new TheoremProverException(e);
                  }
                }
              });
              if(!isBound) {
                Symbol[] symbols = new Symbol[vars.length];
                Sort[] types = new Sort[vars.length];
                Expr[] bounds = new Expr[vars.length];
                int i = 0;
                for(Expr var : vars) {
                  symbols[i] = ctx.MkSymbol(var.toString());
                  types[i] = var.Sort();
                  bounds[i] = ctx.MkBound(i, types[i]);
                  i++;
                }
                body = body.Substitute(vars, bounds);
                return ctx.MkForall(types, symbols, body, 1, ptns, noTriggers, null, null);
              } else { 
                return ctx.MkForall(vars, body, 1, ptns, noTriggers, null, null);
              } 
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
            return ctx.MkGe((ArithExpr) left, (ArithExpr) right);
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
        return ctx.MkGt((ArithExpr) left, (ArithExpr) right);
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
        return ctx.MkIff((BoolExpr) left, (BoolExpr) right);
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
            return ctx.MkImplies((BoolExpr) left, (BoolExpr) right);
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
        return ctx.MkLe((ArithExpr) left, (ArithExpr) right);
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
        return ctx.MkLt((ArithExpr) left, (ArithExpr) right);
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
        return ctx.MkNot((BoolExpr) arg);
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
            return ctx.MkOr(new BoolExpr[] {(BoolExpr) left, (BoolExpr) right});
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
            return ctx.MkOr(boolArgs);
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
    BooleanExpressionImpl e = new BooleanExpressionImpl(exprManager, Kind.CONSTANT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            return ctx.MkTrue();
          }
        });
    e.setConstant(true);
    return e;
  }

  static BooleanExpressionImpl mkXor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new BooleanExpressionImpl(exprManager, Kind.XOR,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right)
              throws Z3Exception {
            return ctx.MkXor((BoolExpr) left, (BoolExpr) right); 
          }
        }, a, b);
  }
  
  static BooleanExpressionImpl mkRewriteRule(ExpressionManagerImpl exprManager,
      Iterable<? extends VariableExpression> vars, Expression guard, Expression rule) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRRewrite(ExpressionManagerImpl exprManager,
      Expression head, Expression body) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRRewrite(ExpressionManagerImpl exprManager,
      Expression head, Expression body, Iterable<? extends Expression> triggers) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRReduction(ExpressionManagerImpl exprManager,
      Expression head, Expression body) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRReduction(ExpressionManagerImpl exprManager,
      Expression head, Expression body, Iterable<? extends Expression> triggers) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRDeduction(ExpressionManagerImpl exprManager,
      Expression head, Expression body) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
  }
  
  static BooleanExpressionImpl mkRRDeduction(ExpressionManagerImpl exprManager,
      Expression head, Expression body, Iterable<? extends Expression> triggers) {
    throw new UnsupportedOperationException("Rewrite rule is not supported in z3.");
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
  private List<ImmutableList<? extends Expression>> noTriggers = Lists.newArrayList();
  private ImmutableList<? extends Expression> boundVars = null;
  private BooleanExpression body = null;

  private BooleanExpressionImpl(ExpressionImpl e) {
    super(e);
  }
  
/*  private BooleanExpression(ExpressionManager exprManager, IExpression b) {
    super(exprManager,b);
  }
*/
  protected BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right) {
    super(exprManager, kind, strategy, left, right);
    setType(exprManager.booleanType());
  }
  
  protected BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
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

  protected BooleanExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression arg) {
    super(exprManager, kind, strategy, arg);
    setType(exprManager.booleanType());
  }

  private BooleanExpressionImpl(ExpressionManagerImpl exprManager, final boolean value) {
    super(exprManager, Kind.CONSTANT,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx) throws Z3Exception {
            return ctx.MkBool(value);
          }
        });
    setType(exprManager.booleanType());
    setConstant(true);
  }

  @Override
  public void addTrigger(Expression p) {
    triggers.add(ImmutableList.<Expression>of(p));
   /* internalSetTriggers();*/
  }
  
  public void addNoTrigger(Expression p) {
    noTriggers.add(ImmutableList.<Expression>of(p));
   /* internalSetNoTriggers();*/
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
    /*internalSetTriggers();*/
  }
  
  public void setNoTriggers(Iterable<? extends Expression> noTriggers) {
    List<ImmutableList<? extends Expression>> multiTriggers = Lists.newArrayList();
    for( Expression trigger : noTriggers ) {
      multiTriggers.add( ImmutableList.<Expression>of(trigger) );
    }
    this.noTriggers = multiTriggers;
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
  
  public void addMultiNoTrigger(Iterable<? extends Expression> multiNoTriggers) {
    noTriggers.add(ImmutableList.copyOf(multiNoTriggers));
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
    /*internalSetTriggers();*/
  }

  public void setMultiNoTriggers(
      Iterable<? extends Iterable<? extends Expression>> multiNoTriggers) {
    List<ImmutableList<? extends Expression>> multiTriggerList = Lists.newArrayList();
    for ( Iterable<? extends Expression> multiTrigger : multiNoTriggers ) {
      ImmutableList.Builder<Expression> triggerList = ImmutableList.builder();
      for( Expression trigger : multiTrigger ) {
        triggerList.add( trigger );
      }
      multiTriggerList.add(triggerList.build());
    }
    this.noTriggers = multiTriggerList;
    /*internalSetTriggers();*/
  }
  

  // FIXME: the func is used for what?
  @Override
  public BooleanExpressionImpl exists(Iterable<? extends Expression> vars) {
    return mkExists(getExpressionManager(), vars, this, null, null);
  }

  @Override
  public BooleanExpression forall(Iterable<? extends Expression> vars) {
    return mkForall(getExpressionManager(), vars, this, null, null);
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
