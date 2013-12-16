package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.BV_AND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_CONCAT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_EXTRACT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NAND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_OR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_SIGN_EXTEND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_ZERO_EXTEND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_LSHIFT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_RSHIFT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_XNOR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_XOR;
import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.SDIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.REM;
import static edu.nyu.cascade.prover.Expression.Kind.SREM;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;

import java.math.BigInteger;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.Pair;

public class BitVectorExpressionImpl extends ExpressionImpl implements
    BitVectorExpression {
  private static final LoadingCache<ExpressionManagerImpl, LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl>> cache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl>>(){
            public LoadingCache<Pair<String, Integer>, BitVectorExpressionImpl> load(final ExpressionManagerImpl exprManager) {
              return CacheBuilder.newBuilder().build(new CacheLoader<Pair<String, Integer>, BitVectorExpressionImpl>(){
                public BitVectorExpressionImpl load(Pair<String, Integer> pair) {
                  try {
                    return new BitVectorExpressionImpl(exprManager, pair.fst(), pair.snd());
                  } catch (Z3Exception e) {
                    throw new TheoremProverException(e);
                  }
                }
              });
            }
          });

  /* TODO: AND, OR, XOR have n-ary variants */

  private static int getResultSize(Kind op, Expression a,
      Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    
    BitVectorType aType = a.asBitVector().getType();
    BitVectorType bType = b.asBitVector().getType();
    
    switch (op) {
    case BV_AND:
    case MINUS:
    case BV_NAND:
    case BV_NOR:
    case BV_OR:
    case PLUS:
    case DIVIDE:
    case SDIVIDE:
    case BV_XNOR:
    case BV_XOR:
      return Math.max(aType.getSize(), bType.getSize());

    case BV_LSHIFT: 
    case BV_RSHIFT:
      return aType.getSize();
      
    case BV_CONCAT:
      return aType.getSize() + bType.getSize();

    case MULT:
      return (2 * Math.max(aType.getSize(), bType.getSize()));
      
    case REM:
    case SREM:
      return bType.getSize();
    default:
      assert false;
      return 0;
    }
  }

  static BitVectorExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_AND, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVAND((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkBinary(ExpressionManagerImpl exprManager,
      Kind kind, BinaryConstructionStrategy strategy,
      Expression a, Expression b) {
    BitVectorExpressionImpl expr;
    try {
      expr = new BitVectorExpressionImpl(exprManager, kind,
          strategy, a, b);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
    expr.setTypeForKind(kind, a, b);
    return expr;
  }

  static BitVectorExpressionImpl mkConcat(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_CONCAT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkConcat((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, int value) {
  	Preconditions.checkArgument(size >= 0);
    try {
    	String decimalRep = Integer.toString(value);
      return cache.get(exprManager).get(Pair.of(decimalRep, size));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, long value) {
  	Preconditions.checkArgument(size >= 0);
    try {
    	String decimalRep = Long.toString(value);
      return cache.get(exprManager).get(Pair.of(decimalRep, size));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, BigInteger value) {
  	Preconditions.checkArgument(size >= 0);
    try {
    	String decimalRep = value.toString();
      return cache.get(exprManager).get(Pair.of(decimalRep, size));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }

  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int c) {
    try {
    	String decimalRep = Integer.toString(c);
      return cache.get(exprManager).get(Pair.of(decimalRep, decimalRep.length()));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      long c) {
    try {
    	String decimalRep = Long.toString(c);
      return cache.get(exprManager).get(Pair.of(decimalRep, decimalRep.length()));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      BigInteger c) {
    try {
      return cache.get(exprManager).get(Pair.of(c.toString(), c.bitLength()));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      String binaryRep) {
    try {
      return cache.get(exprManager).get(Pair.of(binaryRep, binaryRep.length()));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  /** TODO: merge with caching versions above. All constants go through Rational? 
   * @throws Z3Exception */
/*  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager, Rational rat, long len) {
    Preconditions.checkArgument(rat.isIntegral());
    return new BitVectorExpressionImpl(exprManager, rat, len);
  }*/

  static BitVectorExpressionImpl mkZeroExtend(ExpressionManagerImpl exprManager,
      final int size, Expression arg) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(size >= arg.asBitVector().getSize());
    
    if (arg.asBitVector().getSize() == size) {
      return valueOf(exprManager,arg);
    } else {
      final int argSize = arg.asBitVector().getSize();
      BitVectorExpressionImpl expr;
      try {
        expr = new BitVectorExpressionImpl(exprManager,
            BV_ZERO_EXTEND, new UnaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr arg) throws Z3Exception {
            return ctx.MkZeroExt(size-argSize, (BitVecExpr) arg);
          }
        }, arg);
      } catch (Z3Exception e) {
        throw new TheoremProverException(e);
      }
      expr.setType(expr.getExpressionManager().bitVectorType(size));
      return expr;
    }
  }
  
  static BitVectorExpressionImpl mkExtract(ExpressionManagerImpl exprManager,
      Expression arg, final int high, final int low) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(0 <= low);
    Preconditions.checkArgument(low <= high);
    Preconditions.checkArgument(high < arg.asBitVector().getSize());

    BitVectorExpressionImpl expr;
    try {
      expr = new BitVectorExpressionImpl(exprManager, BV_EXTRACT,
          new UnaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr arg) throws Z3Exception {
          return ctx.MkExtract(high, low, (BitVecExpr) arg);
        }
      }, arg);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }

    int size = high - low + 1;
    expr.setType(expr.getExpressionManager().bitVectorType(size));
    return expr;
  }

  static BitVectorExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, MINUS, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSub((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    BitVectorExpressionImpl expr;
    try {
      expr = new BitVectorExpressionImpl(exprManager, MULT, 
            new BinaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
          return ctx.MkBVMul((BitVecExpr) left, (BitVecExpr) right);
        }
      }, a, b);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
    expr.setType(expr.getExpressionManager().bitVectorType(size));
    return expr;
  }
  
  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    Preconditions.checkArgument(Iterables.all(args, new Predicate<Expression>(){
      @Override 
      public boolean apply(Expression arg) {
        return arg.isBitVector();
      }  
    }));
    BitVectorExpressionImpl expr;
    try {
      expr = new BitVectorExpressionImpl(exprManager, MULT,
            new NaryConstructionStrategy() {
              @Override
              public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
                BitVecExpr result = null;
                for(Expr arg : args) {
                  BitVecExpr bvArg = (BitVecExpr) arg;
                  int argSize = bvArg.SortSize();
                  if( argSize < size ) {
                    bvArg = ctx.MkZeroExt(size, bvArg);
                  } else if ( argSize > size ) {
                    bvArg = ctx.MkExtract(size-1, 0, bvArg);
                  }
                  if (result == null) {
                    result = bvArg;
                  } else {
                    result = ctx.MkBVMul(result, bvArg);
                  }
                }
                return result;
              }
            }, args);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
    expr.setType(expr.getExpressionManager().bitVectorType(size));
    return expr;
  }
  
  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Expression first,
      Expression... rest) {
    Preconditions.checkArgument(first.isBitVector());
    for(Expression restElem : rest)
      Preconditions.checkArgument(restElem.isBitVector());
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, MULT,
          new NaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
          Expr result = null;
          for(Expr arg : args) {
            int argSize = ((BitVecExpr) arg).SortSize();
            if( argSize < size ) {
              arg = ctx.MkZeroExt(size, (BitVecExpr) arg);
            } else if ( argSize > size ) {
              arg = ctx.MkExtract(size-1, 0, (BitVecExpr) arg);
            }
            if (result == null) {
              result = arg;
            } else {
              result = ctx.MkBVMul((BitVecExpr) result, (BitVecExpr) arg);
            }
            }
          return result;
        }
      }, first, rest);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }
  
  static BitVectorExpressionImpl mkSDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, SDIVIDE, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSDiv((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, DIVIDE, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVUDiv((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkSRem(ExpressionManagerImpl exprManager, 
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, SREM, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSRem((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkRem(ExpressionManagerImpl exprManager, 
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, REM, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVURem((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkNand(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_NAND, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVNAND((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkNor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_NOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVNOR((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkNot(ExpressionManagerImpl exprManager,
      Expression a) {
    Preconditions.checkArgument(a.isBitVector());
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, BV_NOT,
          new UnaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr arg) throws Z3Exception {
          return ctx.MkBVNot((BitVecExpr) arg);
        }
      }, a);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(a.getType());
    return e;
  }

  static BitVectorExpressionImpl mkOr(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_OR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVOR((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    Preconditions.checkArgument(Iterables.all(args, new Predicate<Expression>(){
      @Override 
      public boolean apply(Expression arg) {
        return arg.isBitVector();
      }  
    }));
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, PLUS,
          new NaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
          Expr result = null;
          for(Expr arg : args) {
            int argSize = ((BitVecExpr) arg).SortSize();
            if ( argSize < size ) {
            	arg = ctx.MkZeroExt((size-argSize), (BitVecExpr) arg);
            } else if ( argSize > size ) {
            	arg = ctx.MkExtract(size-1, 0, (BitVecExpr) arg);
            }
            if (result == null) {
              result = arg;
            } else {
              result = ctx.MkBVAdd((BitVecExpr) result, (BitVecExpr) arg); 
            }
          }
          return result;
        }
      }, args);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkSignExtend(ExpressionManagerImpl exprManager,
      final int size, Expression arg) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(size >= arg.asBitVector().getSize());
    
    if (arg.asBitVector().getSize() == size) {
      return valueOf(exprManager,arg);
    } else {
      final int argSize = arg.asBitVector().getSize();
      BitVectorExpressionImpl expr;
      try {
        expr = new BitVectorExpressionImpl(exprManager,
            BV_SIGN_EXTEND, new UnaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr arg) throws Z3Exception {
            return ctx.MkSignExt(size-argSize, (BitVecExpr) arg);
          }
        }, arg);
      } catch (Z3Exception e) {
        throw new TheoremProverException(e);
      }
      expr.setType(expr.getExpressionManager().bitVectorType(size));
      return expr;
    }
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, PLUS, 
            new BinaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
            int leftSize = ((BitVecExpr) left).SortSize();
            
            if( leftSize < size ) {
              left = ctx.MkZeroExt((size-leftSize), (BitVecExpr) left);
            } else if ( leftSize > size ) {
              left = ctx.MkExtract(size-1, 0, (BitVecExpr) left);
            }
            assert(((BitVecExpr) left).SortSize() == size);
           
            int rightSize = ((BitVecExpr) right).SortSize();
            if( rightSize < size ) {
              right = ctx.MkZeroExt((size-rightSize), (BitVecExpr) right);
            } else if ( rightSize > size ) {
              right = ctx.MkExtract(size-1, 0, (BitVecExpr) right);
            }
            
            return ctx.MkBVAdd((BitVecExpr) left, (BitVecExpr) right);
          }
        }, a, b);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Expression first, Expression... rest) {
    Preconditions.checkArgument(first.isBitVector());
    for(Expression restElem : rest)
      Preconditions.checkArgument(restElem.isBitVector());
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, PLUS,
          new NaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr[] args) throws Z3Exception {
          Expr result = null;
          for(Expr arg : args) {
            int argSize = ((BitVecExpr) arg).SortSize();
            if( argSize < size ) {
              arg = ctx.MkZeroExt((size - argSize), (BitVecExpr) arg);
            } else if ( argSize > size ) {
              arg = ctx.MkExtract(size-1, 0, (BitVecExpr) arg);
            }
            if (result == null) {
              result = arg;
            } else {
              result = ctx.MkBVAdd((BitVecExpr) result, (BitVecExpr) arg);
            }
          }
          return result;
        }
      }, first, rest);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
    Preconditions.checkArgument(a.isBitVector());
    BitVectorExpressionImpl e;
    try {
      e = new BitVectorExpressionImpl(exprManager, UNARY_MINUS,
          new UnaryConstructionStrategy() {
        @Override
        public Expr apply(Context ctx, Expr arg) throws Z3Exception {
          return ctx.MkBVNeg((BitVecExpr) arg);
        }
      }, a);
    } catch (Z3Exception e1) {
      throw new TheoremProverException(e1);
    }
    e.setType(a.getType());
    return e;
  }

  static BitVectorExpressionImpl mkXnor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_XNOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVXNOR((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkXor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_XOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVXOR((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkLShift(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_LSHIFT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVSHL((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkRShift(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    Preconditions.checkArgument(a.isBitVector());
    Preconditions.checkArgument(b.isBitVector());
    return mkBinary(exprManager, BV_RSHIFT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) throws Z3Exception {
        return ctx.MkBVLSHR((BitVecExpr) left, (BitVecExpr) right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl valueOf(ExpressionManagerImpl exprManager, Expression e) {
    if( exprManager.equals( e.getExpressionManager() ) ) {
      if (e instanceof BitVectorExpressionImpl) {
        return (BitVectorExpressionImpl) e;
      } else if (e instanceof ExpressionImpl) {
        return new BitVectorExpressionImpl((ExpressionImpl) e);
      }
    }
    
    switch( e.getKind() ) {
    default:
      throw new UnsupportedOperationException();
    }
  }

  private BitVectorExpressionImpl(ExpressionImpl bv) {
    super(bv);
  }
  
  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Expression e) {
    super(exprManager, e);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, final String decimalRep, final int len) throws Z3Exception {
    super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx) throws Z3Exception {
        return ctx.MkBV(decimalRep, len);
      }
    });

    setConstant(true);
    setType(BitVectorTypeImpl.create(exprManager, len));
  }
  
  private BitVectorExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, BitVectorType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  protected static BitVectorExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isBitVectorType());
    return new BitVectorExpressionImpl(em, kind, expr, type.asBitVectorType(), children);
  }
  
//  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, final long val, final int len) {
//    super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
//      @Override
//      public Expr apply(Context ctx) throws Z3Exception {
//        return ctx.MkBV(val, len);
//      }
//    });
//
//    setConstant(true);
//    setType(BitVectorTypeImpl.create(exprManager, len));
//  }
  
  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression a,
      Expression b) throws Z3Exception {
    super(exprManager, kind, strategy, a, b);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy, Expression first,
      Expression[] rest) throws Z3Exception {
    super(exprManager, kind, strategy, first, rest);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression a) throws Z3Exception {
    super(exprManager, kind, strategy, a);
    setType(a.getType());
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy,
      Iterable<? extends Expression> args) throws Z3Exception {
    super(exprManager, kind, strategy, args);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      TernaryConstructionStrategy strategy,
      Expression arg1, Expression arg2, Expression arg3) throws Z3Exception {
    super(exprManager, kind, strategy, arg1, arg2, arg3);
  }

  @Override
  public BitVectorExpressionImpl and(Expression a) {
    return mkAnd(getExpressionManager(), this, a);

  }

  @Override
  public BitVectorExpressionImpl concat(Expression a) {
    return mkConcat(getExpressionManager(), this, a);

  }

  @Override
  public BitVectorExpressionImpl extract(int i, int j) {
    return mkExtract(getExpressionManager(), this, i, j);

  }

  @Override
  public int getSize() {
    return getType().getSize();
  }

  @Override
  public BitVectorType getType() {
    return super.getType().asBitVectorType();
  }
  
  @Override
  public BitVectorExpressionImpl minus(Expression a) {
    return mkMinus(getExpressionManager(), this, a);

  }

  @Override
  public BitVectorExpressionImpl nand(Expression a) {
    return mkNand(getExpressionManager(), this, a);

  }

  @Override
  public BitVectorExpressionImpl nor(Expression a) {
    return mkNor(getExpressionManager(), this, a);

  }

  @Override
  public BitVectorExpressionImpl not() {
    return mkNot(getExpressionManager(), this);
  }

  @Override
  public BitVectorExpressionImpl or(Expression a) {
    return mkOr(getExpressionManager(), this, a);
  }

  @Override
  public BitVectorExpressionImpl plus(int size, Expression a) {
    return mkPlus(getExpressionManager(), size, this, a);
  }

  @Override
  public BitVectorExpressionImpl plus(int size, Expression... args) {
    return mkPlus(getExpressionManager(), size, this, args);
  }

  @Override
  public BitVectorExpressionImpl plus(int size,
      Iterable<? extends Expression> args) {
    return mkPlus(getExpressionManager(), size, Iterables.concat(Lists
        .newArrayList(this), args));
  }

  private void setTypeForKind(Kind kind, Expression a,
      Expression b) {
    int size = getResultSize(kind, a, b);
    setType(getExpressionManager().bitVectorType(size));
  }

  @Override
  public BitVectorExpressionImpl times(int size, Expression a) {
    return mkMult(getExpressionManager(), size, this, a);
  }
  
  @Override
  public BitVectorExpressionImpl divides(Expression a) {
    return mkDivide(getExpressionManager(), this, a);
  }
  
  @Override
  public BitVectorExpressionImpl signedDivides(Expression a) {
    return mkSDivide(getExpressionManager(), this, a);
  }
  
  @Override
  public BitVectorExpressionImpl rems(Expression a) {
    return mkRem(getExpressionManager(), this, a);
  }
  
  @Override
  public BitVectorExpressionImpl signedRems(Expression a) {
    return mkSRem(getExpressionManager(), this, a);
  }

  @Override
  public BitVectorExpressionImpl xnor(Expression a) {
    return mkXnor(getExpressionManager(), this, a);
  }

  @Override
  public BitVectorExpressionImpl xor(Expression a) {
    return mkXor(getExpressionManager(), this, a);
  }

  @Override
  public BooleanExpression greaterThan(Expression e) {
    Preconditions.checkArgument(e.isBitVector());
    return getType().gt(this,e);
  }

  @Override
  public BooleanExpression greaterThanOrEqual(Expression e) {
    Preconditions.checkArgument(e.isBitVector());
    return getType().geq(this,e);
  }

  @Override
  public BooleanExpression lessThan(Expression e) {
    Preconditions.checkArgument(e.isBitVector());
    return getType().lt(this,e);
  }

  @Override
  public BooleanExpression lessThanOrEqual(Expression e) {
    Preconditions.checkArgument(e.isBitVector());
    return getType().leq(this,e);
  }
  
  @Override
  public BitVectorExpressionImpl lshift(Expression a) {
    Preconditions.checkArgument(a.isInteger() || a.isBitVector());
    return mkLShift(getExpressionManager(), this, a);
  }
  
  @Override
  public BitVectorExpressionImpl rshift(Expression a) {
    Preconditions.checkArgument(a.isInteger() || a.isBitVector());
    return mkRShift(getExpressionManager(), this, a);
  }
  
  @Override
  public BitVectorExpressionImpl zeroExtend(int size) {
    return mkZeroExtend(getExpressionManager(), size, this);
  }
  
  @Override
  public BitVectorExpressionImpl signExtend(int size) {
    return mkSignExtend(getExpressionManager(), size, this);
  }
  
  @Override
  public BitVectorExpressionImpl uminus() {
  	return mkUminus(getExpressionManager(), this);
  }
}
