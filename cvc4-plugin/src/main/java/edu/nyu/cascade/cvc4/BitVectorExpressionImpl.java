package edu.nyu.cascade.cvc4;

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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.math.BigInteger;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ComputationException;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.BitVector;
import edu.nyu.acsys.CVC4.BitVectorExtract;
import edu.nyu.acsys.CVC4.BitVectorSize;
import edu.nyu.acsys.CVC4.BitVectorZeroExtend;
import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.util.CacheException;

public class BitVectorExpressionImpl extends ExpressionImpl implements
    BitVectorExpression {
    private static final LoadingCache<ExpressionManagerImpl, LoadingCache<String, BitVectorExpressionImpl>> constantCache = CacheBuilder
        .newBuilder().build(
            new CacheLoader<ExpressionManagerImpl, LoadingCache<String, BitVectorExpressionImpl>>(){
              public LoadingCache<String, BitVectorExpressionImpl> load(final ExpressionManagerImpl exprManager) {
                    return CacheBuilder.newBuilder().build(new CacheLoader<String, BitVectorExpressionImpl>(){
                      public BitVectorExpressionImpl load(String binaryRep) {
                        try {
                          return new BitVectorExpressionImpl(exprManager, binaryRep);
                        } catch (TheoremProverException e) {
                          throw new ComputationException(e);
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
    return mkBinary(exprManager, BV_AND, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_AND, left, right);
      }
    }, a, b);
  }

  private static BitVectorExpressionImpl mkBinary(ExpressionManagerImpl exprManager,
      Kind kind, BinaryConstructionStrategy strategy,
      Expression a, Expression b) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, kind,
        strategy, a, b);
    e.setTypeForKind(kind, a, b);
    return e;
  }
  
/*  private static BitVectorExpressionImpl mkBinary(ExpressionManagerImpl exprManager,
	      Kind kind, int size, BinaryConstructionStrategy strategy,
	      Expression a, Expression b) {
	    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, kind,
	        strategy, a, b);
	    e.setType(e.getExpressionManager().bitVectorType(size));
	    return e;
  } */

  static BitVectorExpressionImpl mkConcat(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_CONCAT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_CONCAT, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, int value) {
  	Preconditions.checkArgument(size > 0);
    String binary = Integer.toBinaryString(value);
    int repSize = binary.length();
    
    if (repSize < size) { /* Sign-extend the value */
      int prefix_length = (int) (size - repSize);
      char[] prefix = new char[prefix_length];
      Arrays.fill(prefix, value >= 0 ? '0' : '1');
      binary = String.valueOf(prefix) + binary;
    } else if (repSize > size) { /* truncate */
      binary = binary.substring((int) (repSize - size), repSize);
    }

    assert (binary.length() == size);
    try {
      return constantCache.get(exprManager).get(binary);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, long value) {
  	Preconditions.checkArgument(size > 0);
    String binary = Long.toBinaryString(value);
    int repSize = binary.length();
    
    if (repSize < size) { /* Sign-extend the value */
      int prefix_length = (int) (size - repSize);
      char[] prefix = new char[prefix_length];
      Arrays.fill(prefix, value >= 0 ? '0' : '1');
      binary = String.valueOf(prefix) + binary;
    } else if (repSize > size) { /* truncate */
      binary = binary.substring((int) (repSize - size), repSize);
    }

    assert (binary.length() == size);
    try {
      return constantCache.get(exprManager).get(binary);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int size, BigInteger value) {
  	Preconditions.checkArgument(size > 0);
    int repSize = value.bitLength();
    String binary = value.toString(2);
    if (repSize < size) { /* Sign-extend the value */
      int prefix_length = (int) (size - repSize);
      char[] prefix = new char[prefix_length];
      Arrays.fill(prefix, value.compareTo(BigInteger.ZERO) >= 0 ? '0' : '1');
      binary = String.valueOf(prefix) + binary;
    } else if (repSize > size) { /* truncate */
      binary = binary.substring((int) (repSize - size), repSize);
    }

    assert (binary.length() == size);
    try {
      return constantCache.get(exprManager).get(binary);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      int c) {
    try {
    	String binaryString = Integer.toBinaryString(c);
      return constantCache.get(exprManager).get(binaryString);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      long c) {
    try {
    	String binaryString = Long.toBinaryString(c);
      return constantCache.get(exprManager).get(binaryString);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }

  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      BigInteger c) {
    try {
    	String binaryString = c.toString(2);
      return constantCache.get(exprManager).get(binaryString);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager,
      String rep) {
    try {
      return constantCache.get(exprManager).get(rep);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  /** TODO: merge with caching versions above. All constants go through Rational? */
/*  static BitVectorExpressionImpl mkConstant(ExpressionManagerImpl exprManager, Rational rat, long len) {
    Preconditions.checkArgument(rat.isIntegral());
    return new BitVectorExpressionImpl(exprManager, rat, len);
  }*/

  static BitVectorExpressionImpl mkExtract(ExpressionManagerImpl exprManager,
      Expression arg, final int high, final int low) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(0 <= low);
    Preconditions.checkArgument(low <= high);
    Preconditions.checkArgument(high < arg.asBitVector().getSize());

    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, BV_EXTRACT,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg) throws Exception {
            Expr extractor = em.mkConst(new BitVectorExtract(high, low));
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_EXTRACT, extractor, arg);
          }
        }, arg);

    int size = high - low + 1;
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, MINUS, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SUB, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Expression a,
      Expression b) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, MULT, 
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
    	  return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT, left, right);
      }
    }, a, b);
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }
  
  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args) {
            Expr result = null;
            for(Expr arg : args) {
              edu.nyu.acsys.CVC4.BitVectorType bvType = 
                  new edu.nyu.acsys.CVC4.BitVectorType(arg.getType());
              int argSize = (int) bvType.getSize();
              if( argSize < size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-argSize)), arg);
              } else if ( argSize > size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), arg);
              }
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT, result, arg);
              }
            }
            return result;
          }
        }, args);
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }
  
  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      final int size, Expression first,
      Expression... rest) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args) {
            Expr result = null;
            for(Expr arg : args) {
              edu.nyu.acsys.CVC4.BitVectorType bvType = 
                  new edu.nyu.acsys.CVC4.BitVectorType(arg.getType());
              int argSize = (int) bvType.getSize();
              if( argSize < size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-argSize)), arg);
              } else if ( argSize > size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), arg);
              }
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT, result, arg);
              }
            }
            return result;
          }
        }, first, rest);
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }
  
  static BitVectorExpressionImpl mkSDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, SDIVIDE, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SDIV, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, DIVIDE, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_UDIV, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkSRem(ExpressionManagerImpl exprManager, 
      Expression a, Expression b) {
    return mkBinary(exprManager, SREM, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SREM, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkRem(ExpressionManagerImpl exprManager, 
      Expression a, Expression b) {
    return mkBinary(exprManager, REM, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_UREM, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkNand(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_NAND, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NAND, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkNor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_NOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NOR, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkNot(ExpressionManagerImpl exprManager,
      Expression a) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, BV_NOT,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NEG, arg);
          }
        }, a);
    e.setType(a.getType());
    return e;
  }

  static BitVectorExpressionImpl mkOr(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_OR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_OR, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args) {
            Expr result = null;
            for(Expr arg : args) {
              edu.nyu.acsys.CVC4.BitVectorType bvType = 
                  new edu.nyu.acsys.CVC4.BitVectorType(arg.getType());
              int argSize = (int) bvType.getSize();
              if( argSize < size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-argSize)), arg);
              } else if ( argSize > size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), arg);
              }
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS, result, arg);
              }
            }
            return result;
          }
        }, args);
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
      BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager,
          BV_SIGN_EXTEND, new UnaryConstructionStrategy() {
            @Override
            public Expr apply(ExprManager em, Expr arg) {
              Expr sizeExpr = em.mkConst(new BitVectorSize(size));
              return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SIGN_EXTEND,
                  sizeExpr, arg);
            }
          }, arg);
      e.setType(e.getExpressionManager().bitVectorType(size));
      return e;
    }
  }
  
  static BitVectorExpressionImpl mkZeroExtend(ExpressionManagerImpl exprManager,
      final int size, Expression arg) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(size >= arg.asBitVector().getSize());
    
    if (arg.asBitVector().getSize() == size) {
      return valueOf(exprManager,arg);
    } else {
      BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager,
          BV_ZERO_EXTEND, new UnaryConstructionStrategy() {
            @Override
            public Expr apply(ExprManager em, Expr arg) {
              Expr sizeExpr = em.mkConst(new BitVectorSize(size));
              return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SIGN_EXTEND,
                  sizeExpr, arg);
            }
          }, arg);
      e.setType(e.getExpressionManager().bitVectorType(size));
      return e;
    }
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Expression a,
      Expression b) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, PLUS, 
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        edu.nyu.acsys.CVC4.BitVectorType leftType = 
            new edu.nyu.acsys.CVC4.BitVectorType(left.getType());
        int leftSize = (int) leftType.getSize();
        
        if( leftSize < size ) {
          left = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-leftSize)), left);
        } else if ( leftSize > size ) {
          left = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), left);
        }
        edu.nyu.acsys.CVC4.BitVectorType rightType =
            new edu.nyu.acsys.CVC4.BitVectorType(right.getType());
        int rightSize = (int) rightType.getSize();
        if( rightSize < size ) {
          right = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-rightSize)), right);
        } else if ( leftSize > size ) {
          right = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), right);
        }
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS, left, right);
      }
    }, a, b);
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      final int size, Expression first,
      Expression... rest) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args) {
            Expr result = null;
            for(Expr arg : args) {
              edu.nyu.acsys.CVC4.BitVectorType bvType = 
                  new edu.nyu.acsys.CVC4.BitVectorType(arg.getType());
              int argSize = (int) bvType.getSize();
              if( argSize < size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorZeroExtend(size-argSize)), arg);
              } else if ( argSize > size ) {
                arg = em.mkExpr(em.mkConst(new BitVectorExtract(size-1, 0)), arg);
              }
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS, result, arg);
              }
            }
            return result;
          }
        }, first, rest);
    e.setType(e.getExpressionManager().bitVectorType(size));
    return e;
  }

  static BitVectorExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
    BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, UNARY_MINUS,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NEG, arg);
          }
        }, a);
    e.setType(a.getType());
    return e;
  }

  static BitVectorExpressionImpl mkXnor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_XNOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_XNOR, left, right);
      }
    }, a, b);
  }

  static BitVectorExpressionImpl mkXor(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_XOR, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_XOR, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkLShift(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_LSHIFT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SHL, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkRShift(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_RSHIFT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_LSHR, left, right);
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

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, final String rep) {
    super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em) {
        return em.mkConst(new BitVector(rep));
      }
    });

    setConstant(true);
    int size = rep.length();
    setType(BitVectorTypeImpl.create(exprManager, size));
  }

/*  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, final Rational rat, final long len) {
    super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em) {
        assert(rat.isIntegral());
        return em.mkConst(new BitVector(len, rat.floor()));
      }
    });

    setConstant(true);
    int size = len;
    setType(BitVectorTypeImpl.create(exprManager, size));
  }*/
  
  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, final long val, final int len) {
    super(exprManager, CONSTANT, new NullaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em) {
        return em.mkConst(new BitVector(len, val));
      }
    });

    setConstant(true);
    setType(BitVectorTypeImpl.create(exprManager, len));
  }
  
  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression a,
      Expression b) {
    super(exprManager, kind, strategy, a, b);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy, Expression first,
      Expression[] rest) {
    super(exprManager, kind, strategy, first, rest);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression a) {
    super(exprManager, kind, strategy, a);
    setType(a.getType());
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy,
      Iterable<? extends Expression> args) {
    super(exprManager, kind, strategy, args);
  }

  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      TernaryConstructionStrategy strategy,
      Expression arg1, Expression arg2, Expression arg3) {
    super(exprManager, kind, strategy, arg1, arg2, arg3);
  }
  
  private BitVectorExpressionImpl(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, BitVectorType type, Iterable<? extends ExpressionImpl> children) {
    super(exprManager, kind, expr, type);
  }
  
  protected static BitVectorExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
      Expr expr, BitVectorType type, Iterable<? extends ExpressionImpl> children) {
  	return new BitVectorExpressionImpl(exprManager, kind, expr, type, children);
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
  public BitVectorExpression zeroExtend(int size) {
    return mkZeroExtend(getExpressionManager(), size, this);
  }

  @Override
  public BitVectorExpression signExtend(int size) {
    return mkSignExtend(getExpressionManager(), size, this);
  }
  
  @Override
  public BitVectorExpression uminus() {
    return mkUminus(getExpressionManager(), this);
  }
}
