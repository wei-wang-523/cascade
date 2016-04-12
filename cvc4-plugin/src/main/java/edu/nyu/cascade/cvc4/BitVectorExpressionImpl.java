package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.BV_AND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_CONCAT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_EXTRACT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NAND;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOR;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NOT;
import static edu.nyu.cascade.prover.Expression.Kind.BV_NEG;
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
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.math.BigInteger;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ComputationException;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.BitVector;
import edu.nyu.acsys.CVC4.BitVectorExtract;
import edu.nyu.acsys.CVC4.BitVectorSignExtend;
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

final class BitVectorExpressionImpl extends ExpressionImpl implements
    BitVectorExpression {
	static final LoadingCache<ExpressionManagerImpl, LoadingCache<String, BitVectorExpressionImpl>> constantCache = CacheBuilder
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
    int repSize = value.bitLength(); // bit-length of 0 would be 0 (treat 0 as sign bit)
    String binary = value.toString(2);
    if (repSize < size) { /* Sign-extend the value */
      int prefix_length = (int) (size - repSize);
      char[] prefix = new char[prefix_length];
      Arrays.fill(prefix, value.compareTo(BigInteger.ZERO) >= 0 ? '0' : '1');
      binary = repSize == 0 ? String.valueOf(prefix) : String.valueOf(prefix) + binary;
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
      int size, edu.nyu.acsys.CVC4.Integer cvc4Int) {
  	Preconditions.checkArgument(size > 0);
  	String binary = cvc4Int.toString(2);
    int repSize = binary.length();
    if (repSize < size) { /* Sign-extend the value */
      int prefix_length = (int) (size - repSize);
      char[] prefix = new char[prefix_length];
      Arrays.fill(prefix, cvc4Int.sgn() >= 0 ? '0' : '1');
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
  
  /* TODO: AND, OR, XOR have n-ary variants */
	
	static BitVectorExpressionImpl mkAnd(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
	  return mkBinary(exprManager, BV_AND, new BinaryConstructionStrategy() {
	    @Override
	    public Expr apply(ExprManager em, Expr left, Expr right) {
	      return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_AND, left, right);
	    }
	  }, a, b);
	}

	static BitVectorExpressionImpl mkConcat(ExpressionManagerImpl exprManager,
	    Expression a, Expression b) {
	  return mkBinary(exprManager, BV_CONCAT, new BinaryConstructionStrategy() {
	    @Override
	    public Expr apply(ExprManager em, Expr left, Expr right) {
	      return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_CONCAT, left, right);
	    }
	  }, a, b);
	}

  static BitVectorExpressionImpl mkExtract(ExpressionManagerImpl exprManager,
      Expression arg, final int high, final int low) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(0 <= low);
    Preconditions.checkArgument(low <= high);
    Preconditions.checkArgument(high < arg.asBitVector().getSize());

    int size = high - low + 1;
    
    return mkUnary(exprManager, BV_EXTRACT, new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg) throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_EXTRACT, 
            		em.mkConst(new BitVectorExtract(high, low)), arg);
          }
    }, arg, size);
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

  static BitVectorExpressionImpl mkMult(final ExpressionManagerImpl exprManager,
      Expression a, Expression b) {  	
  	return mkBinary(exprManager, MULT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
    	  return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT, left, right);
      }
    }, a, b);
  }
  
  static BitVectorExpressionImpl mkMult(final ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    return mkNary(exprManager, PLUS,
    		new NaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, List<Expr> args) {
    		Expr result = null;
    		for(Expr arg : args) {
    			if (result == null) {
    				result = arg;
    			} else {
    				result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_MULT, result, arg);
    			}
    		}
    		return result;
    	}
    }, args);
  }
  
  static BitVectorExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Expression first, Expression... rest) {
    return mkMult(exprManager, Lists.asList(first, rest));
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
  	int size = a.asBitVector().getSize();
    return mkUnary(exprManager, BV_NOT, new UnaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, Expr arg) {
    		return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NOT, arg);
    	}
    }, a, size);
  }
  
  static BitVectorExpressionImpl mkNegate(ExpressionManagerImpl exprManager,
      Expression a) {
  	int size = a.asBitVector().getSize();
    return mkUnary(exprManager, BV_NEG, new UnaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, Expr arg) {
    		return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NEG, arg);
    	}
    }, a, size);
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

  static BitVectorExpressionImpl mkSignExtend(ExpressionManagerImpl exprManager,
  		int size, Expression arg) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(size >= arg.asBitVector().getSize());
    
    int argSize = arg.asBitVector().getSize() ;
    
    if (argSize == size) return valueOf(exprManager,arg);
    
    final int extend_size = size - argSize;
    
    return mkUnary(exprManager,
    		BV_SIGN_EXTEND, new UnaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, Expr arg) {
    		return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_SIGN_EXTEND,
    				em.mkConst(new BitVectorSignExtend(extend_size)), arg);
    	}
    }, arg, size);
  }
  
  static BitVectorExpressionImpl mkZeroExtend(ExpressionManagerImpl exprManager,
  		int size, Expression arg) {
    Preconditions.checkArgument(arg.isBitVector());
    Preconditions.checkArgument(size >= arg.asBitVector().getSize());
    
    int argSize = arg.asBitVector().getSize() ;
    
    if (argSize == size) return valueOf(exprManager,arg);
    
    final int extend_size = size - arg.asBitVector().getSize();
    return mkUnary(exprManager, BV_ZERO_EXTEND, new UnaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, Expr arg) {
    		return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_ZERO_EXTEND,
    				em.mkConst(new BitVectorZeroExtend(extend_size)), arg);
    	}
    }, arg, size);
  }

  static BitVectorExpressionImpl mkPlus(final ExpressionManagerImpl exprManager,
  		Expression a, Expression b) {
  	return mkBinary(exprManager, PLUS, new BinaryConstructionStrategy() {
    	@Override
    	public Expr apply(ExprManager em, Expr left, Expr right) {
    		return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS, left, right);
    	}
    }, a, b);
  }

  static BitVectorExpressionImpl mkPlus(final ExpressionManagerImpl exprManager,
			Iterable<? extends Expression> args) {
	  Preconditions.checkArgument(!Iterables.isEmpty(args));
	  
	  return mkNary(exprManager, PLUS, new NaryConstructionStrategy() {
	  	@Override
	  	public Expr apply(ExprManager em, List<Expr> args) {
	  		Expr result = null;
	  		for(Expr arg : args) {
	  			if (result == null) {
	  				result = arg;
	  			} else {
	  				result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_PLUS, result, arg);
	  			}
	  		}
	  		return result;
	  	}
	  }, args);
	}

	static BitVectorExpressionImpl mkPlus(final ExpressionManagerImpl exprManager,
  		Expression first, Expression... rest) {
  	return mkPlus(exprManager, Lists.asList(first, rest));
  }

  static BitVectorExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
  	int size = a.asBitVector().getSize();
  	
  	return mkUnary(exprManager, UNARY_MINUS, new UnaryConstructionStrategy() {
  		@Override
  		public Expr apply(ExprManager em, Expr arg) {
  			return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_NEG, arg);
  		}
  	}, a, size);
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
  
  static BitVectorExpressionImpl mkSRShift(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return mkBinary(exprManager, BV_RSHIFT, new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right) {
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.BITVECTOR_ASHR, left, right);
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

  /* TODO: AND, OR, XOR have n-ary variants */
	
  static BitVectorExpressionImpl typeConversion(
			ExpressionManagerImpl exprManager, int size, Expression a) {
		Preconditions.checkArgument(a.isBitVector());
		BitVectorExpression bv = a.asBitVector();
		
		int exprSize = bv.getSize();
		if(exprSize == size)	return valueOf(exprManager, bv);
		
		if(exprSize > size)   return mkExtract(exprManager, bv, size-1, 0);
		
		return mkSignExtend(exprManager, size, bv);
	}

	static BitVectorExpressionImpl create(ExpressionManagerImpl exprManager, Kind kind, 
	    Expr expr, BitVectorType type, Iterable<? extends ExpressionImpl> children) {
		return new BitVectorExpressionImpl(exprManager, kind, expr, type, children);
	}

	private static BitVectorExpressionImpl mkBinary(ExpressionManagerImpl exprManager,
	    Kind kind, BinaryConstructionStrategy strategy,
	    Expression a, Expression b) {
		
		BitVectorType aType = a.asBitVector().getType();
	  BitVectorType bType = b.asBitVector().getType();
	  int size = 0;
	  
  	Expression lhs, rhs;
  	switch(kind) {
  	case BV_AND:
	  case BV_NAND:
	  case BV_NOR:
	  case BV_OR:
	  case BV_XOR:
	  case PLUS:
	  case DIVIDE:
	  case SDIVIDE:
	  case MINUS:
	  case MULT: 
	  case REM:
	  case SREM:
	  case BV_LSHIFT: 
	  case BV_RSHIFT: {
	  	size = Math.max(aType.getSize(), bType.getSize());
	  	lhs = typeConversion(exprManager, size, a);
	  	rhs = typeConversion(exprManager, size, b);
	  	break;
	  }
	  case BV_CONCAT: {
	  	size = aType.getSize() + bType.getSize();
	  	lhs = a; rhs = b; 
	  	break;
	  }
	  default:
	    throw new IllegalArgumentException("Unknown kind " + kind);
  	}
	  BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, kind,
	      strategy, lhs, rhs);
	  e.setType(exprManager.bitVectorType(size));
	  return e;
	}

	private static BitVectorExpressionImpl mkUnary(ExpressionManagerImpl exprManager,
	    Kind kind, UnaryConstructionStrategy strategy,
	    Expression a, int size) {
	  BitVectorExpressionImpl e = new BitVectorExpressionImpl(exprManager, kind,
	      strategy, a);
	  e.setType(exprManager.bitVectorType(size));
	  return e;
	}

	private static BitVectorExpressionImpl mkNary(final ExpressionManagerImpl exprManager,
	    final Kind kind, NaryConstructionStrategy strategy, Iterable<? extends Expression> args) {
		int maxSize = 0;
		for(Expression arg : args) {
			assert arg.isBitVector();
			maxSize = Math.max(maxSize, arg.asBitVector().getSize());
		}
		
		final int size = maxSize;
		Iterable<? extends Expression> argsPrime = Iterables.transform(args, 
				new Function<Expression, Expression>(){
			@Override
			public Expression apply(Expression input) {
		  	switch(kind) {
		  	case BV_AND:
			  case BV_NAND:
			  case BV_NOR:
			  case BV_XOR:
			  case BV_OR:
			  case PLUS:
			  case MULT: {
			  	return typeConversion(exprManager, size, input);
			  }
			  default:
			    throw new IllegalArgumentException("Unknown kind " + kind);
		  	}
			}
		});
		
		BitVectorExpressionImpl expr = new BitVectorExpressionImpl(exprManager, 
				kind, strategy, argsPrime);
	  expr.setType(exprManager.bitVectorType(maxSize));
	  return expr;
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
  public BitVectorExpressionImpl neg() {
    return mkNegate(getExpressionManager(), this);
  }

  @Override
  public BitVectorExpressionImpl or(Expression a) {
    return mkOr(getExpressionManager(), this, a);
  }

  @Override
  public BitVectorExpressionImpl plus(Expression a) {
    return mkPlus(getExpressionManager(), this, a);
  }

  @Override
  public BitVectorExpressionImpl plus(Expression... args) {
    return mkPlus(getExpressionManager(), Lists.asList(this, args));
  }

  @Override
  public BitVectorExpressionImpl plus(Iterable<? extends Expression> args) {
    return mkPlus(getExpressionManager(), Iterables.concat(Collections.singletonList(this), args));
  }

  @Override
  public BitVectorExpressionImpl times(Expression a) {
    return mkMult(getExpressionManager(), this, a);
  }
  
  @Override
	public BitVectorExpression times(Expression... args) {
		return mkMult(getExpressionManager(), Lists.asList(this, args));
	}

	@Override
	public BitVectorExpression times(Iterable<? extends Expression> args) {
		return mkMult(getExpressionManager(), Iterables.concat(Collections.singletonList(this), args));
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
  public BitVectorExpressionImpl signedRshift(Expression a) {
    Preconditions.checkArgument(a.isInteger() || a.isBitVector());
    return mkSRShift(getExpressionManager(), this, a);
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
