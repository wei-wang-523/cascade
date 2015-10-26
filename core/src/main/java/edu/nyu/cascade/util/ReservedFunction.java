package edu.nyu.cascade.util;

import xtc.type.BooleanT;
import xtc.type.IntegerT;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.type.VoidT;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;

/**
 * Reserved function names in Cascade
 * @author Wei
 *
 */
public class ReservedFunction {
  public static final String MALLOC = "malloc";
  public static final String CALLOC = "calloc";
  public static final String FREE = "free";
  public static final String EXIT = "exit";
  public static final String ABORT = "abort";
	public static final String ALLOCA = "alloca";
  public static final String MEMSET = "memset";
  public static final String MEMCOPY = "memcpy";
  public static final String BUILTIN_ALLOCA = "__builtin_alloca";
	
//  public static final String AUX_HAVOC = "havoc";
  
  public static final String ANNO_ASSERT = "ASSERT";
  public static final String ANNO_ASSUME = "ASSUME";
  public static final String ANNO_INVARIANT = "INVARIANT";
  
  public static final String VERIFIER_ASSUME = "__VERIFIER_assume";
  public static final String VERIFIER_nondet_int = "__VERIFIER_nondet_int";
  public static final String VERIFIER_nondet_pointer = "__VERIFIER_nondet_pointer";
  
  public static final String FUN_VALID_ACCESS = "valid";
  public static final String FUN_VALID_MALLOC = "valid_malloc";
  public static final String FUN_VALID_FREE = "valid_free";
  public static final String FUN_IMPLIES = "implies";
  public static final String FUN_FORALL = "forall";
  public static final String FUN_EXISTS = "exists";
  
  public static class Sig {
  	private final Type returnType;
  	private final Type[] argTypes;
  	
  	Sig(Type returnType, Type... argTypes) {
  		this.returnType = returnType;
  		this.argTypes = argTypes;
  	}
  	
  	static Sig of(Type returnType, Type... argTypes) {
  		return new Sig(returnType, argTypes);
  	}

  	public Type getReturnType() {
			return returnType;
		}

  	public Type[] getArgTypes() {
			return argTypes;
		}
  }
  
  public static boolean isReserved(String funcName) {
  	return FuncSignatures.containsKey(funcName);
  }
  
  public static Sig getSignature(String funcName) {
  	Preconditions.checkArgument(isReserved(funcName));
  	return FuncSignatures.get(funcName);
  }
  
  private final static ImmutableMap<String, Sig> FuncSignatures
  	= new ImmutableMap.Builder<String, Sig>()
  	.put(MEMSET, 
  			Sig.of(PointerT.TO_VOID, PointerT.TO_VOID, IntegerT.CHAR, NumberT.U_LONG))
  	.put(MEMCOPY, 
  			Sig.of(PointerT.TO_VOID, PointerT.TO_VOID, PointerT.TO_VOID, NumberT.U_LONG))		
  	.put(MALLOC, 
  			Sig.of(PointerT.TO_VOID, NumberT.U_LONG))
  	.put(CALLOC, 
  			Sig.of(PointerT.TO_VOID, NumberT.LONG, NumberT.U_LONG))
  	.put(ALLOCA, 
  			Sig.of(PointerT.TO_VOID, NumberT.U_LONG))
  	.put(BUILTIN_ALLOCA, 
  			Sig.of(PointerT.TO_VOID, NumberT.U_LONG)) 		
  	.put(FREE, 
  			Sig.of(VoidT.TYPE, PointerT.TO_VOID))
  	.put(EXIT, 
  			Sig.of(VoidT.TYPE))
  	.put(ANNO_ASSERT,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE))
  	.put(ANNO_ASSUME,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE))
  	.put(ANNO_INVARIANT,
  			Sig.of(VoidT.TYPE, BooleanT.TYPE))
  	.put(FUN_VALID_ACCESS,
  			Sig.of(BooleanT.TYPE, PointerT.TO_VOID))
  	.put(FUN_VALID_MALLOC,
  			Sig.of(BooleanT.TYPE, PointerT.TO_VOID, NumberT.LONG))
  	.put(FUN_VALID_FREE,
  			Sig.of(BooleanT.TYPE, PointerT.TO_VOID))
  	.put(FUN_IMPLIES,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE, BooleanT.TYPE))
  	//FIXME: bound variables are arg types or not?
  	.put(FUN_FORALL,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE))
  	.put(FUN_EXISTS,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE))
  	.put(VERIFIER_ASSUME,
  			Sig.of(BooleanT.TYPE, BooleanT.TYPE))
  	.put(VERIFIER_nondet_int,
  			Sig.of(VoidT.TYPE, NumberT.INT))
  	.put(VERIFIER_nondet_pointer,
  			Sig.of(VoidT.TYPE, PointerT.TO_VOID))  			
  	.build();
}
