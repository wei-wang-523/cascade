package edu.nyu.cascade.util;

import java.util.Set;

import com.google.common.collect.Sets;

public class ReservedFunction {
  public static final String MALLOC = "malloc";
  public static final String FREE = "free";
  
  public static final String AUX_HAVOC = "havoc";
  public static final String AUX_ALLOC = "alloc";
  public static final String AUX_ARRAY_ALLOC = "array_allocated";
  public static final String AUX_STRUCT_ALLOC = "struct_allocated";
  
  public static final String ANNO_NONDET = "__NONDET__";
  public static final String ANNO_ASSERT = "ASSERT";
  public static final String ANNO_ASSUME = "ASSUME";
  public static final String ANNO_INVARIANT = "INVARIANT";
  
  public static final String FUN_VALID = "valid";
  public static final String FUN_VALID_MALLOC = "valid_malloc";
  public static final String FUN_IMPLIES = "implies";
  public static final String FUN_FORALL = "forall";
  public static final String FUN_EXISTS = "exists";
  public static final String FUN_REACH = "reach";
  public static final String FUN_ALLOCATED = "allocated";
  public static final String FUN_ISROOT = "is_root";
  public static final String FUN_CREATE_ACYCLIC_LIST = "create_acyclic_list";
  public static final String FUN_CREATE_CYCLIC_LIST = "create_cyclic_list";
  public static final String FUN_CREATE_ACYCLIC_DLIST = "create_acyclic_dlist";
  public static final String FUN_CREATE_CYCLIC_DLIST = "create_cyclic_dlist";
  
  public final static Set<String> Functions = 
      Sets.newHashSet(
          MALLOC, 
          FREE, 
          
          ANNO_NONDET, 
          ANNO_ASSERT, 
          ANNO_ASSUME, 
          ANNO_INVARIANT,
          
          FUN_VALID,
          FUN_VALID_MALLOC,
          FUN_IMPLIES,
          FUN_FORALL,
          FUN_EXISTS, 
          FUN_REACH, 
          FUN_ALLOCATED, 
          FUN_ISROOT, 
          FUN_CREATE_ACYCLIC_LIST, 
          FUN_CREATE_CYCLIC_LIST , 
          FUN_CREATE_ACYCLIC_DLIST, 
          FUN_CREATE_CYCLIC_DLIST,
          
          AUX_HAVOC,
          AUX_ALLOC,
          AUX_ARRAY_ALLOC,
          AUX_STRUCT_ALLOC);
}
