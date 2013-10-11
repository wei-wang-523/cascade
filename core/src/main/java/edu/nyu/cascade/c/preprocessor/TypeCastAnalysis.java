package edu.nyu.cascade.c.preprocessor;

import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.Node;
import xtc.type.FieldReference;
import xtc.type.Reference;
import xtc.type.Type;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.AddressOfReference;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;

public class TypeCastAnalysis {
  
  private final LoadingCache<Reference, Boolean> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Reference, Boolean>(){
        public Boolean load(Reference ref) {
          return hasView(ref);
        }
      });
  
  private Set<Reference> hasViewSet;
  
  private TypeCastAnalysis() {
    hasViewSet = Sets.newHashSet();
  }
  
  public static TypeCastAnalysis create() {
    return new TypeCastAnalysis();
  }
  
  /**
   * Process cast statement like cast (typeNode) opNode
   * @param typeNode
   * @param opNode
   */
  public void cast(Node typeNode, Node opNode) {
    Type type = CType.getType(typeNode);
    Type srcType = CType.getType(opNode);
    
    // pointer casting ?
    if(type.resolve().isPointer() && srcType.resolve().isPointer()) {
      if(!type.equals(srcType)) {
        Reference srcType_ref = srcType.getShape();
        hasViewSet.add(srcType_ref);
      }
    }
  }
  
  /**
   * Process declare structure or union statement like 
   * data := struct[sizeof(union Data)]
   * @param op
   */
  public void declareStruct(Node opNode) {
    Type type = CType.getType(opNode);
    if(type.resolve().isUnion() && type.hasShape()) {
      Reference ref = type.getShape();
      Reference add_ref = new AddressOfReference(ref);
      hasViewSet.add(add_ref);
    }
  }
  
  /**
   * Process heap assign statement like 
   * alloc(data)
   * @param op
   */
  public void heapAssign(Node opNode) {
    Type ptrType = CType.getType(opNode);
    Type type = ptrType.resolve().toPointer().getType();
    if(type.resolve().isUnion()/* || type.resolve().isStruct()*/) {
      if(ptrType.hasShape()) {
        Reference ref = ptrType.getShape();
        hasViewSet.add(ref);
      }
    }
  }
  
  /**
   * Compute aliases for assign statement, if reference of @param rhsNode
   * is contained in hasViewSet, add the reference of @param lhsNode to
   * it too.
   */
  public void assign(Node lhsNode, Node rhsNode) {
    Type lhsType = CType.getType(lhsNode);
    Type rhsType = CType.getType(rhsNode);
    
    if(rhsType.hasShape()) {
      Reference rhsRef = rhsType.getShape();
      if(rhsRef.isCast()) rhsRef = rhsRef.getBase();
      if(hasViewSet.contains(rhsRef)) {
        if(lhsType.hasShape()) {
          Reference lhsRef = lhsType.getShape();
          hasViewSet.add(lhsRef);
        }
      }
    }
  }
  
  /**
   * Decide if @param node reference is contained in the hasViewSet
   * @return
   */
  public boolean hasView(Node node) {
    Type type = CType.getType(node);
    boolean res = false;
    if(type.hasShape()) {
      try {
        res = cache.get(type.getShape());
      } catch (ExecutionException e) {
        throw new ExpressionFactoryException(e);
      }
    }
    return res;
  }
  
  private boolean hasView(Reference ref) {
    if(ref.isIndirect()) {
      Reference base = ref.getBase();
      return hasViewSet.contains(base);
    } else if(ref instanceof FieldReference) {
      return hasView(ref.getBase());
    } else {
      Reference addr = new AddressOfReference(ref);
      return hasViewSet.contains(addr);
    }
  }
  
  public String displaySnapShot() {
    StringBuilder sb = new StringBuilder();
    sb.append("HasView set contains: { ");
    for(Reference ref : hasViewSet) {
      sb.append(ref).append(' ');
    }
    sb.append("}\n");
    return sb.toString();
  }
}
