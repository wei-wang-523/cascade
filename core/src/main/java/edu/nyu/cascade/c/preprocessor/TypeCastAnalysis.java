package edu.nyu.cascade.c.preprocessor;

import java.util.Set;

import xtc.Constants;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.Type;

import com.google.common.collect.Sets;

public class TypeCastAnalysis {
  
  private Set<GNode> hasViewSet;
  
  private TypeCastAnalysis() {
    hasViewSet = Sets.newHashSet();
  }
  
  public static TypeCastAnalysis create() {
    return new TypeCastAnalysis();
  }
  
  /**
   * Compute aliases for the cast statement like cast (typeNode) opNode
   * @param typeNode
   * @param opNode
   */
  public void cast(Node typeNode, Node opNode) {
    Type type = (Type) typeNode.getProperty(Constants.TYPE);
    Type srcType = (Type) opNode.getProperty(Constants.TYPE);
    if(!type.equals(srcType))
      hasViewSet.add((GNode) opNode);
  }
  
  public void assign(Node lhsNode, Node rhsNode) {
    Type rhs_type = (Type) rhsNode.getProperty(Constants.TYPE);
    if(rhs_type.hasShape() && rhs_type.getShape().isCast()) {
      Node opNode = rhsNode.getNode(1);
      hasViewSet.add((GNode) opNode);
      hasViewSet.add((GNode) lhsNode);
    }
    
    if(hasViewSet.contains((GNode) rhsNode)) {
      hasViewSet.add((GNode) lhsNode);
    }
  }
  
  public boolean hasView(Node node) {
    if(node.hasName("IndirectExpression")) {
      return hasViewSet.contains(node.getGeneric(0));
    }
    return hasViewSet.contains((GNode) node);
  }
}
