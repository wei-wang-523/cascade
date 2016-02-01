package edu.nyu.cascade.c.preprocessor.typeanalysis;

import edu.nyu.cascade.c.CType;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.Type;

public class FSTypeEncoder extends Visitor {
    
  public FSType encodeFSType(Node node) {
    FSType res = (FSType) dispatch(node);
    if(res == null) 
    	throw new IllegalArgumentException("Cannot encode FSType for node " + node);
    return res;
  }
  
  private FSType unifyParents(FSType opType1, FSType opType2) {
  	FSType parent1 = opType1.getParent();
  	FSType parent2 = opType2.getParent();
  	return parent1 != null ? parent1 : parent2;
  }

  public FSType visitAdditiveExpression(GNode node) {
  	FSType opType1 = encodeFSType(node.getNode(0));
  	FSType opType2 = encodeFSType(node.getNode(2));
  	FSType parent = unifyParents(opType1, opType2);
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitFunctionCall(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitShiftExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitAssignmentExpression(GNode node) {
  	FSType opType1 = encodeFSType(node.getNode(0));
  	FSType opType2 = encodeFSType(node.getNode(2));
  	FSType parent = unifyParents(opType1, opType2);
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitSubscriptExpression(GNode node) {
  	FSType base = encodeFSType(node.getNode(0));
  	
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitAddressExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitBitwiseAndExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitBitwiseOrExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitBitwiseXorExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitCastExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitCharacterConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitIndirectionExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitIntegerConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitPreincrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }

  public FSType visitPredecrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitPostincrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }

  public FSType visitPostdecrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitPrimaryIdentifier(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitSimpleDeclarator(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitStringConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitSizeofExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitUnaryMinusExpression(GNode node) 
      throws VisitingException {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitMultiplicativeExpression(GNode node) {
  	FSType opType1 = encodeFSType(node.getNode(0));
  	FSType opType2 = encodeFSType(node.getNode(2));
  	FSType parent = unifyParents(opType1, opType2);
  	
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitDirectComponentSelection(GNode node) {
    FSType parent = encodeFSType(node.getNode(0));
    
  	Type xtcType = CType.getType(node);
  	String typeId = CType.parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitIndirectComponentSelection(GNode node) {
  	Type xtcType = CType.getType(node.getNode(0)).resolve().toPointer().getType();
  	String typeId = CType.parseTypeName(xtcType);
  	FSType parent = FSType.of(xtcType, typeId);
  	
  	Type xtcFieldType = CType.getType(node);
  	String xtcFieldTypeId = CType.parseTypeName(xtcFieldType);
  	return FSType.of(xtcFieldType, xtcFieldTypeId, parent);
  }
}
