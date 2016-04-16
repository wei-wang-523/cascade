package edu.nyu.cascade.c.pass.alias.typesafe;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import xtc.Constants;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.AnnotatedT;
import xtc.type.CastReference;
import xtc.type.FieldReference;
import xtc.type.Reference;
import xtc.type.Type;

public class FSTypeEncoder extends Visitor {
  private static final char FIELD_INFIX = Constants.QUALIFIER;
    
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
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitFunctionCall(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitShiftExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitAssignmentExpression(GNode node) {
  	FSType opType1 = encodeFSType(node.getNode(0));
  	FSType opType2 = encodeFSType(node.getNode(2));
  	FSType parent = unifyParents(opType1, opType2);
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitSubscriptExpression(GNode node) {
  	FSType base = encodeFSType(node.getNode(0));
  	
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitAddressExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitBitwiseAndExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitBitwiseOrExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitBitwiseXorExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitCastExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitCharacterConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitIndirectionExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitIntegerConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitPreincrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }

  public FSType visitPredecrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitPostincrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }

  public FSType visitPostdecrementExpression(GNode node) {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitPrimaryIdentifier(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitSimpleDeclarator(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }

  public FSType visitStringConstant(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitSizeofExpression(GNode node) {
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId);
  }
  
  public FSType visitUnaryMinusExpression(GNode node) 
      throws VisitingException {
    FSType base = encodeFSType(node.getNode(0));
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, base.getParent());
  }
  
  public FSType visitMultiplicativeExpression(GNode node) {
  	FSType opType1 = encodeFSType(node.getNode(0));
  	FSType opType2 = encodeFSType(node.getNode(2));
  	FSType parent = unifyParents(opType1, opType2);
  	
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitDirectComponentSelection(GNode node) {
    FSType parent = encodeFSType(node.getNode(0));
    
  	Type xtcType = CType.getType(node);
  	String typeId = parseTypeName(xtcType);
  	return FSType.of(xtcType, typeId, parent);
  }
  
  public FSType visitIndirectComponentSelection(GNode node) {
  	Type xtcType = CType.getType(node.getNode(0)).resolve().toPointer().getType();
  	String typeId = parseTypeName(xtcType);
  	FSType parent = FSType.of(xtcType, typeId);
  	
  	Type xtcFieldType = CType.getType(node);
  	String xtcFieldTypeId = parseTypeName(xtcFieldType);
  	return FSType.of(xtcFieldType, xtcFieldTypeId, parent);
  }
  
  String parseTypeName(Type type) {
  	Preconditions.checkNotNull(type);
    StringBuffer sb =  new StringBuffer();
    switch(type.tag()) {
		case ALIAS:
			sb.append(parseTypeName(type.toAlias().getType()));
			break;
		case ANNOTATED:
			AnnotatedT annoType = type.toAnnotated();
      if(annoType.hasShape()) {
        sb.append(parseRefName(annoType.getShape()));
      } else {
        sb.append(parseTypeName(annoType.getType()));
      }
			break;
		case ARRAY:
			sb.append("array(").append(parseTypeName(type.toArray().getType())).append(')');
			break;
		case BOOLEAN:
			sb.append(type.toString());
			break;
		case FLOAT:
			sb.append(type.toString());
			break;
		case FUNCTION:
			sb.append(type.toString());
			break;
		case INTEGER:
			sb.append(type.toString());
			break;
		case LABEL:
			sb.append(type.toLabel().getName());
			break;
		case POINTER:
			sb.append("pointer(").append(parseTypeName(type.resolve().toPointer().getType())).append(')');
			break;
		case STRUCT:
		case UNION:
			sb.append(type.getName());
			break;
		case VARIABLE:
			sb.append(parseTypeName(type.toVariable().getType()));
			break;
		case VOID:
			sb.append(type.toString());
			break;
		default:
			break;
    }
    return sb.toString();
  }
  
  private String parseRefName(Reference ref) {
		Preconditions.checkNotNull(ref);
	  StringBuffer sb =  new StringBuffer();
	  if(ref instanceof FieldReference) {
	  	FieldReference fieldRef = (FieldReference) ref;
	  	String baseName = parseRefName(fieldRef.getBase());
	  	sb.append(baseName).append(FIELD_INFIX).append(fieldRef.getField());
	  } else if(ref instanceof CastReference) {
	  	//FIXME: (int *) &d, type(ref) is int, type is pointer(int) 
	  	sb.append(parseTypeName(ref.getType().deannotate()));
	  } else {
	  	sb.append(parseTypeName(ref.getType()));
	  }
	  return sb.toString();
	}
  
}
