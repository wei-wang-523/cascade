package edu.nyu.cascade.c;

import xtc.tree.Node;
import xtc.type.*;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.util.Identifiers;

/**
 * An auxiliary C type analyzer for C programs.
 *
 */
public class CType {
  public static final String TYPE = xtc.Constants.TYPE;
  public static final String SCOPE = xtc.Constants.SCOPE;
  
  public enum CellKind {
    SCALAR, POINTER, STRUCTORUNION, ARRAY, BOOL
  }
  
  public static xtc.type.Type unwrapped(xtc.type.Type type) {
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type;
  }
  
  public static CellKind getCellKind(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    type = unwrapped(type);
    if(type.isBoolean())        return CellKind.BOOL;
    else if(type.isInteger())   return CellKind.SCALAR;
    else if(type.isPointer())   return CellKind.POINTER;
    else if(type.isArray())     return CellKind.ARRAY;
    else if(type.isStruct())    return CellKind.STRUCTORUNION;
    else if(type.isUnion())     return CellKind.STRUCTORUNION;
    else
      throw new IllegalArgumentException("Unknown type " + type);
  }
  
  public static String getReferenceName(Type type) {
    if(!(type.hasShape() 
        || (type.hasConstant() && type.getConstant().isReference())))   
      return Identifiers.CONSTANT;
    
    if(type.hasConstant() && type.getConstant().isReference()) {
      Reference constRef = type.getConstant().refValue();
      if(!constRef.isString()) return getReferenceName(constRef);
    } 
      
    return getReferenceName(type.getShape());
  }
  
  private static String getReferenceName(Reference ref) {
    Preconditions.checkArgument(ref != null);
    if(ref.isStatic()) {
      return ((StaticReference) ref).getName();
    } else if(ref.isDynamic()) {
      return ((DynamicReference) ref).getName();
    } else if(ref.isIndirect()) {
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref instanceof FieldReference) {
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref instanceof IndexReference) {
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref.isCast()) { 
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref instanceof AddressOfReference) { 
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref.isString()) {
      return ((StringReference) ref).getLiteral();
    } else if(ref.isNull()) {
      return ((NullReference) ref).toString();
    } else {
      throw new IllegalArgumentException("Unknown reference for " + ref);
    }
  }
  
  public static String parseTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);     
    StringBuffer sb =  new StringBuffer();
    if(type.isBoolean()) {
      sb.append(Identifiers.ARRAY_NAME_INFIX).append("BoolT");
    } else if(type.isPointer()) {
      xtc.type.Type pType = type.toPointer().getType();
      sb.append(Identifiers.ARRAY_NAME_INFIX)
      .append("PointerT").append(parseTypeName(pType));
    } else if(type.isArray()) {
      xtc.type.Type aType = type.toArray().getType();
      sb.append(Identifiers.ARRAY_NAME_INFIX)
      .append("ArrayT").append(parseTypeName(aType));
    } else if(type.isStruct()) {
      sb.append(Identifiers.ARRAY_NAME_INFIX)
      .append(type.getName());
    } else if(type.isUnion()) {
      sb.append(Identifiers.ARRAY_NAME_INFIX).append(type.getName());
    } else if(type.isAnnotated()){
      AnnotatedT annoType = type.toAnnotated();
      if(annoType.hasShape()) {
        Reference ref = annoType.getShape();
        if(ref instanceof FieldReference) {
          FieldReference fieldRef = (FieldReference) ref;
          xtc.type.Type baseType = fieldRef.getBase().getType();
          String baseTypeName = parseTypeName(baseType);
          sb.append(baseTypeName).append('.').append(fieldRef.getField());
        } else {
          sb.append(parseTypeName(ref.getType()));
        }
      } else {
        sb.append(parseTypeName(annoType.getType()));
      }
    } else if(type.isAlias()) {
      xtc.type.Type aliasType = type.toAlias().getType();
      sb.append(parseTypeName(aliasType));
    } else if(type.isVariable()) {
      xtc.type.Type varType = type.toVariable().getType();
      sb.append(parseTypeName(varType));
    } else if(type.isInteger()){
      String kindName = type.toInteger().getKind().name();
      sb.append(Identifiers.ARRAY_NAME_INFIX)
      .append(kindName);
    } else if(type.isLabel()){
      sb.append(Identifiers.ARRAY_NAME_INFIX)
      .append(type.toLabel().getName());
    } else {
      throw new IllegalArgumentException("Cannot parse type " + type.getName());
    }
    return sb.toString();
  }
  
  public static int numOfIndRef(Reference ref) {
    int currentNum = ref.hasBase() ? numOfIndRef(ref.getBase()) : 0;
    if(ref.isIndirect()) 
      currentNum++;
    if(ref instanceof AddressOfReference)
      currentNum--;
    return currentNum;
  }
  
  public static Type getType(Node node) {
  	Preconditions.checkArgument(node.hasProperty(TYPE));
  	return (Type) node.getProperty(TYPE);
  }
  
  public static String getScope(Node node) {
  	Preconditions.checkArgument(node.hasProperty(SCOPE));
  	return node.getStringProperty(SCOPE);
  }
}
