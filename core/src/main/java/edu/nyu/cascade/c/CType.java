package edu.nyu.cascade.c;

import xtc.type.*;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.util.Identifiers;

/**
 * An auxiliary C type analyzer for C programs.
 *
 */
public class CType {

  private final static String CONSTANT = Identifiers.toValidId("Constant");
  
  public enum CellKind {
    SCALAR, POINTER, STRUCT, UNION, ARRAY, BOOL
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
    if(type.hasConstant() && type.getConstant().isReference()) {
      Reference ref = type.getConstant().refValue();
      if(ref.getType().equals(BooleanT.TYPE)) {
        return CellKind.BOOL;
      }
    }
    
    type = unwrapped(type);
    if(type.isInteger())        return CellKind.SCALAR;
    else if(type.isPointer())   return CellKind.POINTER;
    else if(type.isArray())     return CellKind.ARRAY;
    else if(type.isStruct())    return CellKind.STRUCT;
    else if(type.isUnion())     return CellKind.UNION;
    else
      throw new IllegalArgumentException("Unknown type " + type);
  }
  
  public static String getReferenceName(Type type) {
    if(!(type.hasShape() 
        || (type.hasConstant() && type.getConstant().isReference())))   
      return CONSTANT;
    
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
    } else if(ref instanceof CastReference) { 
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref instanceof AddressOfReference) { 
      Reference base = ref.getBase();
      return getReferenceName(base);
    } else if(ref instanceof StringReference) {
      return ((StringReference) ref).getLiteral();
    } else {
      throw new IllegalArgumentException("Unknown reference for " + ref);
    }
  }
  
  public static String parseTypeName(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);     
    StringBuffer sb =  new StringBuffer();
    if(type.isPointer()) {
      xtc.type.Type pType = type.toPointer().getType();
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX)
      .append("PointerT").append(parseTypeName(pType));
    } else if(type.isArray()) {
      xtc.type.Type aType = type.toArray().getType();
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX)
      .append("ArrayT").append(parseTypeName(aType));
    } else if(type.isStruct()) {
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX)
      .append(type.getName());
    } else if(type.isUnion()) {
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX).append(type.getName());
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
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX)
      .append(kindName);
    } else if(type.isLabel()){
      sb.append(Identifiers.BURSTALL_ARRAY_NAME_INFIX)
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
}
