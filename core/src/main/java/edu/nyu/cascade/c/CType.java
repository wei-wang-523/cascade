package edu.nyu.cascade.c;

import xtc.tree.Node;
import xtc.type.*;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/**
 * An auxiliary C type analyzer for C programs.
 *
 */
public class CType {
  public static final String TYPE = xtc.Constants.TYPE;
  public static final String SCOPE = xtc.Constants.SCOPE;
  
  private static final String FIELD_INFIX = Identifiers.UNDERLINE;
  private static final xtc.type.C cAnalyzer = new xtc.type.C();
  
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
  	Preconditions.checkNotNull(ref);
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
    } else if(ref.isString()) {
      return ((StringReference) ref).getLiteral();
    } else if(ref.isNull()) {
      return ((NullReference) ref).toString();
    } else {
      throw new IllegalArgumentException("Unknown reference for " + ref);
    }
  }
  
  public static String parseTypeName(xtc.type.Type type) {
  	Preconditions.checkNotNull(type);
    StringBuffer sb =  new StringBuffer();
    if(type.isVoid())	 					sb.append(type.toString());
    else if(type.isBoolean()) 	sb.append(type.toString());
    else if(type.isStruct()) 		sb.append(type.getName());
    else if(type.isUnion())			sb.append(type.getName());
    else if(type.isInteger()) 	sb.append(type.toString());
    else if(type.isLabel())			sb.append(type.toLabel().getName());
    else if(type.isAlias()) 		sb.append(parseTypeName(type.toAlias().getType()));
    else if(type.isVariable()) 	sb.append(parseTypeName(type.toVariable().getType()));
    else if(type.isPointer()) 
    	sb.append("pointer(").append(parseTypeName(type.toPointer().getType())).append(')');
    else if(type.isArray())
      sb.append("array(").append(parseTypeName(type.toArray().getType())).append(')');
    else if(type.isAnnotated()){
      AnnotatedT annoType = type.toAnnotated();
      if(annoType.hasShape()) {
        sb.append(parseRefName(annoType.getShape()));
      } else {
        sb.append(parseTypeName(annoType.getType()));
      }
    }
    else
      throw new IllegalArgumentException("Cannot parse type " + type.getName());
    return sb.toString();
  }
  
  private static String parseRefName(Reference ref) {
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
  
  public static boolean hasType(Node node) {
  	return node.hasProperty(TYPE);
  }
  
  public static boolean hasScope(Node node) {
  	return node.hasProperty(SCOPE);
  }
  
  public static Type getType(Node node) {
  	Preconditions.checkArgument(hasType(node));
  	return (Type) node.getProperty(TYPE);
  }
  
  public static String getScopeName(Node node) {
  	Preconditions.checkArgument(node.hasProperty(SCOPE));
  	return node.getStringProperty(SCOPE);
  }

  /**
   * Get the size of <code>type</code>
   * 
   * @param type
   * @return 0 if the array type without size:
   * <code>extern char *sys_errlist[];</code>
   */
	public static long getSizeofType(Type type) {
			
		if(Preferences.isSet(Preferences.OPTION_BYTE_BASED)) {
			try {
				return cAnalyzer.getSize(type);
			} catch (IllegalArgumentException e) {
				IOUtils.err().println("WARNING: " + e.getMessage());
				return 0;
			} catch (NullPointerException e) {
				IOUtils.err().println("WARNING: emptry structure type " + type);
				return 0;
			}
		}
		
    xtc.type.Type resolvedType = type.resolve();
    if(resolvedType.isStruct()) {
    	if(resolvedType.toStruct().getMembers() == null) return 0;
    	
    	long size = 0;
    	for(VariableT member : resolvedType.toStruct().getMembers()) {
    		size += getSizeofType(member);
    	}
    	return size;
    }
	
    if(resolvedType.isUnion()) {
    	if(resolvedType.toUnion().getMembers() == null) return 0;
    	
    	long size = 0;
    	for(VariableT member : resolvedType.toUnion().getMembers()) {
    		size = Math.max(size, getSizeofType(member));
    	}
    	return size;
    }
    
		if(resolvedType.isArray()) {
			long length = resolvedType.toArray().getLength();
			long cellSize = getSizeofType(resolvedType.toArray().getType());
			return length * cellSize;
		}
		
		return 1;
  }
	
	public static Type getOffsetType(Type type, final String name) {
  	Preconditions.checkArgument(type.isStruct() || type.isUnion());
  	StructOrUnionT suType = type.toStructOrUnion();
  	return Iterables.find(suType.getMembers(), new Predicate<VariableT>() {
			@Override
      public boolean apply(VariableT elem) {
        return elem.getName().equals(name);
      }
  	}).getType();
	}

  public static long getOffset(Type type, final String name) {
  	Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
  	StructOrUnionT suType = type.resolve().toStructOrUnion();
  	
    if(Preferences.isSet(Preferences.OPTION_BYTE_BASED)){
      return cAnalyzer.getOffset(suType, name);
    }
    
    if(suType.isUnion()) {
    	if(Iterables.any(suType.getMembers(), new Predicate<VariableT>() {
				@Override
        public boolean apply(VariableT elem) {
	        return elem.getName().equals(name);
        }
    	})) 
    		return 0;      
    } else {
      long offset = 0;
      for(VariableT elem : suType.getMembers()) {
      	if(elem.getName().equals(name)) {
      		return offset;
      	}
      	offset += getSizeofType(elem.getType());
      }
    }
    
    throw new IllegalArgumentException("WARNING: " + suType.getName() 
    		+ " doesn't has member " + name);
  }
  
  public static Type getBottomType(Type t1, Type t2) {
  	if(t1 == null) return t2;
  	if(t2 == null) return t1;
  	if(t1.equals(t2)) return t1;
  	return getUnitType();
  }
  
  public static Type getUnitType() {
  	return NumberT.U_CHAR;
  }
  
  public static Type getVoidType() {
	  return VoidT.TYPE;
	}

	public static Type getBottomType(StructOrUnionT su) {
		if(su.getMembers() == null) return CType.getVoidType();
		
  	Type res = null;
  	for(Type type : su.getMembers()) {
  		res = res == null ? type : getBottomType(res, type);
  	}
  	return res;
  }
  
	/**
	 * Get the cell type of array, structure or union
	 * @param type
	 * @return
	 */
  public static Type getCellType(Type type) {
  	type = type.resolve();
  	if(type.isArray()) 
  		return getCellType(type.toArray().getType());
  	if(type.isStruct() || type.isUnion()) 
  		return getCellType(CType.getBottomType(type.toStructOrUnion()));
  	return type;
  }
  
  public static Type getArrayCellType(Type type) {
  	Preconditions.checkArgument(type.resolve().isArray());
  	Type resType = type.resolve();
  	while(resType.isArray()) {
  		resType = resType.toArray().getType().resolve();
  	}
  	return resType;
  }
  
  public static Type getStructOrUnionCellType(Type type) {
  	Preconditions.checkArgument(type.resolve().isStruct() ||
  			type.resolve().isUnion());
  	return getCellType(type);
  }
  
  public static long getArraySize(ArrayT type) {
  	Preconditions.checkArgument(type.hasLength());
  	Type cellType = type.getType();
  	if(cellType.isArray()) 
  		return type.getLength() * getArraySize(cellType.toArray());
  	else
  		return type.getLength();
  }
  
  public static boolean isPointerOrDecay(Type type) {
  	return type.isArray() || type.isPointer();
  }

	public static long getNumberOfCells(Type type, Type cellType) {
	  if(type.equals(cellType)) return 1;
	  
	  long size = CType.getSizeofType(type);
	  long cellSize = CType.getSizeofType(cellType);
	  return size/cellSize;
  }
	
	public static boolean isIncompatible(Type lhs, Type rhs) {
		Type lhs_ = lhs.resolve();
		Type rhs_ = rhs.resolve();
		
		if(isPointerOrDecay(lhs_))	return isPointerOrDecay(rhs_);
		
		return lhs.equals(rhs);
	}
	
	public static boolean isUnsigned(Type type) {
		type = type.resolve();
		if(!type.isNumber()) return true;
		switch(type.toNumber().getKind()) {
		case BYTE:
		case U_CHAR:
		case U_INT:
		case U_LONG:
		case U_LONG_LONG:
		case U_SHORT:
			return true;
		default:
			return false;
		}
	}
}
