package edu.nyu.cascade.c;

import java.util.List;

import xtc.tree.Node;
import xtc.type.*;
import xtc.type.Type.Tag;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/**
 * An auxiliary C type analyzer for C programs.
 *
 */
public final class CType {
  public static final String TYPE = xtc.Constants.TYPE;
  public static final String SCOPE = xtc.Constants.SCOPE;
  
  public static final int BYTE_SIZE = Preferences.isSet(Preferences.OPTION_M32) ?
  		Limits32.CHAR_BITS : Limits64.CHAR_BITS;
  
  private static final String FIELD_INFIX = Identifiers.SCOPE_INFIX;
  
  private static final CType instance = new CType();
  
  public static CType getInstance() {
  	return instance;
  }
	
  public static String parseTypeName(Type type) {
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
  
	public static Type getArrayCellType(Type type) {
  	Preconditions.checkArgument(Tag.ARRAY.equals(type.tag()));
  	Type resType = type.resolve();
  	do {
  		resType = resType.toArray().getType().resolve();
  	} while(resType.isArray());
  	return resType;
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

	public static boolean isScalar(Type type) {
	  switch (type.tag()) {
	  case BOOLEAN:
	  case INTEGER:
	  case FLOAT:
	  case POINTER:
	    return true;
	  default:
	    return false;
	  }
	}

	/**
	 * Get the cell type of array, structure or union
	 * @param type
	 * @return
	 */
	public static Type getCellType(Type type) {
    type = type.resolve();

    // The type has been resolved.
    switch (type.tag()) {
    case VOID:
      return type;
    case ARRAY: {
      // An array is incomplete if (1) it is not variable and has no
      // lenght, (2) it has an incomplete member type, or (3) it has a
      // trailing array.
      ArrayT a = type.toArray();
      return getCellType(a.getType());
    }
    case STRUCT: 
    case UNION: {
      // A struct is incomplete if (1) it has no members, (2) any
      // member but the last member is incomplete, (3) the last member
      // is not an array but is incomplete, or (4) the last member is
      // an array with an incomplete element type.
      List<VariableT> members = type.toStructOrUnion().getMembers();
      if (null == members) return VoidT.TYPE;
      Type cellType = null;
      
      for (VariableT member : members) {
      	Type memCellType = getCellType(member);
        if(cellType == null) {
        	cellType = memCellType;
        } else {
        	if(cellType.tag().equals(memCellType.tag())) continue;
        	cellType = IntegerT.BYTE; break;
        }
      }
      
      return cellType;
    }
    default:
      return type;
    }
	}

	private final xtc.type.C C =  
			Preferences.isSet(Preferences.OPTION_M32) ? new C32() : new C64();

	public boolean equal(Type lhs, Type rhs) {
		return C.equal(lhs, rhs);
	}

	public Type convert(Type lhsType, Type rhsType) {
		if(lhsType.resolve().tag().equals(Tag.POINTER) || !C.isScalar(lhsType)
				|| rhsType.resolve().tag().equals(Tag.POINTER) || !C.isScalar(rhsType))
			return PointerT.TO_VOID;
		
		return C.convert(lhsType, rhsType);
	}
	
	public int getWordSize() {
		if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) return BYTE_SIZE;
		
		if(Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE))
				return Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE);
		
		return (int) C.getWidth(NumberT.INT);
	}

	public Type typeInteger(String literal) {
		return C.typeInteger(literal);
	}

	public Type typeCharacter(String literal) {
		return C.typeCharacter(literal);
	}

	public long getWidth(Type type) {  	
		if(Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return getSize(type) * C.getWidth(NumberT.CHAR);
		else {
			return getSize(type) * getWordSize();
		}
	}

	/**
	 * Get the size of <code>type</code>
	 * 
	 * @param type
	 * @return 0 if the array type without size:
	 * <code>extern char *sys_errlist[];</code>
	 */
	public long getSize(Type type) {
		if(Preferences.isSet(Preferences.OPTION_BYTE_BASED))
			return C.getSize(type);
		else
			return getSizeSimple(type);
	}

	private long getSizeSimple(Type type) {
	  switch(type.resolve().tag()) {
		case BOOLEAN:
		case ENUM:
		case ENUMERATOR:
		case FLOAT:
		case INTEGER:
		case POINTER:
			return 1;
		case STRUCT: {
			List<VariableT> members = type.resolve().toStruct().getMembers();
			if(members == null) return 0;
			long size = 0;
			
			for(VariableT member : members)
				size += getSizeSimple(member);
			
			return size;
		}
		case ARRAY: {
			ArrayT arrayT = type.resolve().toArray();
		  long length = arrayT.getLength();
		  long cellSize = getSizeSimple(arrayT.toArray().getType());
		  return length * cellSize;
		}
		case UNION: {
			List<VariableT> members = type.resolve().toUnion().getMembers();
			if(members == null) return 0;
			long size = 0;
			
			for(VariableT member : members)
				size = Math.max(size, getSizeSimple(member));
			
			return size;
		}
		case VOID:
			return 0;
		default:
			throw new IllegalArgumentException("Unknown size of type: " + type);
	  }
	}

	public long getOffset(Type type, String name) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
		
	  if(Preferences.isSet(Preferences.OPTION_BYTE_BASED))
	    return C.getOffset( type.resolve().toStructOrUnion(), name);
	  else
	  	return getOffsetSimple(type, name);
	}

	private long getOffsetSimple(Type type,  String name) {
		StructOrUnionT suType = type.resolve().toStructOrUnion();
	  if (suType.isStruct()) {
	    final List<VariableT> members     = suType.getMembers();
	    final int             memberCount = members.size();
	    long size = 0;
	    for (int i=0; i<memberCount; i++) {
	      // Process the member.
	      final VariableT var = members.get(i);
	      
	      if (null != name) {
	        if (var.hasName(name)) {
	          return size;
	        } else if (! var.hasName()) {
	          final long offset = getOffsetSimple(var.toStructOrUnion(), name);
	          if (-1 != offset) return size + offset;
	        }
	      }
	      
	      size += getSizeSimple(var);
	    }
	    
	    return size;
	  } else {
	    for (VariableT var : suType.getMembers()) {
	      if (var.hasName(name)) {
	        return 0;
	      } else if (! var.hasName() && ! var.hasWidth()) {
	        final long offset = getOffset(var.toStructOrUnion(), name);
	        if (-1 != offset) return offset;
	      }
	    }
	    return -1;
	  }
	}
}
