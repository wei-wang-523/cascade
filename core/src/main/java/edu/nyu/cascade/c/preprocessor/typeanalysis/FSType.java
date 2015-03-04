package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.math.BigInteger;
import java.util.Map;

import com.google.common.collect.Maps;

import edu.nyu.cascade.util.HashCodeUtil;
import edu.nyu.cascade.util.Identifiers;
import xtc.type.Type;

/**
 * A wrapper for scalar type with an id, used for field sensitive 
 * type analysis. For elements nested inside a structure or union
 * the id is structName.elemName.
 * 
 * @author Wei
 *
 */

public final class FSType {
	
	private static Map<String, FSType> fsTypeMap = Maps.newHashMap();
	
  private static BigInteger nextId = BigInteger.ONE;

  private BigInteger id;  
	private final Type type;
	private final String typeName;
	private final FSType parent;
	
	private FSType(Type type, String typeName, FSType parent) {
		this.type = type;
		this.typeName = typeName;
		this.parent = parent;
		id = nextId;
		nextId = nextId.add(BigInteger.ONE);
	}

	static FSType of(Type type, String typeName) {
		if(fsTypeMap.containsKey(typeName)) return fsTypeMap.get(typeName);
		FSType fsType = new FSType(type, typeName, null);
		fsTypeMap.put(typeName, fsType);
		return fsType;
	}
	
	static FSType of(Type type, String typeName, FSType parent) {
		String id = parent != null ? 
				parent.getTypeName() + Identifiers.UNDERLINE + typeName
				 : typeName;
		
		if(fsTypeMap.containsKey(id)) return fsTypeMap.get(id);
		FSType fsType = new FSType(type, typeName, parent);
		fsTypeMap.put(id, fsType);
		return fsType;
	}
	
	@Override
	public boolean equals(Object o) {
		if(!(o instanceof FSType)) return false;
		FSType that = (FSType) o;
		return id.equals(that.id);
	}
	
	@Override
	public int hashCode() {
		return HashCodeUtil.hash(HashCodeUtil.SEED, id);
	}
	
	@Override
  public String toString() {
    return typeName;
  }
	
	Type getType() {
		return type;
	}
	
	String getTypeName() {
		return typeName;
	}
	
	int getId() {
		return id.intValue();
	}
	
	FSType getParent() {
		return parent;
	}
	
	boolean hasParent() {
		return parent != null;
	}
}
