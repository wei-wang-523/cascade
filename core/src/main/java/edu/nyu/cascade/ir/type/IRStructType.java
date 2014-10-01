package edu.nyu.cascade.ir.type;

import java.util.Iterator;
import java.util.Map;

import com.google.common.collect.Maps;

public final class IRStructType extends IRType {

	private static final Map<String, IRStructType> singletonMap = Maps.newHashMap();
	
  public static IRStructType create(String name, 
  		 Iterable<String> elemNames, Iterable<IRType> memTypes) {
  	if(singletonMap.containsKey(name))
  		return singletonMap.get(name);
  	
    IRStructType type = new IRStructType(name, elemNames, memTypes);
    singletonMap.put(name, type);
    return type;
  }
  
  private final String name;
  private final Iterable<String> elemNames;
  private final Iterable<? extends IRType> elemTypes;
  
  private IRStructType(String name, Iterable<String> elemNames, Iterable<? extends IRType> elemTypes) {
    this.name = name;
    this.elemTypes = elemTypes;
    this.elemNames = elemNames;
  }

  @Override
  public Kind getKind() {
    return Kind.STRUCT;
  }
  
  public String getName() {
		return name;
	}

	public Iterable<String> getElemNames() {
		return elemNames;
	}

	public Iterable<? extends IRType> getElemTypes() {
		return elemTypes;
	}

	@Override
  public String toString() {
		StringBuilder sb = new StringBuilder().append("Struct ").append(name)
				.append("(\n");
		
		Iterator<String> elemNameItr = elemNames.iterator();
		Iterator<? extends IRType> elemTypeItr = elemTypes.iterator();
		
		while(elemNameItr.hasNext() && elemTypeItr.hasNext()) {
			sb.append(elemNameItr.next()).append(" : ").append(elemTypeItr.next()).append('\n');
		}
		sb.append(')');
		
		return sb.toString();
  }
}
