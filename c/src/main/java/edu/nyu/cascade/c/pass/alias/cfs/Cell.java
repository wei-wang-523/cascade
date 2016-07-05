package edu.nyu.cascade.c.pass.alias.cfs;

import java.math.BigInteger;
import java.util.Map;

import com.google.common.collect.Maps;

import edu.nyu.cascade.util.UnionFind.Partition;

class Cell extends Partition {
	private static final long serialVersionUID = 4086783340865611195L;

	// Property Names
	static String IsArray = "isArray";
	static String ArrayLength = "arrayLength";

	private static BigInteger nextId = BigInteger.ZERO;

	private final BigInteger id;

	enum CellKind {
		BOTTOM, SCALAR, STRUCT, FUNC
	}

	private final CellKind kind;
	private final long size;
	private Map<String, Object> properties = Maps.newHashMap();

	Cell(CellKind kind, long size) {
		super();
		this.kind = kind;
		this.size = size;
		this.id = nextId;
		nextId = nextId.add(BigInteger.ONE);
	}

	@Override
	public String toString() {
		return "Cell " + id;
	}

	int getId() {
		return id.intValue();
	}

	CellKind getKind() {
		return kind;
	}

	/**
	 * Get the size (the cell size) of the value type
	 * 
	 * @return
	 */
	long getSize() {
		return size;
	}

	void addProperty(String propertyName, Object property) {
		properties.put(propertyName, property);
	}

	Object getProperty(String propertyName) {
		return properties.get(propertyName);
	}

	boolean hasProperty(String propertyName) {
		return properties.containsKey(propertyName);
	}
}
