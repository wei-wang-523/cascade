package edu.nyu.cascade.c.graphml;

import java.math.BigInteger;

import edu.nyu.cascade.graphml.jaxb.DataType;
import edu.nyu.cascade.graphml.jaxb.NodeType;
import edu.nyu.cascade.graphml.jaxb.ObjectFactory;

public class MLNode {

	enum Type {
		SINK, ENTRY, VIOLATION, FRONTIER, OTHER
	}

	private static BigInteger next_id = BigInteger.ONE;

	private final Type type;
	private final BigInteger id;

	private MLNode(Type type) {
		this.type = type;
		this.id = next_id;
		next_id = next_id.add(BigInteger.ONE);
	}

	public static MLNode createSink() {
		return new MLNode(Type.SINK);
	}

	public static MLNode createEntry() {
		return new MLNode(Type.ENTRY);
	}

	public static MLNode createViolation() {
		return new MLNode(Type.VIOLATION);
	}

	public static MLNode createFrontier() {
		return new MLNode(Type.FRONTIER);
	}

	public static MLNode create() {
		return new MLNode(Type.OTHER);
	}

	@Override
	public String toString() {
		return "A" + id;
	}

	public NodeType toNodeType(ObjectFactory factory) {
		NodeType nodeType = factory.createNodeType();
		nodeType.setId(toString());
		switch (type) {
		case ENTRY: {
			DataType dataType = factory.createDataType();
			dataType.setKey("entry");
			dataType.setContent(String.valueOf(true));
			nodeType.getDataOrPort().add(dataType);
			break;
		}
		case SINK: {
			DataType dataType = factory.createDataType();
			dataType.setKey("sink");
			dataType.setContent(String.valueOf(true));
			nodeType.getDataOrPort().add(dataType);
			break;
		}
		case VIOLATION: {
			DataType dataType = factory.createDataType();
			dataType.setKey("violation");
			dataType.setContent(String.valueOf(true));
			nodeType.getDataOrPort().add(dataType);
			break;
		}
		case FRONTIER: {
			DataType dataType = factory.createDataType();
			dataType.setKey("frontier");
			dataType.setContent(String.valueOf(true));
			nodeType.getDataOrPort().add(dataType);
			break;
		}
		default:
			break;
		}
		return nodeType;
	}
}
