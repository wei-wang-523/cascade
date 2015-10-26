package edu.nyu.cascade.c.graphml;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.Maps;

import edu.nyu.cascade.graphml.jaxb.DataType;
import edu.nyu.cascade.graphml.jaxb.EdgeType;
import edu.nyu.cascade.graphml.jaxb.ObjectFactory;

public class MLEdge {

	private static final String SOURCE_CODE = "sourcecode";
//	private static final String TOKENS = "tokens";
//	private static final String ORIGIN_FILE = "originfile";
	private static final String ORIGIN_OFFSET = "originoffset";
	private static final String ORIGIN_LINE = "originline";
	private static final String ASSUMPTION = "assumption";
	private static final String CONTROL = "control";
	private static final String SCOPE = "assumption.scope";
	private static final String ENTER_FUNC = "enterFunction";
	private static final String EXIT_FUNC = "returnFromFunction";
	
	private final MLNode srcNode;
	private final MLNode destNode;
	
	private final Map<String, Object> properties = Maps.newHashMap();
	
	private MLEdge(MLNode srcNode, MLNode destNode) {
		this.srcNode = srcNode;
		this.destNode = destNode;
	}
	
	public static MLEdge create(MLNode srcNode, MLNode destNode) {
		return new MLEdge(srcNode, destNode);
	}
	
	public void setSourceCode(String srcCode) {
		properties.put(SOURCE_CODE, srcCode);
	}
	
	public void setScope(String scope) {
		properties.put(SCOPE, scope);
	}
	
	public void setOriginLine(int line) {
		properties.put(ORIGIN_LINE, line);
	}
	
	public void setOriginOffset(int offset) {
		properties.put(ORIGIN_OFFSET, offset);
	}
	
	public void setAssumption(String assumption) {
		properties.put(ASSUMPTION, assumption);
	}
	
	public void setEnterFunc(String funcName) {
		properties.put(ENTER_FUNC, funcName);
	}
	
	public void setExitFunc(String funcName) {
		properties.put(EXIT_FUNC, funcName);
	}
	
	public void setCondition(boolean edgeNegated) {
	  properties.put(CONTROL, edgeNegated ? "condition-false" : "condition-true");
  }
	
	public EdgeType toEdgeType(ObjectFactory factory) {
		EdgeType edgeType = factory.createEdgeType();
		edgeType.setSource(srcNode.toString());
		edgeType.setTarget(destNode.toString());
		List<DataType> datas = edgeType.getData();
		
		for(Entry<String, Object> entry : properties.entrySet()) {
			DataType dataType = factory.createDataType();
			dataType.setKey(entry.getKey());
			dataType.setContent(entry.getValue().toString());
			datas.add(dataType);
		}
		
		return edgeType;
	}
}
