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
	private static final String TOKENS = "tokens";
	private static final String ORIGIN_FILE = "originfile";
	private static final String ORIGIN_TOKENS = "origintokens";
	private static final String ORIGIN_LINE = "originline";
	private static final String ASSUMPTION = "assumption";
	private static final String NEGATED = "negated";
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
	
	public void setTokens(String tokens) {
		properties.put(TOKENS, tokens);
	}
	
	public void setOriginFile(String file) {
		properties.put(ORIGIN_FILE, file);
	}
	
	public void setOriginTokens(String tokens) {
		properties.put(ORIGIN_TOKENS, tokens);
	}
	
	public void setOriginLine(int line) {
		properties.put(ORIGIN_LINE, line);
	}
	
	public void setAssumption(String assumption) {
		properties.put(ASSUMPTION, assumption);
	}
	
	public void setNegate() {
		properties.put(NEGATED, true);
	}
	
	public void setEnterFunc(String funcName) {
		properties.put(ENTER_FUNC, funcName);
	}
	
	public void setExitFunc(String funcName) {
		properties.put(EXIT_FUNC, funcName);
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
