package edu.nyu.cascade.c.graphml;

import java.io.OutputStream;
import java.util.List;

import javax.xml.bind.JAXBElement;

import xtc.tree.Location;
import xtc.tree.Node;

import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.graphml.jaxb.DataType;
import edu.nyu.cascade.graphml.jaxb.DefaultType;
import edu.nyu.cascade.graphml.jaxb.GraphEdgedefaultType;
import edu.nyu.cascade.graphml.jaxb.GraphType;
import edu.nyu.cascade.graphml.jaxb.GraphmlType;
import edu.nyu.cascade.graphml.jaxb.KeyForType;
import edu.nyu.cascade.graphml.jaxb.KeyType;
import edu.nyu.cascade.graphml.jaxb.KeyTypeType;
import edu.nyu.cascade.graphml.jaxb.ObjectFactory;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.Identifiers;

public class TraceGraphMLBuilder {
	private final ObjectFactory objectFactory;
	private final List<Object> graphElems = Lists.newArrayList();
	
	public TraceGraphMLBuilder() {
		this.objectFactory = new ObjectFactory();
	}
	
	public JAXBElement<?> analyzeTrace(IRTraceNode entryTraceNode) {
		MLNode entry = MLNode.createEntry();
		addNode(entry);
		analyzeIRMLNode(entryTraceNode, entry);
		return build();
	}
	
	public void dumpXmlTrace(JAXBElement<?> traceGraphML, OutputStream outputStream) {
		GraphML.toXmlFile(traceGraphML, outputStream);
	}
	
	private void analyzeIRMLNode(IRTraceNode traceNode, MLNode preMLNode) {
		MLNode pre = preMLNode;
		for(IRStatement stmt : traceNode.getStatements()) {
			MLNode post = MLNode.create();
			MLEdge edge = MLEdge.create(pre, post);
			
			edge.setSourceCode(stmt.toString());
			
			Node srcNode = stmt.getSourceNode();
			
			if(srcNode != null) {
				Location loc = srcNode.getLocation();
				edge.setOriginLine(loc.line);
				edge.setOriginFile(loc.file);
			}
			
			switch(stmt.getType()) {
			case ASSIGN: {
				Expression traceExpr = traceNode.getTraceExpr(stmt);
				StringBuilder sb = new StringBuilder();
				sb.append(stmt.getOperand(0)).append('=').append(traceExpr);
				edge.setAssumption(sb.toString());
				break;
			}
			case ASSUME: {
				Expression traceExpr = traceNode.getTraceExpr(stmt);
				edge.setAssumption(traceExpr.toString());
				break;
			}
			case FUNC_ENT: {
				String funcName = CType.getScopeName(srcNode);
				edge.setEnterFunc(funcName);
				break;
			}
			case FUNC_EXIT:
				edge.setExitFunc((String) stmt.getProperty(Identifiers.SCOPE));
				break;
			default:
				break;
			}
			
			addEdge(edge);
			addNode(post);
			
			pre = post;
		}
		
		if(traceNode.hasSuccessor()) {
			IRTraceNode succ = traceNode.getSuccessors().get(0);
			analyzeIRMLNode(succ, pre);
		} else {
			MLNode vio = MLNode.createViolation();
			MLEdge edge = MLEdge.create(pre, vio);
			addEdge(edge); addNode(vio);
		}
	}
	
	private JAXBElement<GraphmlType> build() {
		GraphmlType graphmlType = objectFactory.createGraphmlType();
		List<KeyType> keys = graphmlType.getKey();
		
		keys.add(getKeyType("assumption", "assumption", KeyForType.EDGE, KeyTypeType.STRING));
		keys.add(getKeyType("sourcecode", "sourcecode", KeyForType.EDGE, KeyTypeType.STRING));
		keys.add(getKeyType("sourcecodeLanguage", "sourcecodelang", KeyForType.GRAPH, KeyTypeType.STRING));
		keys.add(getKeyType("tokenSet", "tokens", KeyForType.EDGE, KeyTypeType.STRING));
		keys.add(getKeyType("originTokenSet", "origintokens", KeyForType.EDGE, KeyTypeType.STRING));
		keys.add(getKeyType("negativeCase", "negated", KeyForType.EDGE, KeyTypeType.STRING, String.valueOf(false)));
		keys.add(getKeyType("lineNumberInOrigin", "originline", KeyForType.EDGE, KeyTypeType.INT));
		keys.add(getKeyType("originFileName", "originfile", KeyForType.EDGE, KeyTypeType.STRING, "&lt;command-line&gt;"));
		keys.add(getKeyType("nodeType", "nodetype", KeyForType.NODE, KeyTypeType.STRING, "path"));
		keys.add(getKeyType("isFrontierNode", "frontier", KeyForType.NODE, KeyTypeType.BOOLEAN, String.valueOf(false)));
		keys.add(getKeyType("isViolationNode", "violation", KeyForType.NODE, KeyTypeType.BOOLEAN, String.valueOf(false)));
		keys.add(getKeyType("isEntryNode", "entry", KeyForType.NODE, KeyTypeType.BOOLEAN, String.valueOf(false)));
		keys.add(getKeyType("isSinkNode", "sink", KeyForType.NODE, KeyTypeType.BOOLEAN, String.valueOf(false)));
		keys.add(getKeyType("enterFunction", "enterFunction", KeyForType.EDGE, KeyTypeType.STRING));
		keys.add(getKeyType("returnFromFunction", "returnFrom", KeyForType.EDGE, KeyTypeType.STRING));
		
		GraphType graphType = buildGraphType();
		graphmlType.getGraphOrData().add(graphType);
		return objectFactory.createGraphml(graphmlType);
	}
	
	private void addNode(MLNode node) {
		graphElems.add(node.toNodeType(objectFactory));
	}
	
	private void addEdge(MLEdge edge) {
		graphElems.add(edge.toEdgeType(objectFactory));
	}
	
	private KeyType getKeyType(String attrName, String id, KeyForType forWhat, KeyTypeType keyTypeType) {
		KeyType keyType = objectFactory.createKeyType();
		keyType.setAttrName(attrName);
		keyType.setAttrType(keyTypeType);
		keyType.setFor(forWhat);
		keyType.setId(id);
  	return keyType;
	}
	
	private KeyType getKeyType(String attrName, String id, KeyForType forWhat, KeyTypeType keyTypeType, String defaultVal) {
		KeyType keyType = objectFactory.createKeyType();
		keyType.setAttrName(attrName);
		keyType.setAttrType(keyTypeType);
		keyType.setFor(forWhat);
		keyType.setId(id);
		
		DefaultType defaultType = objectFactory.createDefaultType();
		defaultType.setContent(defaultVal);
		keyType.setDefault(defaultType);
  	return keyType;
	}
	
	private GraphType buildGraphType() {
		GraphType graphType = objectFactory.createGraphType();
		graphType.setEdgedefault(GraphEdgedefaultType.DIRECTED);
		
		DataType dataType = objectFactory.createDataType();
		dataType.setKey("sourcecodelang");
		dataType.setContent("C");
		
		graphElems.add(0, dataType);
		graphType.getDataOrNodeOrEdge().addAll(graphElems);
		return graphType;
	}
}
