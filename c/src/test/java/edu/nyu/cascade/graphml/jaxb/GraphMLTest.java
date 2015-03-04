package edu.nyu.cascade.graphml.jaxb;

import java.util.List;

import javax.xml.bind.JAXBElement;

import org.junit.Test;

import edu.nyu.cascade.c.graphml.GraphML;

public class GraphMLTest {
	
	private final ObjectFactory factory = new ObjectFactory();
	
	@Test
	public void testKeyToXML() {
		GraphmlType graphmlType = factory.createGraphmlType();
		List<KeyType> keys = graphmlType.getKey();
		
  	KeyType keyType_1 = factory.createKeyType();
  	keyType_1.setAttrName("assumption");
  	keyType_1.setAttrType(KeyTypeType.STRING);
  	keyType_1.setFor(KeyForType.EDGE);
  	keyType_1.setId("assumption");
  	keys.add(keyType_1);
  	
  	KeyType keyType_2 = factory.createKeyType();
  	keyType_2.setAttrName("negativeCase");
  	keyType_2.setAttrType(KeyTypeType.STRING);
  	keyType_2.setFor(KeyForType.EDGE);
  	keyType_2.setId("negated");
  	
  	DefaultType defaultType = factory.createDefaultType();
  	defaultType.setContent("false");
  	keyType_2.setDefault(defaultType);
  	keys.add(keyType_2);
  	
  	JAXBElement<GraphmlType> graphml = factory.createGraphml(graphmlType);
  	GraphML.toXml(graphml);
	}
	
	@Test
	public void testDataToXML() {
		DataType dataType = factory.createDataType();
		dataType.setKey("sourcecodelang");
		dataType.setContent("C");
		GraphML.toXml(factory.createData(dataType));
	}
	
	@Test
//	@Ignore
	public void testGraphToXML() {
  	GraphType graphType = factory.createGraphType();
  	graphType.setEdgedefault(GraphEdgedefaultType.DIRECTED);
  	
  	List<Object> elems = graphType.getDataOrNodeOrEdge();
  	
  	{
  		DataType dataType = factory.createDataType();
  		dataType.setKey("sourcecodelang");
  		dataType.setContent("C");
  		elems.add(dataType);
  	}
		
  	{
			DataType nodeDataType = factory.createDataType();
			nodeDataType.setKey("entry");
			nodeDataType.setContent("true");
			
			NodeType nodeType = factory.createNodeType();
			nodeType.setId("A1");
			nodeType.getDataOrPort().add(nodeDataType);
			elems.add(nodeType);
		}
  	
  	{
  		EdgeType edgeType = factory.createEdgeType();
  		edgeType.setSource("A6");
  		edgeType.setTarget("A9");
  		List<DataType> data = edgeType.getData();
  		
  		DataType data_0 = factory.createDataType();
  		data_0.setKey("originline");
  		data_0.setContent("5");
  		data.add(data_0);
  		
  		DataType data_1 = factory.createDataType();
  		data_1.setKey("tokens");
  		data_1.setContent("21");
  		data.add(data_1);
  		
  		elems.add(edgeType);
  	}
  	
		GraphmlType graphmlType = factory.createGraphmlType();
		graphmlType.getGraphOrData().add(graphType);
  	
  	JAXBElement<GraphmlType> graphml = factory.createGraphml(graphmlType);
  	GraphML.toXml(graphml);
	}
}
