package edu.nyu.cascade.c.graphml;

import java.io.OutputStream;
import java.net.URL;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;

import org.xml.sax.SAXException;

import edu.nyu.cascade.util.FileUtils;

public class GraphML {
	public static final URL SCHEMA_URL = FileUtils.resourceURL("graphml.xsd");
	private static final Marshaller MARSHALLER;
	public static final Schema SCHEMA;

	static {
		SchemaFactory sf = SchemaFactory.newInstance(
				XMLConstants.W3C_XML_SCHEMA_NS_URI);
		try {
			SCHEMA = sf.newSchema(SCHEMA_URL);
			JAXBContext jc = JAXBContext.newInstance("edu.nyu.cascade.graphml.jaxb");
			MARSHALLER = jc.createMarshaller();
			MARSHALLER.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, true);
			MARSHALLER.setSchema(SCHEMA);
		} catch (SAXException e) {
			throw new RuntimeException("Could not parse graph ml schema", e);
		} catch (JAXBException e) {
			throw new RuntimeException("Could not create graph ml parser", e);
		}
	}

	public static void toXml(Object graphml) {
		try {
			MARSHALLER.marshal(graphml, System.out);
		} catch (JAXBException e) {
			throw new RuntimeException("Could not create graph ml parser", e);
		}
	}

	public static void toXmlFile(Object graphml, OutputStream outputStream) {
		try {
			MARSHALLER.marshal(graphml, outputStream);
		} catch (JAXBException e) {
			throw new RuntimeException("Could not create graph ml parser", e);
		}
	}
}
