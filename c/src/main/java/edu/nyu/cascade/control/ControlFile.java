package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.net.URL;
import java.util.Map;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;

import org.xml.sax.SAXException;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.FileUtils;

public class ControlFile {
  public static final URL SCHEMA_URL = FileUtils.resourceURL("control.xsd");
  // private static final Schema schema = null;
  private static final Unmarshaller UNMARSHALLER;
  public static final Schema SCHEMA;
  
  static {
    SchemaFactory sf = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
//    URL schema_url = ClassLoader.getSystemResource(XML_SCHEMA.toString());
    try {
      SCHEMA = sf.newSchema(SCHEMA_URL);
      JAXBContext jc = JAXBContext.newInstance("edu.nyu.cascade.control.jaxb");
      UNMARSHALLER = jc.createUnmarshaller();
      UNMARSHALLER.setSchema(SCHEMA);
    } catch (SAXException e) {
      throw new RuntimeException("Could not parse control file schema", e);
    } catch (JAXBException e) {
      throw new RuntimeException("Could not create control file parser", e);
    }
  }
  
  public static ControlFile fromXml(File file) throws ControlFileException {
    try {
      edu.nyu.cascade.control.jaxb.ControlFile jaxbControlFile = (edu.nyu.cascade.control.jaxb.ControlFile) UNMARSHALLER.unmarshal(file);
      ControlFile.Builder cfBuilder = new ControlFile.Builder();
      Map<BigInteger, File> sourceFiles = Maps.newHashMap();
      for (edu.nyu.cascade.control.jaxb.ControlFile.SourceFile sourceFile : jaxbControlFile.getSourceFile()) {
        File f = new File(file.getParent(),sourceFile.getName());
        sourceFiles.put(sourceFile.getId(), f);
        cfBuilder.addSourceFile(f);
      }
      
//      cfBuilder.addTheories( jaxbControlFile.getTheory() );
      
//      cfBuilder.setTheoryId(jaxbControlFile.getTheory());
      edu.nyu.cascade.control.jaxb.ControlFile.Theory theory = jaxbControlFile.getTheory();
      if( theory != null ) {
        cfBuilder.setTheoryId(TheoryId.valueOf(theory));
      }
      
      for (edu.nyu.cascade.control.jaxb.ControlFile.Run run : jaxbControlFile.getRun()) {
        cfBuilder.addRun(Run.valueOf(run, sourceFiles));
      }
      return cfBuilder.build();
    } catch (JAXBException e) {
      throw new ControlFileException("Failed to parse " + file, e);
    }
  }

  private final ImmutableList<File> sourceFiles;
//  private final ImmutableList<TheoryId> theories;
  private final TheoryId theoryId;
  private final ImmutableList<Run> runs;

  private ControlFile(ImmutableList<File> sourceFiles, /*ImmutableList<TheoryId> theories*/TheoryId theoryId, ImmutableList<Run> runs) {
    this.sourceFiles = sourceFiles;
//    this.theories = theories;
    this.theoryId = theoryId;
    this.runs = runs;
  }

  public static class Builder {
    private ImmutableList.Builder<File> sourceFiles;
//    private ImmutableList.Builder<TheoryId> theories;
    private TheoryId theoryId;
    private ImmutableList.Builder<Run> runs;

    public Builder() {
      this.sourceFiles = new ImmutableList.Builder<File>();
      this.theoryId = null;
//      this.theories = new ImmutableList.Builder<TheoryId>();
      this.runs = new ImmutableList.Builder<Run>();
    }

    public Builder addSourceFile(File file) {
      sourceFiles.add(file);
      return this;
    }

    public Builder setTheoryId(TheoryId theoryId) {
      this.theoryId = theoryId;
//      this.theories.add(theoryId);
      return this;
    }
    
    public Builder addRun(Run run) {
      runs.add(run);
      return this;
    }

    public ControlFile build() {
      return new ControlFile(sourceFiles.build(), theoryId /*theories.build()*/, runs.build());
    }
  }

  public ImmutableList<Run> getRuns() {
    return runs;
  }

  public ImmutableList<File> getSourceFiles() {
    return sourceFiles;
  }

/*  public ImmutableList<TheoryId> getTheories() {
    return theories;
  }
*/
  
  public TheoryId getTheoryId() { return theoryId; }
}
