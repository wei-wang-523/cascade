package edu.nyu.cascade.control.jaxb;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FilenameFilter;
import java.util.List;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;
import javax.xml.validation.Schema;

import org.junit.Test;

import edu.nyu.cascade.util.TestUtils;
import edu.nyu.cascade.control.jaxb.ControlFile.Run;
import edu.nyu.cascade.control.jaxb.ControlFile.SourceFile;
import edu.nyu.cascade.control.jaxb.Position.Command;

public class ControlFileTest {
  private static final File programs_location = edu.nyu.cascade.control.ControlFileTest.programs_location;
  private static final File bad_programs_location = edu.nyu.cascade.control.ControlFileTest.bad_programs_location;

  private static final Schema SCHEMA = edu.nyu.cascade.control.ControlFile.SCHEMA;

  private void checkPosition(Position p) {
    assertNotNull("No FileID for Position", p.getFileId());
    assertNotNull("No LineNum for Position", p.getLine());
    List<Command> cmds = p.getCommand();
    for(Command c : cmds) {
      assertNotNull("No CascadeFunction for Command", c.getCascadeFunction());
      assertNotNull("No Argument for Command", c.getArgument());
    }
  }

  /**
   * Try to parse the program, given a filename
   * 
   * @param file
   */
  private void parseFromFile(File file) {
    System.out.println("Parsing: " + file);
    try {
      JAXBContext jc = JAXBContext.newInstance("edu.nyu.cascade.control.jaxb");
      Unmarshaller u = jc.createUnmarshaller();
      u.setSchema(SCHEMA);
      ControlFile cf = (ControlFile) u.unmarshal(file);
      /*
       * Validate that the ControlFile object has the expected fields populated:
       * 1) At least one SourceFile 2) At least one Run. 3) A Name and Id for
       * each SourceFile. 4) At least one Start/End Position for each Run 5) A
       * FileId and LineNum for each Position.
       */

      List<SourceFile> sfs = cf.getSourceFile();
      assertFalse("No SourceFile tags found in control file.", sfs == null
          || sfs.isEmpty());

      for (SourceFile sf : sfs) {
        assertNotNull("No Name for SourceFile", sf.getName());
        assertNotNull("No Id for SourceFile", sf.getId());
      }

      List<Run> runs = cf.getRun();
      assertFalse("No Run tags found in control file.", runs == null
          || runs.isEmpty());

      for (Run run : runs) {
        assertNotNull("null Run found in control file", run);
        Position sp = run.getStartPosition();
        Position ep = run.getEndPosition();
        assertNotNull("No StartPosition for Run", sp);
        assertNotNull("No EndPosition for Run", ep);
        checkPosition(sp);
        checkPosition(ep);
        for (Position wp : run.getWayPoint()) {
          checkPosition(wp);
        }
      }
    } catch (Throwable x) {
      fail(x.toString());
    }
  }

  @Test
  public void testPProgram() {
    // Make the control file filter
    FilenameFilter filter = new FilenameFilter() {
      public boolean accept(File dir, String name) {
        return name.endsWith(".ctrl");
      }
    };

    TestUtils.Tester<File> tester = new TestUtils.Tester<File>() {
      @Override
      public void runTest(File f) {
        parseFromFile(f);
      }
    };

    TestUtils.checkDirectory(programs_location, filter, tester, false);
    TestUtils.checkDirectory(bad_programs_location, filter, tester, true);
  }

}
