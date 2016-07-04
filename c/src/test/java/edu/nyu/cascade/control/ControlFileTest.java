package edu.nyu.cascade.control;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FilenameFilter;
import java.util.List;

import org.junit.Test;

import edu.nyu.cascade.util.TestUtils;
import edu.nyu.cascade.control.ControlFile;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.util.FileUtils;

public class ControlFileTest {
	public static final File programs_location = FileUtils.absoluteResourcePath(
	    "syntax");
	public static final File bad_programs_location = FileUtils.filePath(
	    programs_location, "bad");

	private void checkPosition(Position p) {
		assertNotNull("No File for Position", p.getFile());
		assertNotNull("No LineNum for Position", p.getLine());
		List<Command> cmds = p.getCommands();
		for (Command c : cmds) {
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
		// System.out.print("Parsing " + file + " ... ");
		try {
			ControlFile cf = ControlFile.fromXml(file);
			/*
			 * Validate that the ControlFile object has the expected fields populated:
			 * 1) At least one source File 2) At least one Run. 4) At least one
			 * Start/End Position for each Run 5) A File and LineNum for each
			 * Position.
			 */

			List<File> sfs = cf.getSourceFiles();
			assertFalse("No source files in control file.", sfs == null || sfs
			    .isEmpty());

			for (File sf : sfs) {
				assertNotNull(sf);
				assertTrue("file " + sf.getAbsolutePath() + " does not exist", sf
				    .exists());
			}

			// for( TheoryId theory : cf.getTheories() ) {
			TheoryId theory = cf.getTheoryId();
			if (theory != null) {
				// assertNotNull( theory );
				try {
					Class.forName(theory.getQname());
				} catch (ClassNotFoundException e) {
					fail("Theory definition not found: " + theory.getQname());
				}
			}

			List<Run> runs = cf.getRuns();
			assertFalse("No runs in control file.", runs == null || runs.isEmpty());

			for (Run run : runs) {
				assertNotNull("null Run found in control file", run);
				Position sp = run.getStartPosition();
				Position ep = run.getEndPosition();
				assertNotNull("No start position for Run", sp);
				assertNotNull("No end position for Run", ep);
				checkPosition(sp);
				checkPosition(ep);
				for (Position wp : run.getWayPoints()) {
					checkPosition(wp);
				}
			}
		} catch (ControlFileException e) {
			fail(e.getMessage());
			// fail(x.toString());
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
