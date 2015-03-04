package edu.nyu.cascade.c;

import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FilenameFilter;
import java.io.Reader;
import java.net.URISyntaxException;

import org.junit.Test;

import xtc.lang.CParser;
import xtc.parser.ParseError;
import xtc.parser.Result;
import edu.nyu.cascade.util.FileUtils;

public class ParserTest {
  private static final String programs_path = "c";
  private static final File programs_dir = FileUtils
      .absoluteResourcePath(programs_path);

  /**
   * Try to parse the program, given a filename
   * 
   * @param filename
   */
  private void parseProgramFromFile(File file) {
    // System.out.print("Parsing " + filename + " ... ");

    // The reader for the files
    Reader in = null;
    try {

      // Create a new buffered file reader
      in = new BufferedReader(new FileReader(file));

      // Create a new parser for this file
      CParser p = new CParser(in, file.getPath(), (int) file.length());

      // Try to parse the program
      Result r = p.pTranslationUnit(0);

      // If parsed correctly, we're fine
      if (!r.hasValue()) {

        String parse_error = "Failed parsing Program :";

        // Get the error from the result
        ParseError err = (ParseError) r;

        // If error index is -1, we don't know the position
        if (-1 != err.index) {
          parse_error += p.location(err.index) + ": " + err.msg;
        }

        // Fail the test case with the parse error
        fail(parse_error);
      }

    } catch (Throwable x) {
      fail(x.toString());
    } finally {
      try {
        in.close();
      } catch (Throwable x) {
        fail(x.toString());
      }
    }

    // System.out.println("OK");
  }

  @Test
  public void testPProgram() throws URISyntaxException {

    // Create the directory object

    // Make the C files filter
    FilenameFilter filter = new FilenameFilter() {
      public boolean accept(File dir, String name) {
        return name.endsWith(".c");
      }
    };

    // Get all C files
    String[] c_tests = programs_dir.list(filter);

    if (c_tests == null) {
      fail("No test cases found in directory: " + programs_path);
    } else {
      for (int i = 0; i < c_tests.length; i++) {
        parseProgramFromFile(new File(programs_dir, c_tests[i]));
      }
    }
  }

}
