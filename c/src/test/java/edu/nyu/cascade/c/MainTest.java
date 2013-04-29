package edu.nyu.cascade.c;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.Callable;

import org.junit.Test;

import xtc.parser.ParseException;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.util.TestUtils.ExitException;
import edu.nyu.cascade.util.TestUtils;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

public class MainTest {
  private static final File programs_location = FileUtils
      .absoluteResourcePath("syntax");
  private static final File programs_c_location = FileUtils
      .absoluteResourcePath("c");
  private static final File bad_programs_location = new File(programs_location,
      "bad");
  private static final File programs_test_location = new File(programs_c_location,
      "test");
  private static final File mini_programs_location = new File(programs_test_location,
      "minicase_bug");
//  private static final File nec_programs_location = new File(programs_test_location,
//      "testcase_nec");
  private static final FilenameFilter cFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".c");
    }
  };
  private static final FilenameFilter ctrlFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".ctrl");
    }
  };
  private static final FilenameFilter propFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".properties");
    }
  };
  private void runCascade(final String... args) throws Exception {
    System.out.println("runCascade: " + Joiner.on(";").join(args));
    TestUtils.callMayExit(new Callable<Void>() {
      @Override
      public Void call() throws Exception {
        Preferences.clearAll();
        Main main = getInjector().getInstance(Main.class);
        main.setOutStream(IOUtils.NULL_PRINT_STREAM);
        main.setErrStream(System.err);
        main.run(args);
        return null;
      }
    });
    /*
     * new Thread() {
     * 
     * @Override public void run() { try { Cascade.main(args); } catch
     * (IOException e) { // TODO Auto-generated catch block e.printStackTrace();
     * } catch (ParseException e) { // TODO Auto-generated catch block
     * e.printStackTrace(); } }
     * 
     * }.start();
     */}

  private TestUtils.Tester<File> parserTest(final String... args) {
    return new TestUtils.Tester<File>() {
      @Override
      public void runTest(File f) {
        try {
          List<String> argList = Lists.newArrayList(args);
          argList.add(f.toString());
          runCascade(argList.toArray(new String[0]));
        } catch (ParseException e) {
          throw new AssertionError(e);
        } catch (Throwable e) {
          throw new RuntimeException(e);
        }
      }
    };
  }

  /**
   * Try to parse the program, given a filename
   * 
   * @param filename
   * @throws ParseException
   * @throws IOException
   * @throws Exception
   * @throws
   * @throws InterruptedException
   */
  /*
   * private void parseProgramFromFile(File file,String... args) throws
   * IOException, ParseException { System.out.print("Parsing " + file +
   * " ... "); Cascade.main(new String[] { "-parseC", file.toString() });
   * Cascade.main(new String[] { "-parseC", "-noThreads", file.toString() }); }
   */
  @Test(expected = ExitException.class)
  public void testHelp() throws Exception {
    runCascade(new String[] { "--help" });
  }

  @Test(expected = ExitException.class)
  public void testVersion() throws Exception {
    runCascade(new String[] { "--version" });
  }

  @Test
  public void testPrograms() {
//    IOUtils.enableDebug();
    TestUtils.checkDirectory(programs_location, cFileFilter,
        parserTest("--parsec"), false);
  }

  @Test
  public void testProgramsNoThreads() {
    TestUtils.checkDirectory(programs_location, cFileFilter, parserTest(
        "--parsec", "--no-threads"), false);
  }

  @Test
  public void testBadPrograms() {
    TestUtils.checkDirectory(bad_programs_location, cFileFilter,
        parserTest("--parsec"), true);
  }

  @Test
  public void testBadProgramsNoThreads() {
    TestUtils.checkDirectory(bad_programs_location, cFileFilter, parserTest(
        "--parsec", "--no-threads"), true);
  }

  @Test
  public void testProperties() {
    TestUtils.checkDirectory(bad_programs_location, propFileFilter,
        parserTest("--prop"), true);
  }

  @Test
  public void testControlFiles() {
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--parse-only"), false);
  }
  
  @Test
  public void testDryRun() {
//    IOUtils.enableDebug();
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--dry-run", "--process", "seq"), false);
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--dry-run", "--process", "nonseq"), false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter,
        parserTest("--dry-run", "--process", "seq"), false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter,
        parserTest("--dry-run", "--process", "nonseq"), false);
//    TestUtils.checkDirectory(nec_programs_location, ctrlFileFilter, 
//        parserTest("--dry-run", "--process", "seq"), false);
//    TestUtils.checkDirectory(nec_programs_location, ctrlFileFilter, 
//        parserTest("--dry-run", "--process", "nonseq"), false);
  }

  /** FIXME: This is really a test for tp-tp */
  @Test
  public void testLogTp() {
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--parse-only", "--prover", "cvc4", "--cvc4-log", "foo.cvc"), false);
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--parse-only", "--prover", "z3", "--z3-log", "foo.cvc"), false);
  }  
}
