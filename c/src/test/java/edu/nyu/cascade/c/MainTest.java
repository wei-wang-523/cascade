package edu.nyu.cascade.c;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;

import java.io.File;
import java.io.FilenameFilter;
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
  private static final File syntax_location = FileUtils
      .absoluteResourcePath("syntax");
  private static final File bad_programs_location = new File(syntax_location,
      "bad");
  
  private static final FilenameFilter cFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".c");
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
        main.init();
        List<String> files = main.processCommandLine(args);
        main.setOutStream(System.out);
        main.setErrStream(IOUtils.NULL_PRINT_STREAM);
        main.run(files);
        return null;
      }
    });
  }
  
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
    TestUtils.checkDirectory(syntax_location, cFileFilter,
    		parserTest("--parsec"), false);
  }

  @Test
  public void testProgramsNoThreads() {
    TestUtils.checkDirectory(syntax_location, cFileFilter, parserTest(
        "--parsec", "--no-threads"), false);
  }

  @Test
  public void testBadPrograms() {
    TestUtils.checkDirectory(bad_programs_location, cFileFilter,
    		parserTest("--parsec"), true);
  }

  @Test
  public void testBadProgramsNoThreads() {
    TestUtils.checkDirectory(bad_programs_location, cFileFilter, 
    		parserTest("--parsec", "--no-threads"), true);
  }

  @Test
  public void testProperties() {
    TestUtils.checkDirectory(bad_programs_location, propFileFilter,
    		parserTest("--prop"), true);
  }
}
