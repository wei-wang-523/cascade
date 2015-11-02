package edu.nyu.cascade.c;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.Callable;

import org.junit.Ignore;
import org.junit.Test;

import xtc.parser.ParseException;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.util.TestUtils.ExitException;
import edu.nyu.cascade.util.TestUtils;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.TestUtils.Tester;

public class MainTest {
  private static final File programs_location = FileUtils
      .absoluteResourcePath("syntax");
  private static final File programs_c_location = FileUtils
      .absoluteResourcePath("c");
  private static final File bad_programs_location = new File(programs_location,
      "bad");
  private static final File mini_programs_location = new File(programs_c_location,
      "mini_bnc");
  private static final File nec_programs_location = new File(programs_c_location,
      "nec_bnc");
  private static final File nec_inline_programs_location = new File(programs_c_location,
      "nec_inline_bnc");
  
  private static final File sv_programs_location = new File(System.getProperty("user.dir"),
      "../../benchmarks/sv_bnc");
  
  private static final FilenameFilter cFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".c");
    }
  };
  
  private static final FilenameFilter iFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith(".i");
    }
  };
  
  private static final FilenameFilter falseDerefFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith("_false-valid-deref.c");
    }
  };
  
  private static final FilenameFilter falseFreeFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith("_false-valid-free.c");
    }
  };
  
  private static final FilenameFilter falseMemtrackFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith("_false-valid-memtrack.c");
    }
  };
  
  private static final FilenameFilter falseAssertFileFilter = new FilenameFilter() {
    public boolean accept(File dir, String name) {
      return name.endsWith("_false-valid-assert.c");
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
        main.setOutStream(IOUtils.NULL_PRINT_STREAM);
        main.setErrStream(System.err);
        main.setStatsStream(System.err);
        main.run(files);
        return null;
      }
    });
  }
  
  private void runCascadeTO(final String... args) throws Exception {
    System.out.println("runCascade with timeout " + "20s: " + Joiner.on(";").join(args));
    TestUtils.callWithTimeout(new Runnable() {
      @Override
      public void run() {
        Preferences.clearAll();
        try {
          Main main = getInjector().getInstance(Main.class);
          main.init();
          List<String> files = main.processCommandLine(args);
          main.setOutStream(System.out);
          main.setErrStream(IOUtils.NULL_PRINT_STREAM);
        	IOUtils.enableOut();
					main.run(files);
				} catch (TheoremProverException e) {
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				} catch (ParseException e) {
					e.printStackTrace();
				}
      }
    }, 20);
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
  
  private TestUtils.Tester<File> parserTestTimeout(final String... args) {
    return new TestUtils.Tester<File>() {
      @Override
      public void runTest(File f) {
        try {
          List<String> argList = Lists.newArrayList(args);
          argList.add(f.toString());
          runCascadeTO(argList.toArray(new String[0]));
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
    TestUtils.checkDirectory(bad_programs_location, cFileFilter, 
    		parserTest("--parsec", "--no-threads"), true);
  }

  @Test
  public void testProperties() {
    TestUtils.checkDirectory(bad_programs_location, propFileFilter,
    		parserTest("--prop"), true);
  }
  
  @Test
  public void testDryRun() {
  	TestUtils.checkDirectory(programs_location, cFileFilter,
  			parserTest("--dry-run"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, cFileFilter,
  			parserTest("--dry-run", "--iter-times", "1"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, cFileFilter,
  			parserTest("--dry-run", "--iter-times", "1", "--lambda"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, cFileFilter,
  			parserTest("--dry-run", "--multi-cell", "--iter-times", "1"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, cFileFilter,
  			parserTest("--dry-run", "--multi-cell", "--iter-times", "1", "--lambda"), false);
  }
  
  @Test
  @Ignore
  public void testFieldSensitive() {
  	File invalid_programs_location = new File(mini_programs_location, "invalid");
  	File valid_programs_location = new File(mini_programs_location, "valid");
  	Tester<File> tester = parserTestTimeout("--inline-anno", "--iter-times", "10", "--vari-cell",
				"--lambda", "--memory-check", "--hoare", "--fs", "-m32");
  	
  	TestUtils.checkDirectoryRec(invalid_programs_location, cFileFilter, tester, false);
  	TestUtils.checkDirectoryRec(valid_programs_location, cFileFilter, tester, false);
  }
    
  @Test
  @Ignore
  public void testReachability() {
    File bv_programs_location = new File(sv_programs_location, "bitvector");
    File bv_reg_programs_location = new File(sv_programs_location, "bitvector-regression");
    
  	TestUtils.checkDirectoryRec(bv_programs_location, iFileFilter, 
  			parserTestTimeout("-r", "ERROR", 
  					"--multi-cell", "--iter-times", "10", "--function-inline", "2"), false);
  	TestUtils.checkDirectoryRec(bv_reg_programs_location, iFileFilter, 
  			parserTestTimeout("-r", "ERROR", 
  					"--multi-cell", "--iter-times", "10", "--function-inline", "2"), false);
  }
  
  @Test
  @Ignore
  public void testMemorySafety() {
    File memsafety_programs_location = new File(sv_programs_location, "memsafety");
    
  	TestUtils.checkDirectoryRec(memsafety_programs_location, iFileFilter, 
  			parserTestTimeout("--memory-check", "--lambda", "--hoare",
  					"--multi-cell", "--iter-times", "10", "--function-inline", "2"), false);
  }
  
  @Test
  @Ignore
  public void testNecBenchmarkDry() {
  	final Tester<File> SoundTester = parserTestTimeout("--dry-run");
    TestUtils.checkDirectoryRec(nec_programs_location, cFileFilter, SoundTester, false);
  }
  
  @Test
//  @Ignore
  public void testCFSMiniBenchmark() {
  	final Tester<File> SoundTester = parserTestTimeout("--inline-anno", "--iter-times", 
  			"10", "-m32", "--vari-cell", "--lambda", "--memory-check", "--hoare", "-cfs");
  	
  	File invalid_location = new File(mini_programs_location, "invalid");
  	File valid_location = new File(mini_programs_location, "valid");
  	
    TestUtils.checkDirectoryRec(invalid_location, falseDerefFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseFreeFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseMemtrackFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseAssertFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(valid_location, cFileFilter, SoundTester, false);
  }
  
  @Test
  //@Ignore
  public void testCFSCSMiniBenchmark() {
  	final Tester<File> SoundTester = parserTestTimeout("--inline-anno", "--iter-times", 
  			"10", "-m32", "--vari-cell", "--lambda", "--memory-check", "--hoare", "-cfscs");
  	
  	File invalid_location = new File(mini_programs_location, "invalid");
  	File valid_location = new File(mini_programs_location, "valid");
  	
    TestUtils.checkDirectoryRec(invalid_location, falseDerefFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseFreeFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseMemtrackFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(invalid_location, falseAssertFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(valid_location, cFileFilter, SoundTester, false);
  }
  
  @Test
  @Ignore
  public void testNecInlineBenchmarkDry() {    
  	final Tester<File> SoundTester = parserTestTimeout("--dry-run", "--inline-anno");
    TestUtils.checkDirectoryRec(nec_inline_programs_location, cFileFilter, SoundTester, false);
  }
}
