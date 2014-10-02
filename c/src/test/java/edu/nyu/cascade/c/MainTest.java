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

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.util.TestTimeoutUtils;
import edu.nyu.cascade.util.TestTimeoutUtils.TaskBuilder;
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
  
//  private static final File smtFile_dump_location = new File(mini_programs_location,
//      "dump");
  
  private static final int Timeout = 20;
  
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
        main.init();
        List<String> files = main.processCommandLine(args);
        main.setOutStream(IOUtils.NULL_PRINT_STREAM);
        main.setErrStream(System.err);
        main.setStatsStream(System.err);
        main.run(files);
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
  
  private void runCascadeTO(final String... args) throws Exception {
    System.out.println("runCascade with timeout " + Timeout + "s: " + Joiner.on(";").join(args));
    TestUtils.callWithTimeout(new Runnable() {
      @Override
      public void run() {
        Preferences.clearAll();
        try {
          Main main = getInjector().getInstance(Main.class);
          main.init();
          List<String> files = main.processCommandLine(args);
          main.setOutStream(IOUtils.NULL_PRINT_STREAM);
          main.setErrStream(System.err);
        	IOUtils.enableErr();
					main.run(files);
				} catch (TheoremProverException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (ParseException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
      }
    }, Timeout);
  }
  
  private Void runCascadeTOTask(final String... args) 
  		throws IOException, ParseException, TheoremProverException {
  	System.out.println("runCascade: " + Joiner.on(";").join(args));
    Preferences.clearAll();
    Main main = getInjector().getInstance(Main.class);
    main.init();
    List<String> files = main.processCommandLine(args);
    main.run(files);
    return null;
	}
  
  private TestUtils.Tester<File> parserTest(final String... args) {
    return new TestUtils.Tester<File>() {
      @Override
      public void runTest(File f) {
        try {
          List<String> argList = Lists.newArrayList(args);
          argList.add(f.toString());
//          argList.add("--smt2-file");
//          File dumpFile = new File(smtFile_dump_location, f.getName().replaceFirst("ctrl", "cvc"));
//          argList.add(dumpFile.getAbsolutePath());
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

	private TaskBuilder<File> parserTestTimeoutTask(final String... args) {
    return new TaskBuilder<File>().setFunction(new Function<File, Void>() {
			@Override
      public Void apply(File file) {
				Preconditions.checkNotNull(file);
				List<String> argList = Lists.newArrayList(args);
				argList.add(file.toString());
        try {
	        runCascadeTOTask(argList.toArray(new String[0]));
        } catch (Exception e) {
	        IOUtils.err().println("[WARNING] " + e.getMessage());
        }
        return null;
      }
    });
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
  public void testControlFiles() {
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
    		parserTest("--parse-only"), false);
  }
  
  @Test
  public void testDryRun() {
  	TestUtils.checkDirectory(programs_location, ctrlFileFilter,
  			parserTest("--dry-run"), false);
  	TestUtils.checkDirectory(programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--seq"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--mode", "Partition"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--lambda"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--mode", "Partition", "--lambda"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--multi-cell"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--multi-cell", "--mode", "Partition"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--multi-cell", "--lambda"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--multi-cell", "--mode", "Partition", "--lambda"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--mode", "Partition", 
  					"-fs", "--vari-cell"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--seq"), false);
  }

    @Test
	@Ignore
	public void testDryRunPathBased() {
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--path-based"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--path-based", "--mode", "Partition"), false);
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--path-based", "--lambda"), false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter,
  			parserTest("--dry-run", "--path-based", "--mode", "Partition", "--lambda"), false);	
    }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithFlat() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Flat");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Flat",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--mode", "Flat");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
	public void testMiniBenchmarkWithBurstall() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Burstall");  	
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Burstall",
				"--mem-encoding", "sync");  	
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--mode", "Burstall");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore
	public void testMiniBenchmarkWithPartition() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Partition");
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Partition",
				"--mem-encoding", "sync");
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--mode", "Partition");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}
	
	@Test
  @Ignore
	public void testMiniBenchmarkWithFSPartition() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", 
				"--mode", "Partition", "--fs");
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", 
				"--mode", "Partition", "--fs",
				"--mem-encoding", "sync");
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", 
				"--mode", "Partition", "--fs");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}
	
	@Test
  @Ignore
	public void testMiniBenchmarkWithFSCSPartition() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", 
				"--mode", "Partition", "--fs", "--cs");
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", 
				"--mode", "Partition", "--fs", "--cs",
				"--mem-encoding", "sync");
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", 
				"--mode", "Partition", "--fs", "--cs");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore
  public void testMiniBenchmarkPathBasedWithFlat() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Flat");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Flat");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Flat");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkPathBasedWithLambdaFlat() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Flat", "--lambda");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Flat", "--lambda");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Flat", "--lambda");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkPathBasedWithLambdaBurstall() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Burstall", "--lambda");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Burstall", "--lambda");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Burstall", "--lambda");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkPathBasedWithLambdaPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Partition", "--lambda");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Partition", "--lambda");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Partition", "--lambda");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkPathBasedWithLambdaFSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Partition", "--fs", "--lambda");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Partition", "--fs", "--lambda");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Partition", "--fs", "--lambda");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkPathBasedWithLambdaFSCSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mode", "Partition", "--fs", "--cs", "--lambda");
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--path-based",
  			"--mem-encoding", "sync", 
  			"--mode", "Partition", "--fs", "--cs", "--lambda");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--path-based",
  			"--mode", "Partition", "--fs", "--cs", "--lambda");
  	
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
  	TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
	public void testMiniBenchmarkWithLambdaFlat() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Flat", "--lambda");  	
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--mode", "Flat", "--lambda",
				"--mem-encoding", "sync");  	
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--mode", "Flat", "--lambda");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore
  public void testMiniBenchmarkWithLambdaBurstall() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Burstall", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Burstall", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--mode", "Burstall", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Partition", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--mode", "Partition", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--mode", "Partition", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaFSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", 
  			"--mode", "Partition", "--fs", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", 
  			"--mode", "Partition", "--fs", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", 
  			"--mode", "Partition", "--fs", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaFSCSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", 
  			"--mode", "Partition", "--fs", "--cs", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", 
  			"--mode", "Partition", "--fs", "--cs", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", 
  			"--mode", "Partition", "--fs", "--cs", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithFlatMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell", 
  			"--mode", "Flat"); 	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell", "--mem-encoding", "sync", 
  			"--mode", "Flat");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--multi-cell", 
  			"--mode", "Flat");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithBurstallMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell", 
  			"--mode", "Burstall"); 	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell", 
  			"--mem-encoding", "sync", 
  			"--mode", "Burstall");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--multi-cell", 
  			"--mode", "Burstall");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore("It takes too long.")
	public void testMiniBenchmarkWithPartitionMultiCell() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--multi-cell", 
				"--mode", "Partition"); 	
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--multi-cell", 
				"--mem-encoding", "sync", 
				"--mode", "Partition");  	
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--multi-cell", 
				"--mode", "Partition");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}
  
	@Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithFlatVariCell() {
  	final Tester<File> soundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell", 
  			"--mode", "Flat");
  	final Tester<File> orderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell", 
  			"--mode", "Flat");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, soundTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, orderTester, false);
  }

	@Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithBurstallVariCell() {
  	final Tester<File> soundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell", 
  			"--mode", "Burstall");
  	final Tester<File> orderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell", 
  			"--mode", "Burstall");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, soundTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, orderTester, false);
  }
	
	@Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithPartitionVariCell() {
  	final Tester<File> soundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell", 
  			"--mode", "Partition");
  	final Tester<File> orderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell", 
  			"--mode", "Partition");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, soundTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, orderTester, false);
  }
	
	@Test
  @Ignore("It takes too long.")
  public void testMiniBenchmarkWithFSPartitionVariCell() {
  	final Tester<File> soundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell", 
  			"--mode", "Partition", "--fs");
  	final Tester<File> orderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell", 
  			"--mode", "Partition", "--fs");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, soundTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, orderTester, false);
  }
	
	@Test
	@Ignore("It takes too long.")
	public void testMiniBenchmarkWithFSCSPartitionVariCell() {
		final Tester<File> soundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--vari-cell", 
				"--mode", "Partition", "--fs", "--cs");
		final Tester<File> orderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--vari-cell", 
				"--mode", "Partition", "--fs", "--ce");
		
		TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, soundTester, false);
		TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, orderTester, false);	
	}
	
  @Test
  @Ignore
	public void testMiniBenchmarkWithLambdaFlatMultiCell() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--multi-cell",
				 "--mode", "Flat", "--lambda");  	
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--multi-cell",
				 "--mode", "Flat", "--lambda",
				"--mem-encoding", "sync");  	
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--multi-cell",
				 "--mode", "Flat", "--lambda");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore
  public void testMiniBenchmarkWithLambdaBurstallMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Burstall", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Burstall", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--multi-cell",
  			 "--mode", "Burstall", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaPartitionMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Partition", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Partition", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--multi-cell",
  			 "--mode", "Partition", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaFSPartitionMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Partition", "--fs", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--multi-cell",
  			 "--mode", "Partition", "--fs", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--multi-cell",
  			 "--mode", "Partition", "--fs", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
	public void testMiniBenchmarkWithLambdaFlatVariCell() {
		final Tester<File> SoundTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--vari-cell",
				 "--mode", "Flat", "--lambda");  	
		final Tester<File> SyncTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--sound", "--vari-cell",
				 "--mode", "Flat", "--lambda",
				"--mem-encoding", "sync");  	
		final Tester<File> OrderTester = parserTestTimeout(
				"--feasibility", "--inline-anno", "--order", "--vari-cell",
				 "--mode", "Flat", "--lambda");
		
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
	  TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore
  public void testMiniBenchmarkWithLambdaBurstallVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Burstall", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Burstall", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell",
  			 "--mode", "Burstall", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaPartitionVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Partition", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Partition", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell",
  			 "--mode", "Partition", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
  
  @Test
  @Ignore
  public void testMiniBenchmarkWithLambdaFSPartitionVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Partition", "--fs", "--lambda");  	
  	final Tester<File> SyncTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--sound", "--vari-cell",
  			 "--mode", "Partition", "--fs", "--lambda",
  			"--mem-encoding", "sync");  	
  	final Tester<File> OrderTester = parserTestTimeout(
  			"--feasibility", "--inline-anno", "--order", "--vari-cell",
  			 "--mode", "Partition", "--fs", "--lambda");
  	
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SoundTester, false);    
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(mini_programs_location, ctrlFileFilter, OrderTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
	public void testNecInlineBenchmarkWithFlat() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", "--inline-anno",
				 
				"--mode", "Flat");
		final Tester<File> SyncTester = parserTestTimeout("--sound", "--inline-anno",
				 "--mem-encoding", "sync", 
				"--mode", "Flat");
		final Tester<File> OrderTester = parserTestTimeout("--order", "--inline-anno",
				 
				"--mode", "Flat");
		
    TestUtils.checkDirectoryRec(nec_inline_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_inline_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_inline_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithFlat() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound",
  			 "--mode", "Flat");
  	final Tester<File> SyncTester = parserTestTimeout("--sound",
  			 "--mem-encoding", "sync", "--mode", "Flat");
  	final Tester<File> OrderTester = parserTestTimeout("--order",
  			 "--mode", "Flat");
    
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, OrderTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithBurstall() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", 
				 "--mode", "Burstall");
		final Tester<File> SyncTester = parserTestTimeout("--sound", 
				 "--mem-encoding", "sync", "--mode", "Burstall");
		final Tester<File> OrderTester = parserTestTimeout("--order",
				 "--mode", "Burstall");
		
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithPartition() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", 
				 "--mode", "Partition");
		final Tester<File> SyncTester = parserTestTimeout("--sound", 
				 "--mem-encoding", "sync", "--mode", "Partition");
		final Tester<File> OrderTester = parserTestTimeout("--order",
				 "--mode", "Partition");
		
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, OrderTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithFSPartition() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", 
				 
				"--mode", "Partition", "--fs");
		final Tester<File> SyncTester = parserTestTimeout("--sound", 
				 "--mem-encoding", "sync", 
				"--mode", "Partition", "--fs");
		final Tester<File> OrderTester = parserTestTimeout("--order",
				 
				"--mode", "Partition", "--fs");
		
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, OrderTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithFSCSPartition() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", 
				 
				"--mode", "Partition", "--fs", "--cs");
		final Tester<File> SyncTester = parserTestTimeout("--sound", 
				 "--mem-encoding", "sync", 
				"--mode", "Partition", "--fs", "--cs");
		final Tester<File> OrderTester = parserTestTimeout("--order",
				 
				"--mode", "Partition", "--fs", "--cs");
		
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SyncTester, false);
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, OrderTester, false);
	}

	@Test
	@Ignore("It takes too long")
  public void testNecBenchmarkPathBasedWithFlat() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Flat");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
  public void testNecBenchmarkPathBasedWithLambdaFlat() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Flat", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
  public void testNecBenchmarkPathBasedWithLambdaBurstall() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Burstall", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkPathBasedWithLambdaPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Partition", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkPathBasedWithLambdaFSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Partition", "--fs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkPathBasedWithLambdaFSCSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--path-based",
  			 "--mode", "Partition", "--fs", "--cs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}

	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithLambdaFlat() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--mode", "Flat", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaBurstall() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", 
  			 "--mode", "Burstall", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", 
  			 "--mode", "Partition", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaFSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", 
  			 "--mode", "Partition", "--fs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaFSCSPartition() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", 
  			 "--mode", "Partition", "--fs", "--cs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithFlatMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound",
  			 "--multi-cell", "--mode", "Flat");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithBurstallMultiCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound",
  			 "--multi-cell", "--mode", "Burstall");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithPartitionMultiCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--multi-cell", "--mode", "Partition");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithFSPartitionMultiCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--multi-cell", "--mode", "Partition", "--fs");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithFSCSPartitionMultiCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--multi-cell", "--mode", "Partition", "--fs", "--cs");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithFlatVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--vari-cell", "--mode", "Flat");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }

	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithBurstallVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--vari-cell", "--mode", "Burstall");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithPartitionVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--vari-cell", "--mode", "Partition");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithFSPartitionVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--vari-cell", "--mode", "Partition", "--fs");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithFSCSPartitionVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound",
				 "--vari-cell", "--mode", "Partition", "--fs", "--cs");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
	@Ignore("It takes too long")
	public void testNecBenchmarkWithLambdaFlatVariCell() {
		final Tester<File> SoundTester = parserTestTimeout("--sound", "--vari-cell",
				 "--mode", "Flat", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
	}
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaBurstallVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--vari-cell",
  			 "--mode", "Burstall", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaPartitionVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--vari-cell",
  			 "--mode", "Partition", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaFSPartitionVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--vari-cell",
  			 "--mode", "Partition", "--fs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore("It takes too long")
  public void testNecBenchmarkWithLambdaFSCSPartitionVariCell() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--vari-cell",
  			 "--mode", "Partition", "--fs", "--cs", "--lambda");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }
	
	@Test
  @Ignore
  public void testNecBenchmarkDry() {
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--dry-run",
  			 "--mode", "Partition");
    TestUtils.checkDirectoryRec(nec_programs_location, ctrlFileFilter, SoundTester, false);
  }	
  
  @Test
  @Ignore
  public void testNecInlineBenchmarkDry() {    
  	final Tester<File> SoundTester = parserTestTimeout("--sound", "--dry-run", "--inline-anno",
  			 "--mode", "Partition");
    TestUtils.checkDirectoryRec(nec_inline_programs_location, ctrlFileFilter, SoundTester, false);
  }
  
  @Test
  @Ignore
  public void testNecBenchmarkDryTimeout() {    
  	final TaskBuilder<File> SoundTester = parserTestTimeoutTask("--sound", "--dry-run", 
  			 "--mode", "Flat");
    
  	final TestTimeoutUtils.Scheduler scheduler = new TestTimeoutUtils.Scheduler(Timeout);
    TestTimeoutUtils.checkDirectory(scheduler, nec_programs_location, ctrlFileFilter, SoundTester);
    scheduler.run();
  }
  
  /** FIXME: This is really a test for tp-tp */
  @Test
  public void testLogTp() {
      //    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
      //        parserTestWithTimeout("--parse-only", "--prover", "cvc4", "--cvc4-log", "foo.cvc"), false);
    TestUtils.checkDirectory(programs_location, ctrlFileFilter,
        parserTest("--parse-only", "--z3-log", "foo.cvc"), false);
  }  
}
