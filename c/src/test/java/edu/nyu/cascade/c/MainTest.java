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
  private static final File programs_test_location = new File(programs_c_location,
      "test");
  private static final File mini_programs_location = new File(programs_test_location,
      "mini_bnc");
  private static final File nec_programs_location = new File(programs_test_location,
      "nec_bnc");
  
//  private static final File smtFile_dump_location = new File(mini_programs_location,
//      "dump");
  
  private static final int Timeout = 10;
  
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
  
  private void runCascadeWithTimeout(final String... args) throws Exception {
    System.out.println("runCascade with timeout " + Timeout + "s: " + Joiner.on(";").join(args));
    TestUtils.callWithTimeout(new Runnable() {
      @Override
      public void run() {
        Preferences.clearAll();
        Main main = getInjector().getInstance(Main.class);
        main.init();
        List<String> files = main.processCommandLine(args);
        IOUtils.enableErr();
//        main.setErrStream(IOUtils.NULL_PRINT_STREAM);
//        main.setErrStream(System.err);
        try {
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
  
  private TestUtils.Tester<File> parserTestWithTimeout(final String... args) {
    return new TestUtils.Tester<File>() {
      @Override
      public void runTest(File f) {
        try {
          List<String> argList = Lists.newArrayList(args);
          argList.add(f.toString());
//          argList.add("--smt2-file");
//          File dumpFile = new File(smtFile_dump_location, f.getName().replaceFirst("ctrl", "cvc"));
//          argList.add(dumpFile.getAbsolutePath());
          runCascadeWithTimeout(argList.toArray(new String[0]));
        } catch (Throwable e) {
          throw new RuntimeException(e);
        }
      }
    };
  }
  
  private Void runCascadeTimeout(final String... args) 
  		throws IOException, ParseException, TheoremProverException {
  	System.out.println("runCascade: " + Joiner.on(";").join(args));
    Preferences.clearAll();
    Main main = getInjector().getInstance(Main.class);
    main.init();
    List<String> files = main.processCommandLine(args);
    IOUtils.enableErr();
    main.run(files);
    return null;
	}

	private TaskBuilder<File> parserTestTimeout(final String... args) {
    return new TaskBuilder<File>().setFunction(new Function<File, Void>() {
			@Override
      public Void apply(File file) {
				Preconditions.checkNotNull(file);
				List<String> argList = Lists.newArrayList(args);
				argList.add(file.toString());
        try {
	        runCascadeTimeout(argList.toArray(new String[0]));
        } catch (Exception e) {
	        IOUtils.err().println(e.getMessage());
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
      TestUtils.checkDirectory(programs_location, ctrlFileFilter,
			       parserTest("--dry-run", "--prover", "z3"), false);
      TestUtils.checkDirectory(programs_location, ctrlFileFilter,
			       parserTest("--dry-run", "--seq", "--prover", "z3"), false);
      TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter,
			       parserTest("--dry-run", "--prover", "z3"), false);
      TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter,
			       parserTest("--dry-run", "--seq", "--prover", "z3"), false);
  }
  
/*  private Map<Tester<File>, String[]> validOptMap() {
    Map<Tester<File>, String[]> optMap = Maps.newLinkedHashMap();
    Tester<File> mem_9 = parserTest("--unsigned", "--feasibility", "--mem-cell-size", "9", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_11 = parserTest("--unsigned", "--feasibility", "--mem-cell-size", "11", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_13 = parserTest("--unsigned", "--feasibility", "--mem-cell-size", "13", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sound = parserTest("--unsigned", "--feasibility", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> signed = parserTest("--feasibility", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> signed_mem_9 = parserTest("--feasibility", "--mem-cell-size", "9", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> signed_mem_11 = parserTest("--feasibility", "--mem-cell-size", "11", "--sound", "--prover", "z3", "--theory", "Partition");
    
    String[] mem_9_bnc = {"ex21-100.ctrl"};
    String[] mem_11_bnc = {"ex2-3.ctrl", "ex2-1024.ctrl", "ex9-3.ctrl" , "ex9-1024.ctrl"};
    String[] mem_13_bnc = {"ex23-36.ctrl"};
    String[] sound_bnc = {"ex5.ctrl", "ex6.ctrl", "ex7-3.ctrl", "ex7-200.ctrl", "ex10-3.ctrl", 
        "ex10-17.ctrl", "ex11.ctrl", "ex15.ctrl", "ex17.ctrl", "ex18-10.ctrl", "ex18-100.ctrl", "ex31-7.ctrl",
        "ex34.ctrl", "ex40-3.ctrl", "ex49-3.ctrl", "inf6a.ctrl", "inf6b.ctrl", "inf8a.ctrl",
        "inf8b.ctrl"};
    String[] signed_bnc = {"ex14-10.ctrl"};
    String[] signed_mem_9_bnc = {"ex22-50.ctrl"};
    String[] signed_mem_11_bnc = {"ex32-1000.ctrl"};
    
    optMap.put(signed, signed_bnc);
    optMap.put(signed_mem_9, signed_mem_9_bnc);
    optMap.put(signed_mem_11, signed_mem_11_bnc);
    optMap.put(sound, sound_bnc);
    optMap.put(mem_9, mem_9_bnc);
    optMap.put(mem_13, mem_13_bnc);
    optMap.put(mem_11, mem_11_bnc);
    
    return optMap;
  }
  
  private Map<Tester<File>, String[]> invalidOptMap() {
    Map<Tester<File>, String[]> optMap = Maps.newLinkedHashMap();
    Tester<File> sgn_mem_9 = parserTest("--mem-cell-size", "9", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn_mem_11 = parserTest("--mem-cell-size", "11", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_9 = parserTest("--mem-cell-size", "9", "--sound", "--unsigned", "--prover", "z3", "--theory", "Partition");
    Tester<File> sound = parserTest("--sound", "--unsigned", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn = parserTest("--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> fea_sgn = parserTest("--feasibility", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> fea_mem_10 = parserTest("--feasibility", "--mem-cell-size", "10", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> fea_mem_11 = parserTest("--feasibility", "--mem-cell-size", "11", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    
    String[] sgn_mem_9_bnc = {"ex27-200.ctrl"};
    String[] sgn_mem_11_bnc = {"ex20-1.ctrl", "ex20-1024.ctrl"};
    String[] mem_9_bnc = {"ex41-3.ctrl", "ex26-200.ctrl"};
    String[] sound_bnc = {"ex3-10.ctrl", "ex4-10.ctrl", "ex8.ctrl", "ex12-10.ctrl", "ex30.ctrl", 
        "ex43.ctrl", "ex46-3.ctrl", "ex47-2.ctrl", "inf1.ctrl", "inf5.ctrl"};
    String[] sgn_bnc = {"ex13.ctrl", "ex37.ctrl", "inf2.ctrl", "inf4.ctrl"};
    String[] fea_sgn_bnc = {"ex16-4.ctrl", "ex19-3.ctrl", "ex39-3.ctrl"};
    String[] fea_mem_10_bnc = {"ex25-3.ctrl"};
    String[] fea_mem_11_bnc = {"ex1-3.ctrl", "ex1-512.ctrl"};
    
    optMap.put(sgn, sgn_bnc);
    optMap.put(sound, sound_bnc);
    optMap.put(mem_9, mem_9_bnc);
    optMap.put(sgn_mem_9, sgn_mem_9_bnc);
    optMap.put(sgn_mem_11, sgn_mem_11_bnc);
    optMap.put(fea_sgn, fea_sgn_bnc);
    optMap.put(fea_mem_10, fea_mem_10_bnc);
    optMap.put(fea_mem_11, fea_mem_11_bnc);
    
    return optMap;
  }
  
  private Map<Tester<File>, String[]> invValidOptMap() {
    Map<Tester<File>, String[]> optMap = Maps.newLinkedHashMap();
    Tester<File> mem_11 = parserTest("--feasibility", "--mem-cell-size", "11", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_9 = parserTest("--feasibility", "--mem-cell-size", "9", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_13 = parserTest("--feasibility", "--mem-cell-size", "13", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sound = parserTest("--feasibility", "--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn = parserTest("--feasibility", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn_mem_11 = parserTest("--feasibility", "--mem-cell-size", "11", "--sound", "--prover", "z3", "--theory", "Partition");
    
    String[] mem_11_bnc = {"ex1-inv.ctrl", "ex2-inv.ctrl", "ex9-inv.ctrl"};
    String[] mem_9_bnc = {"ex21-inv.ctrl"};
    String[] mem_13_bnc = {"ex23-inv.ctrl"};
    String[] sound_bnc = {"ex7-inv.ctrl", "ex10-inv.ctrl", "ex17-inv.ctrl", "ex18-inv.ctrl", "ex31-inv.ctrl"};
    String[] sgn_bnc = {"ex14-inv.ctrl"};
    String[] sgn_mem_11_bnc = {"ex32-inv.ctrl"};
    
    optMap.put(sgn, sgn_bnc);
    optMap.put(sound, sound_bnc);
    optMap.put(mem_13, mem_13_bnc);
    optMap.put(mem_11, mem_11_bnc);
    optMap.put(sgn_mem_11, sgn_mem_11_bnc);
    optMap.put(mem_9, mem_9_bnc);
    
    return optMap;
  }
  
  private Map<Tester<File>, String[]> invInvalidOptMap() {
    Map<Tester<File>, String[]> optMap = Maps.newLinkedHashMap();
    Tester<File> sgn_mem_11 = parserTest("--mem-cell-size", "11", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> mem_9 = parserTest("--unsigned", "--mem-cell-size", "9", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sound = parserTest("--unsigned", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn = parserTest("--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> fea_sgn = parserTest("--feasibility", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> fea_mem_10 = parserTest("--unsigned", "--feasibility", "--mem-cell-size", "10", "--sound", "--prover", "z3", "--theory", "Partition");
    Tester<File> sgn_mem_9 = parserTest("--mem-cell-size", "9", "--sound", "--prover", "z3", "--theory", "Partition");
    
    String[] fea_sgn_bnc = {"ex16-inv.ctrl"};
    String[] sgn_mem_9_bnc = {"ex22-inv.ctrl", "ex27-inv.ctrl"};
    String[] fea_mem_10_bnc = {"ex25-inv.ctrl"};
    String[] sgn_mem_11_bnc = {"ex19-inv.ctrl", "ex20-inv.ctrl"};
    String[] mem_9_bnc = {"ex26-inv.ctrl", "ex41-inv.ctrl"};
    String[] sound_bnc = {"ex3-inv.ctrl", "ex4-inv.ctrl", "ex8-inv.ctrl", "ex12-inv.ctrl", 
        "ex40-inv.ctrl", "ex43-inv.ctrl",  "ex46-inv.ctrl", "ex47-inv.ctrl", "ex49-inv.ctrl"};
    String[] sgn_bnc = {"ex39-inv.ctrl"};
    
    
    optMap.put(sound, sound_bnc);
    optMap.put(sgn, sgn_bnc);
    optMap.put(mem_9, mem_9_bnc);
    optMap.put(sgn_mem_9, sgn_mem_9_bnc);
    optMap.put(sgn_mem_11, sgn_mem_11_bnc);
    optMap.put(fea_sgn, fea_sgn_bnc);
    optMap.put(fea_mem_10, fea_mem_10_bnc);
    
    return optMap;
  }
  
  @Test
  @Ignore
  public void testNecBenchmark() {
    final File valid_nec_location = new File(nec_programs_location, "valid");
    TestUtils.checkFile(valid_nec_location, validOptMap(), false);
    final File invalid_nec_location = new File(nec_programs_location, "invalid");
    TestUtils.checkFile(invalid_nec_location, invalidOptMap(), false);
    final File inv_valid_nec_location = new File(nec_programs_location, "inv-valid");
    TestUtils.checkFile(inv_valid_nec_location, invValidOptMap(), false);
    final File inv_invalid_nec_location = new File(nec_programs_location, "inv-invalid");
    TestUtils.checkFile(inv_invalid_nec_location, invInvalidOptMap(), false);
  }*/
  
  @Test
  public void testMiniBenchmark() {
  	final Tester<File> FlatTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Flat");
  	final Tester<File> BurstallTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Burstall");
  	final Tester<File> PartitionTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Partition");
  	
  	final Tester<File> FlatSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Flat");
  	final Tester<File> BurstallSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Burstall");
  	final Tester<File> PartitionSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Partition");
  	
  	final Tester<File> FlatOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Flat");
  	final Tester<File> BurstallOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Burstall");
  	final Tester<File> PartitionOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16",
  			"--theory", "Partition");
  	
  	final Tester<File> FlatSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Flat");
  	final Tester<File> BurstallSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Burstall");
  	final Tester<File> PartitionSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync",
  			"--theory", "Partition");
  	
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionTester, false);
    
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatSyncTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallSyncTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionSyncTester, false);
  	
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionOrderTester, false);
    
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatSyncOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallSyncOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionSyncOrderTester, false);
  }
  
  @Test
  @Ignore("It takes too long")
  public void testMiniBenchmarkMultiCell() {
  	final Tester<File> FlatMultiCellTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell", 
  			"--theory", "Flat");
  	final Tester<File> BurstallMultiCellTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell",
  			"--theory", "Burstall");
  	final Tester<File> PartitionMultiCellTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell",
  			"--theory", "Partition");
  	
  	final Tester<File> FlatMultiCellSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Flat");
  	final Tester<File> BurstallMultiCellSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Burstall");
  	final Tester<File> PartitionMultiCellSyncTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Partition");
  	
  	
  	final Tester<File> FlatMultiCellOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell", 
  			"--theory", "Flat");
  	final Tester<File> BurstallMultiCellOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell",
  			"--theory", "Burstall");
  	final Tester<File> PartitionMultiCellOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell",
  			"--theory", "Partition");
  	
  	final Tester<File> FlatMultiCellSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Flat");
  	final Tester<File> BurstallMultiCellSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Burstall");
  	final Tester<File> PartitionMultiCellSyncOrderTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell", "--mem-encoding", "sync", 
  			"--theory", "Partition");
  	
  	final Tester<File> BurstallMultiCellSimpTester = parserTest(
  			"--feasibility", "--inline-anno", "--sound", "--prover", "z3", "--multi-cell", "--simp", 
  			"--theory", "Burstall");
  	final Tester<File> BurstallMultiCellOrderSimpTester = parserTest(
  			"--feasibility", "--inline-anno", "--order", "--prover", "z3", "--multi-cell", "--simp", 
  			"--theory", "Burstall");
  	
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellSimpTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellOrderSimpTester, false);
    
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatMultiCellTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionMultiCellTester, false);
    
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatMultiCellSyncTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellSyncTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionMultiCellSyncTester, false);
    
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatMultiCellOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionMultiCellOrderTester, false);
  	
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, FlatMultiCellSyncOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, BurstallMultiCellSyncOrderTester, false);
    TestUtils.checkDirectory(mini_programs_location, ctrlFileFilter, PartitionMultiCellSyncOrderTester, false);
  }

	@Test
  @Ignore("It takes too long")
  public void testNecBenchmark() {
  	final Tester<File> FlatTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Flat");
  	final Tester<File> BurstallTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Burstall");
  	final Tester<File> PartitionTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Partition");
  	
  	final Tester<File> FlatSyncTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync", "--theory", "Flat");
  	final Tester<File> BurstallSyncTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync", "--theory", "Burstall");
  	final Tester<File> PartitionSyncTester = parserTestWithTimeout("--sound", 
  			"--prover", "z3", "--mem-cell-size", "16", "--mem-encoding", "sync", "--theory", "Partition");
  	
  	final Tester<File> FlatMultiCellTester = parserTestWithTimeout("--sound", "--dry-run",
  			"--prover", "z3", "--multi-cell", "--theory", "Flat");
  	final Tester<File> BurstallMultiCellTester = parserTestWithTimeout("--sound", "--dry-run",
  			"--prover", "z3", "--multi-cell", "--theory", "Burstall");
  	final Tester<File> PartitionMultiCellTester = parserTestWithTimeout("--sound", "--dry-run",
  			"--prover", "z3", "--multi-cell", "--theory", "Partition");
  	
  	final File valid_nec_location = new File(nec_programs_location, "valid");
    final File invalid_nec_location = new File(nec_programs_location, "invalid");
    final File inv_valid_nec_location = new File(nec_programs_location, "inv-valid");
    final File inv_invalid_nec_location = new File(nec_programs_location, "inv-invalid");
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, FlatTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, FlatTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, FlatTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, FlatTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, BurstallTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, BurstallTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, BurstallTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, BurstallTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, PartitionTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, PartitionTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, PartitionTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, PartitionTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, FlatSyncTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, FlatSyncTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, FlatSyncTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, FlatSyncTester, false);

    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, BurstallSyncTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, BurstallSyncTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, BurstallSyncTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, BurstallSyncTester, false);
   
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, PartitionSyncTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, PartitionSyncTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, PartitionSyncTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, PartitionSyncTester, false); 
   
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, FlatMultiCellTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, FlatMultiCellTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, FlatMultiCellTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, FlatMultiCellTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, BurstallMultiCellTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, BurstallMultiCellTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, BurstallMultiCellTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, BurstallMultiCellTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, PartitionMultiCellTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, PartitionMultiCellTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, PartitionMultiCellTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, PartitionMultiCellTester, false);
  }
  
  @Test
  @Ignore("It takes too long.")
  public void testNecBenchmarkDry() {
  	final File valid_nec_location = new File(nec_programs_location, "valid");
    final File invalid_nec_location = new File(nec_programs_location, "invalid");
    final File inv_valid_nec_location = new File(nec_programs_location, "inv-valid");
    final File inv_invalid_nec_location = new File(nec_programs_location, "inv-invalid");
    
  	final Tester<File> FlatSoundTester = parserTestWithTimeout("--sound", "--dry-run", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Flat");
  	final Tester<File> BurstallSoundTester = parserTestWithTimeout("--sound", "--dry-run", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Burstall");
  	final Tester<File> PartitionSoundTester = parserTestWithTimeout("--sound", "--dry-run",
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Partition");
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, FlatSoundTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, FlatSoundTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, FlatSoundTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, FlatSoundTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, BurstallSoundTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, BurstallSoundTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, BurstallSoundTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, BurstallSoundTester, false);
    
    TestUtils.checkDirectory(valid_nec_location, ctrlFileFilter, PartitionSoundTester, false);
    TestUtils.checkDirectory(invalid_nec_location, ctrlFileFilter, PartitionSoundTester, false);
    TestUtils.checkDirectory(inv_valid_nec_location, ctrlFileFilter, PartitionSoundTester, false);
    TestUtils.checkDirectory(inv_invalid_nec_location, ctrlFileFilter, PartitionSoundTester, false);
  }
  
  
  @Test
  @Ignore
  public void testNecBenchmarkDryTimeout() {
  	final File valid_nec_location = new File(nec_programs_location, "valid");
    final File invalid_nec_location = new File(nec_programs_location, "invalid");
    final File inv_valid_nec_location = new File(nec_programs_location, "inv-valid");
    final File inv_invalid_nec_location = new File(nec_programs_location, "inv-invalid");
    
  	final TaskBuilder<File> FlatSoundTester = parserTestTimeout("--sound", "--dry-run", 
  			"--prover", "z3", "--mem-cell-size", "16", "--theory", "Flat");
    
  	final TestTimeoutUtils.Scheduler scheduler = new TestTimeoutUtils.Scheduler(Timeout);
  	
    TestTimeoutUtils.checkDirectory(scheduler, valid_nec_location, ctrlFileFilter, FlatSoundTester);
    TestTimeoutUtils.checkDirectory(scheduler, invalid_nec_location, ctrlFileFilter, FlatSoundTester);
    TestTimeoutUtils.checkDirectory(scheduler, inv_valid_nec_location, ctrlFileFilter, FlatSoundTester);
    TestTimeoutUtils.checkDirectory(scheduler, inv_invalid_nec_location, ctrlFileFilter, FlatSoundTester);
    
    scheduler.run();
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
