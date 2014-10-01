package edu.nyu.cascade.c;

import static com.google.inject.Guice.createInjector;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.PosixParser;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.util.Runtime;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.base.Stopwatch;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import com.google.inject.Inject;
import com.google.inject.Injector;

import edu.nyu.cascade.c.mode.AbstractMode;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.c.theory.Theory;
import edu.nyu.cascade.control.ControlFile;
import edu.nyu.cascade.control.ControlFileException;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.TheoryId;
import edu.nyu.cascade.datatypes.CompressedDomainNamesEncoding;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTableFactory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;
import edu.nyu.cascade.util.CascadeModule;
import edu.nyu.cascade.util.CommandTokenizer;
import edu.nyu.cascade.util.CommandTokenizer.ArgList;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.PipedInputProcess;
import edu.nyu.cascade.util.Preferences;

/**
 * The Cascade parser.
 * 
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 * @author <a href="mailto:wwang1109@cs.nyu.edu">Wei Wang</a>
 * 
 */
public class Main {

  private static final String C_PREPROCESSOR_TO_FILE = "cpp-o";
  private static final String C_PREPROCESSOR = "cpp";
  private static final String OPTION_VERSION_SHORT = "v";
  private static final String OPTION_HELP_SHORT = "h";
  private static final String OPTION_VERSION = "version";
  private static final String OPTION_HELP = "help";
  private static final String OPTION_PROPERTIES = "prop";
  private static final String OPTION_NO_THREADS = "no-threads";
  private static final String OPTION_PARSEC = "parsec";
  private static final String OPTION_PARSE_ONLY = "parse-only";
  private static final String OPTION_DRY_RUN = "dry-run";
  private static final String OPTION_DEBUG = "debug";
  private static final String OPTION_STATS = "stats";
  private static final String OPTION_EFFORT_LEVEL = "effort-level";
  private static final String OPTION_SOLVER_TIMEOUT = "solver-timeout";
  private static final String OPTION_FEASIBILITY = "feasibility";
  private static final String OPTION_SMT2_FILE = "smt2-file";
  private static final String OPTION_MARK_AST = "optionMarkAST";
  private static final String OPTION_PEDANTIC = "pedantic";
  private static final String OPTION_INTERNAL_PEDANTIC = "optionPedantic";
  private static final String OPTION_REACHABILITY = "reachability";  

  @SuppressWarnings("static-access")
  private static final Options options = new Options() //
      .addOption(OPTION_HELP_SHORT, OPTION_HELP, false, //
          "Print usage information") //
      .addOption(OPTION_VERSION_SHORT, OPTION_VERSION, false, //
          "Print version and exit") // 
      .addOption(OptionBuilder.withLongOpt(OPTION_PROPERTIES) //
          .hasArg() //
          .withArgName("FILE") //
          .withType(File.class) //
          .withDescription("Specify a user properties file").create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_REACHABILITY) //
          .hasArg() //
          .withArgName("LABEL") //
          .withType(String.class) //
          .withDescription("Enable reachability of a LABEL") //
          .create("r")) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_INCREMENTAL) //
          .withDescription("Run reachability checking incrementally until"
          		+ "reach the iteration bound specified via "
          		+ Preferences.OPTION_ITERATION_TIMES) //
          .create("i")) //    
      .addOption(OptionBuilder.withLongOpt(OPTION_NO_THREADS) //
          .withDescription("Run all sub-processes in a single thread") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_PARSEC) //
          .withDescription("Parse input as C source file") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_PARSE_ONLY) //
          .withDescription("Parse input and quit") //
          .create()) //
      .addOption(
          OptionBuilder.withLongOpt(OPTION_DRY_RUN) //
          .withDescription(
          		"Do a dry run (no theorem prover calls)") //
              .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_PEDANTIC) //
          .withDescription("Enforce strict C99 compliance.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_DEBUG) //
          .withDescription("Run in debug mode.") //
          .create("D")) //
      .addOption(OptionBuilder.withLongOpt(OPTION_STATS) //
          .withDescription("Enable statistics.") //
          .create("ST")) //          
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_COUNTER_EXAMPLE) //
          .withDescription("Enable counter example.") //
          .create("cex")) //
      .addOption(OptionBuilder.withLongOpt(OPTION_SMT2_FILE) //
          .withDescription("Dump theorem prover input file into log FILE") //
          .hasArg() //
          .withArgName("FILE") //
          .withType(File.class) //
          .create())
      .addOption(OptionBuilder.withLongOpt(OPTION_EFFORT_LEVEL) //
          .hasArg() //
          .withArgName("N") //
          .withType(Integer.class) //
          .withDescription("Set effort level for the theorem prover to N.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_MEM_CELL_SIZE) //
          .hasArg() //
          .withArgName("N") //
          .withType(Integer.class) //
          .withDescription("Set the size of memory model cell to N.") //
          .create("m")) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_FUNC_INLINE) //
          .hasArg() //
          .withArgName("N") //
          .withType(Integer.class) //
          .withDescription("Set effort level for the function inline to N.") //
          .create()) //          
      .addOption(OptionBuilder.withLongOpt(OPTION_SOLVER_TIMEOUT) //
          .hasArg() //
          .withArgName("S") //
          .withType(Integer.class) //
          .withDescription("Set timeout for the theorem prover to S sec.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_TIMEOUT) //
          .hasArg() //
          .withArgName("S") //
          .withType(Integer.class) //
          .withDescription("Set timeout for Cascade to S sec.") //
          .create("T")) //
      .addOption(OptionBuilder.withLongOpt(OPTION_FEASIBILITY) //
          .withDescription("Check path feasibility for runs.") //
          .create()) //
      .addOption(
          OptionBuilder.withLongOpt(
              CompressedDomainNamesEncoding.OPTION_EXPLICIT_UNDEFINED) //
              .withDescription("Use explicit unknowns in datatype theories.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(CompressedDomainNamesEncoding.OPTION_FRAME_AXIOM) //
              .withDescription("Omit the frame axiom in datatype theories.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_SOUND_ALLOC) //
              .withDescription("Use a sound allocation model (may be slow).") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_ORDER_ALLOC) //
              .withDescription("Use an ordered allocation model (unsound).") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_NON_OVERFLOW) //
              .withDescription("No overflow checking (use integer incoding).") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_VARI_CELL) //
              .withDescription("Enable the various size of cell based on type information (for burstall-related model only).") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MODE) //
              .withDescription("Use a particular mode: Flat(default), Burstall, Partition") //
              .hasArg() //
              .withType(String.class)
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MEM_ENCODING) //
              .withDescription("Use either encoding: linear(default), sync") //
              .hasArg() //
              .withType(String.class)
              .create()) //          
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_SEQ_PATH) //
              .withDescription("Run sequantial analysis without merge ite branches") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MEMORY_CHECK) //
              .withDescription("Enable checking of memory manipulations") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_INLINE_ANNOTATION) //
              .withDescription("Eable annotation inlined in code.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MULTI_CELL) //
              .withDescription("Enable multi-cell datatype formatter.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_PATH_BASED) //
              .withDescription("Enable loop merge path processing, which"
              		+ " keep the iteration times for every loop rather than"
              		+ " split and connect loop for unrolling.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_PLUGINS_DIRECTORY) //
              .withDescription("Directory where Cascade plugins are stored.") //
              .hasArg() //
              .withArgName("DIR") //
              .withType(File.class)
              .create())
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_ITERATION_TIMES)
              .withDescription("Default iteration times of loop unrolling.")
              .hasArg()
              .withArgName("N")
              .withType(Integer.class)
              .create())
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_LAMBDA) //
              .withDescription("Enable lambda encoding.") //
              .create())
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_HOARE) //
              .withDescription("Enable hoare encoding (treate stack variables without &(..) op as pure logic variable .") //
              .create())              
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_FIELD_SENSITIVE) //
              .withDescription("Enable field sensitive pointer analysis.") //
              .create("fs"))
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_CONTEXT_SENSITIVE) //
              .withDescription("Enable context sensitive pointer analysis.") //
              .create("cs"));
  
  public static void main(String[] args) throws IOException, ParseException, TheoremProverException {
    IOUtils.enableOut();
    IOUtils.enableErr();

    Injector myInjector = createInjector(new CModule(), new CascadeModule());
    final Main main = myInjector.getInstance(Main.class);
    
    // Initialize this tool.
    main.init();
    // Process the command line arguments
    final List<String> files = main.processCommandLine(args);
    
    if(!Preferences.isSet(Preferences.OPTION_TIMEOUT)) {
    	main.run(files); 
    	return;
    }
    
  	ExecutorService executor = Executors.newSingleThreadExecutor();
  	Future<Void> future = executor.submit(new Callable<Void>() {
			@Override
      public Void call() throws Exception {
				main.run(files);
				return null;
      }
  	});
  	
  	long timeout = Preferences.getInt(Preferences.OPTION_TIMEOUT);
  	try {
  		future.get(timeout, TimeUnit.SECONDS);
  	} catch(TimeoutException e) {
  		future.cancel(true);
  		
  		IOUtils.err().println("Timeout");
      IOUtils.err().println("Cascade took time: " + timeout + "s");
  		
  		IOUtils.out().println("Timeout");
  		IOUtils.out().println("Cascade took time: " + timeout + "s");
  		
      System.exit(0);
  	} catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (ExecutionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } finally {   	
    	executor.shutdown();
    }
  }

  /** The runtime. */
  protected final Runtime runtime;
  private TheoremProver theoremProver;
  
  private final Map<File, Node> asts;
  
  private final SymbolTableFactory symbolTableFactory;
  private final Map<File, CSymbolTable> symbolTables;
  
  private CAnalyzer cAnalyzer;

  private Map<Node, IRControlFlowGraph> cfgs;
  private int effortLevel = 0;

  @Inject
  private Main(SymbolTableFactory symbolTableFactory) {
    this.symbolTableFactory = symbolTableFactory;
    
    runtime = new Runtime();
    runtime.setConsole(IOUtils.outPrinter());
    runtime.setErrConsole(IOUtils.errPrinter());

    asts = Maps.newHashMap();
    symbolTables = Maps.newHashMap();
    cfgs = Maps.newHashMap();
  }

  private void failOnError(String msg) {
    runtime.error(msg);
    runtime.exit();
  }
  
  private void failOnException(Throwable e) {
  	IOUtils.err().println(e.getMessage());
    IOUtils.err().flush();
    runtime.exit();
  }

  @SuppressWarnings("unused")
  private void failWithMessage(String msg) {
    IOUtils.err().println(msg);
    IOUtils.err().flush();
    runtime.exit();
  }

  public String getCopy() {
    return "Copyright 2007-2009, New York University";
  }

  public String getName() {
    return "Cascade";
  }

  public String getVersion() {
    return "0.1 (experimental)";
  }

  public void init() {
    try {
      Preferences.init();
    } catch (IOException e) {
      failOnException(e);
    }
    
    // The following are needed by CAnalyzer.
    // We'll fill them in with appropriate values in prepare()
    runtime.bool(OPTION_MARK_AST, OPTION_MARK_AST, true,
        "Mark AST nodes with types.")
        .bool(OPTION_PEDANTIC, OPTION_INTERNAL_PEDANTIC, false,
            "Enforce strict C99 compliance.");

    TheoremProverFactory.discover();
    for( Option opt : TheoremProverFactory.getOptions() ) {
      options.addOption(opt);
    }
  }

  public Node parseSourceFile(File file) throws IOException, ParseException {
    Reader in = new FileReader(file);
    CParser parser = null;
    Result result = null;
    
    /* .i file is a preprocessed file, no need to further preprocessing */
    if(FileUtils.isISourceFile(file)) {
      parser = new CParser(in, file.toString(), (int) file.length());
      result = parser.pTranslationUnit(0);
      /* Everything's OK, return the parse result. */
      return (Node) parser.value(result);
    }

    // if (runtime.test(OPTION_NO_THREADS)) {
    if (Preferences.isSet(OPTION_NO_THREADS)) {
      File preprocessedSource = preprocessToTempFile(in, file);
      Reader preprocessedInput = new FileReader(preprocessedSource);

      parser = new CParser(preprocessedInput, preprocessedSource.toString(),
          (int) preprocessedSource.length());
      result = parser.pTranslationUnit(0);

      preprocessedSource.delete();
    } else {
      PipedInputProcess cppProcess = startPreprocessorThread(in, file);
      Reader cpp_stdout = cppProcess.getOutputAsReader();
      parser = new CParser(cpp_stdout, file.toString());
      result = parser.pTranslationUnit(0);

      try {
        /*
         * Check that the preprocessor didn't barf. If it did, we may have a
         * well-formed but invalid parse tree.
         */
        int returnCode = cppProcess.get();
        if (returnCode != 0) {
          throw new ParseException("Preprocessor failed (retcode=" + returnCode
              + ")");
        }
      } catch (InterruptedException e) {
        throw new AssertionError("Unexpected interrupt");
      } catch (ExecutionException e) {
        throw new ParseException("Preprocessor failed: " + e.getMessage());
      }

      cppProcess.cleanup();
    }

    /* Everything's OK, return the parse result. */
    return (Node) parser.value(result);
  }

  private void prepare() {
  	Preconditions.checkArgument(asts.isEmpty());
  	Preconditions.checkArgument(cfgs.isEmpty());
  	Preconditions.checkArgument(cAnalyzer == null);
  	Preconditions.checkArgument(symbolTables.isEmpty());
    runtime.initDefaultValues();
    runtime.setValue(OPTION_INTERNAL_PEDANTIC,
        Preferences.isSet(OPTION_PEDANTIC));

    if (Preferences.isSet(OPTION_DEBUG)) {
      IOUtils.enableDebug();
      IOUtils.setDebugStream(IOUtils.out());
    }
    
    if (Preferences.isSet(OPTION_STATS)) {
    	IOUtils.enableStats();
    	IOUtils.setStatsStream(IOUtils.err());
    }
    
    if (Preferences.isSet(OPTION_SMT2_FILE)) {
      IOUtils.enableTpFile();
      try {
        IOUtils.setTpFileStream(new PrintStream(
            Preferences.getFile(OPTION_SMT2_FILE)));
      } catch (FileNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    try {
      theoremProver = TheoremProverFactory.getInstance();
    } catch(TheoremProverFactoryException e) {
      failOnException(e);
    }
    if( Preferences.isSet(OPTION_DRY_RUN)) {
      theoremProver = new DryRunTheoremProver(theoremProver);
    }
    
    /* Set the theorem prover "effort level" */
    if( Preferences.isSet(OPTION_EFFORT_LEVEL) ) {
      String effortLevelStr = Preferences.getString(OPTION_EFFORT_LEVEL);
      try {
        effortLevel  = Integer.parseInt(effortLevelStr);
        theoremProver.setEffortLevel(effortLevel);
      } catch( NumberFormatException e ) {
        IOUtils.err().println("Invalid effort level: " + effortLevelStr);
        failOnException(e);
      } catch (TheoremProverException e) {
        failOnException(e);
      } 
    }
    
    /* Set the theorem prover "time limit" */
    if( Preferences.isSet(OPTION_SOLVER_TIMEOUT) ) {
      String timeLimitStr = Preferences.getString(OPTION_SOLVER_TIMEOUT);
      try {
        int tlimit  = Integer.parseInt(timeLimitStr);
        theoremProver.setTimeLimit(tlimit);
      } catch( NumberFormatException e ) {
        failOnException(e);
      } catch (TheoremProverException e) {
        failOnException(e);
      } 
    }
    
    /* Send options down to the theorem prover. */
    try {
      theoremProver.setPreferences();
    } catch (TheoremProverException e) {
      failOnException(e);
    }
    
    /* Set the byte-based or value-based encoding */
    if(Preferences.isSet(Preferences.OPTION_MULTI_CELL) || 
    		Preferences.isSet(Preferences.OPTION_VARI_CELL)) {
    	Preferences.set(Preferences.OPTION_BYTE_BASED);
    }
    
    cAnalyzer = new CAnalyzer(runtime);
  }

  private File preprocessToTempFile(Reader source, File file)
      throws IOException, ParseException {
    String cpp_command = Preferences.getString(C_PREPROCESSOR_TO_FILE);
    assert (cpp_command != null);
    IOUtils.debug()
        .pln("cpp_command: \'" + cpp_command + "\'");

    File preprocessedSource = File.createTempFile(file.getName() + ".", ".E");
    ArgList argsList = CommandTokenizer.tokenize(cpp_command);
    argsList.append(preprocessedSource.toString(), file.toString());
    String args[] = argsList.toArray();
    IOUtils.debug()
        .pln("cpp args: [\'" + Joiner.on("' '").join(args) + "\']");

    Process preprocessor = java.lang.Runtime.getRuntime()
        .exec(args);
    try {
      int returnCode = preprocessor.waitFor();
      if (returnCode != 0) {
        preprocessedSource.delete();
        throw new ParseException("Preprocessor failed (retcode=" + returnCode
            + ")");
      }
      return preprocessedSource;
    } catch (InterruptedException e) {
      preprocessedSource.delete();
      throw new AssertionError("Unexpected interrupt");
    }
  }

  private void printUsage() {
    IOUtils.err()
        .print(getName() + ", v. " + getVersion() + ", " + getCopy() + "\n\n");
    String name = System.getenv("_");
    if (null != name) {
      name = new File(name).getName();
    } else {
      name = getClass().getName();
    }
    PrintWriter writer = new PrintWriter(IOUtils.err());
    new HelpFormatter().printHelp(writer, 78, name
        + " [OPTIONS...] FILE [FILES...]\n", "Options:", options, 2, 4, "");
    writer.flush();
  }

  private void printVersion() {
    IOUtils.out()
        .println(getVersion());
  }
  
  private void printMenu() {
    StringBuilder menuBuilder = new StringBuilder().append("Menu: {");
    
    if(Preferences.isSet(Preferences.OPTION_TIMEOUT)) {
    	menuBuilder.append(Preferences.OPTION_TIMEOUT).append(':')
    		.append(Preferences.getInt(Preferences.OPTION_TIMEOUT)).append(',');
    }
    
    menuBuilder.append(Preferences.OPTION_MODE).append(':');
    if(Preferences.isSet(Preferences.OPTION_MODE)) {
    	menuBuilder.append(Preferences.getString(Preferences.OPTION_MODE)).append(',');
    } else {
    	menuBuilder.append("Flat ");
    }

    if(Preferences.isSet(Preferences.OPTION_HOARE)) {
    	menuBuilder.append(Preferences.OPTION_HOARE).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_FIELD_SENSITIVE)) {
    	menuBuilder.append(Preferences.OPTION_FIELD_SENSITIVE).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_CONTEXT_SENSITIVE)) {
    	menuBuilder.append(Preferences.OPTION_CONTEXT_SENSITIVE).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_LAMBDA)) {
    	menuBuilder.append(Preferences.OPTION_LAMBDA).append(',');
    }
    
    menuBuilder.append(Preferences.OPTION_MEM_ENCODING).append(":");
    if(Preferences.isSet(Preferences.OPTION_MEM_ENCODING)) {
    	menuBuilder.append(Preferences.getString(Preferences.OPTION_MEM_ENCODING)).append(',');
    } else {
    	menuBuilder.append(Preferences.MEM_ENCODING_LINEAR).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) {
    	menuBuilder.append(Preferences.OPTION_MULTI_CELL).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_VARI_CELL)) {
    	menuBuilder.append(Preferences.OPTION_VARI_CELL).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
    	menuBuilder.append(Preferences.OPTION_SOUND_ALLOC).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	menuBuilder.append(Preferences.OPTION_ORDER_ALLOC).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_SEQ_PATH)) {
    	menuBuilder.append(Preferences.OPTION_SEQ_PATH).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_PATH_BASED)) {
    	menuBuilder.append(Preferences.OPTION_PATH_BASED).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_FUNC_INLINE)) {
    	menuBuilder.append(Preferences.OPTION_FUNC_INLINE).append(':').append(
    			Preferences.getInt(Preferences.OPTION_FUNC_INLINE)).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_ITERATION_TIMES)) {
    	menuBuilder.append(Preferences.OPTION_ITERATION_TIMES).append(':').append(
    			Preferences.getInt(Preferences.OPTION_ITERATION_TIMES)).append(',');
    }
    
    if(Preferences.isSet(Preferences.OPTION_INCREMENTAL)) {
    	menuBuilder.append(Preferences.OPTION_INCREMENTAL).append(',');
    }
    
    menuBuilder.append(theoremProver.getProviderName()).append("}\n");
    
    IOUtils.out().println(menuBuilder.toString());
  }

  @SuppressWarnings("unchecked")
  public List<String> processCommandLine(String[] args) {
    CommandLineParser commandLineParser = new PosixParser();
    CommandLine commandLine = null;

    try {
      commandLine = commandLineParser.parse(options, args);
      Preferences.loadCommandLine(commandLine);
    } catch (org.apache.commons.cli.ParseException e) {
      failOnException(e);
    }

    if (commandLine.hasOption(OPTION_PROPERTIES)) {
      String propFile = commandLine.getOptionValue(OPTION_PROPERTIES);
      try {
        Preferences.loadProperties(propFile);
      } catch (IOException e) {
        IOUtils.err().println("Failed to load properties file: " + propFile);
        failOnException(e);
      }
    }

    return (List<String>) commandLine.getArgList();
  }

  public void processSourceFile(File file, Node ast) {
    asts.put(file, ast);
    IOUtils.debug()
        .pln("<source>")
        .incr()
        .flush();
    IOUtils.debugC(ast);
    IOUtils.debug()
        .decr()
        .pln("\n</source>")
        .pln("<ast>")
        .incr()
        .format(ast)
        .decr()
        .pln("\n</ast>")
        .flush();
    
    xtc.util.SymbolTable xtcSymbolTable = cAnalyzer.analyze(ast);
    CSymbolTable symbolTable = CSymbolTable.create(file, symbolTableFactory,
    		xtcSymbolTable);
    Map<Node, IRControlFlowGraph> currCfgs = CfgBuilder.getCfgs(symbolTable, cAnalyzer, ast);
    cfgs.putAll(currCfgs);
    
    for(Node node : currCfgs.keySet()) {
    	/* node may has .c file as source file with lineMarker */
    	String fileName = node.getLocation().file;
    	File currFile = new File(fileName);
    	symbolTables.put(currFile, symbolTable);
    }
  }

  public void run(List<String> files) throws IOException, ParseException, TheoremProverException {
    
    Stopwatch timer = Stopwatch.createUnstarted();
  	timer.start();

    // Prepare for processing the files.
    prepare();

    if (Preferences.isSet(OPTION_VERSION)) {
      printVersion();
      runtime.exit();
    }

    // Print the tool description and exit if there are no arguments.
    if (Preferences.isSet(OPTION_HELP)) { 
      printUsage();
      runtime.exit();
    }

    if (files.isEmpty()) { // index >= args.length) {
      failOnError("no file names specified");
    }

    for (String fileName : files) { 
      // Locate the file.
      File file = null;

      try {
        file = new File(fileName);
      } catch (IllegalArgumentException e) {
        failOnException(e);
      }

      // Parse and process the file.
      if (null != file) {
        if (!file.exists()) {
          failOnError("Cannot open file: " + file);
        }

        if (FileUtils.isCSourceFile(file) || FileUtils.isISourceFile(file)) {
          IOUtils.out()
              .println(
                  "Input appears to be a C source file: " + file.toString());
          
        	assert(Preferences.isSet(OPTION_PARSEC) || Preferences.isSet(OPTION_REACHABILITY));
        	
        	Preferences.set(OPTION_NO_THREADS); // threads will cause broken pipe in parse source file
          try {
          	
          	if (Preferences.isSet(OPTION_PARSEC)) {
          		Node ast = parseSourceFile(file);
          		processSourceFile(file, ast);
            
            } else {
              Node ast = parseSourceFile(file);
              processSourceFile(file, ast);
              
              printMenu();
              
              Mode mode = AbstractMode.getMode(theoremProver.getExpressionManager());
              
              RunProcessor<?> runProcessor;
            	
              if( Preferences.isSet(Preferences.OPTION_SEQ_PATH) ) {
              	runProcessor = new RunSeqProcessor(mode, symbolTables, cfgs, cAnalyzer);
              } else if( Preferences.isSet(Preferences.OPTION_PATH_BASED)) {
              	runProcessor = RunPathBasedProcessor.create(mode, symbolTables, cfgs, cAnalyzer);
              } else {
              	runProcessor = RunMergeProcessor.create(mode, symbolTables, cfgs, cAnalyzer);
              }
              
              String label = Preferences.getString(OPTION_REACHABILITY);
              
              Node mainNode = Iterables.find(cfgs.keySet(), 
              		new Predicate<Node>(){
    								@Override
                    public boolean apply(Node node) {
    									if(node.hasName("FunctionDefinition")) {
    								  	/* Analyze current function definition */
    								    final GNode declarator = node.getGeneric(2);
    								    final GNode identifier = CAnalyzer.getDeclaredId(declarator);
    								    final String functionName = identifier.getString(0);
      	                return "main".equals(functionName);
    									}
    									return false;
                    }
              });
              IRControlFlowGraph mainCfg = cfgs.get(mainNode);
              
            	IOUtils.debug().incr();
            	
            	if(Preferences.isSet(Preferences.OPTION_INCREMENTAL)) {
            		Table<Integer, Integer, Boolean> runIsReachIncrementalTable = 
            				runProcessor.processReachabilityIncremental(mainCfg, label);
            		for(Cell<Integer, Integer, Boolean> entry : runIsReachIncrementalTable.cellSet()) {
            			boolean runIsReachable = entry.getValue();
            			StringBuilder sb = new StringBuilder().append('{')
            					.append(entry.getRowKey())
            					.append(':')
            					.append(entry.getColumnKey())
            					.append("} ")
            					.append(runIsReachable ? "UNSAFE" : "SAFE");
            			
            			IOUtils.out().println(sb.toString());
            		}
            		
            	} else {
                boolean runIsReachable = runProcessor.processReachability(mainCfg, label);
              	IOUtils.out().println(runIsReachable? "UNSAFE" : "SAFE");
              	IOUtils.err().println(runIsReachable ? "UNSAFE" : "SAFE");
            	}
            	IOUtils.debug().decr();
            }
          } catch (RunProcessorException e) {
            failOnException(e);
          } catch (ExpressionFactoryException e) {
            failOnException(e);
          }
        }

        else {
          try {
            ControlFile controlFile = ControlFile.fromXml(file);
            ImmutableList<File> sourceFiles = controlFile.getSourceFiles();
            
            printMenu();
            
            /*
             * ImmutableList.Builder<ITheory> listBuilder =
             * ImmutableList.builder(); for( TheoryId id :
             * controlFile.getTheories() ) { listBuilder.add(
             * id.toTheory(exprManager) ); } List<ITheory> theories =
             * listBuilder.build();
             */
            TheoryId theoryId = controlFile.getTheoryId();
            
            if (theoryId != null) {
            	Theory theory = theoryId.getInstance(theoremProver.getExpressionManager());
            	ExpressionEncoding encoding = theory.getEncoding();
            	theoremProver.assume(encoding.getAssumptions());
            }
            
            for (File sourceFile : sourceFiles) {
              Node ast = parseSourceFile(sourceFile);
              processSourceFile(sourceFile, ast);
            }

            if (Preferences.isSet(OPTION_PARSE_ONLY)) {
              return;
            }
            
            Mode mode = AbstractMode.getMode(theoremProver.getExpressionManager());
            
            RunProcessor<?> runProcessor;
          	
            if( Preferences.isSet(Preferences.OPTION_SEQ_PATH) ) {
            	runProcessor = new RunSeqProcessor(mode, 
            			symbolTables, cfgs, cAnalyzer);
            } else if( Preferences.isSet(Preferences.OPTION_PATH_BASED)) {
            	runProcessor = RunPathBasedProcessor.create(mode, 
            			symbolTables, cfgs, cAnalyzer);
            } else {
            	runProcessor = RunMergeProcessor.create(mode, 
            			symbolTables, cfgs, cAnalyzer);
            }
            
            if( Preferences.isSet(OPTION_FEASIBILITY)) {
              runProcessor.enableFeasibilityChecking();
            }
            
            int i = 1;
            for (Run run : controlFile.getRuns()) {
            	IOUtils.out().println("Run #" + i++ + ":");
            	IOUtils.debug().incr();
            	
            	boolean runIsValid = runProcessor.process(run);
            	IOUtils.out().println(runIsValid ? "Valid" : "Invalid");
            	IOUtils.err().println(runIsValid ? "Valid" : "Invalid");
            	IOUtils.debug().decr();
            }
          } catch (RunProcessorException e) {
            failOnException(e);
          } catch (ExpressionFactoryException e) {
            failOnException(e);
          } catch (ControlFileException e) {
            failOnException(e);
          }

          /*
           * Node ast = null; boolean success = false;
           * 
           * // Parse the input. Reader in = null; try { in =
           * runtime.getReader(file); ast = parseSourceFile(in, file); success
           * = true;
           * 
           * } catch (IllegalArgumentException x) {
           * runtime.error(x.getMessage());
           * 
           * } catch (FileNotFoundException x) {
           * runtime.error(x.getMessage());
           * 
           * } catch (UnsupportedEncodingException x) {
           * runtime.error(x.getMessage());
           * 
           * } catch (IOException x) { if (null == x.getMessage()) {
           * runtime.error(args[index] + ": I/O error"); } else {
           * runtime.error(args[index] + ": " + x.getMessage()); }
           * 
           * } catch (ParseException x) { runtime.error();
           * System.err.print(x.getMessage());
           * 
           * } catch (Throwable x) { runtime.error(); x.printStackTrace();
           * 
           * } finally { if (null != in) { try { in.close(); } catch
           * (IOException x) { // Nothing to see here. Move on. } } }
           * 
           * // Process the AST. try { process(ast); } catch
           * (VisitingException x) { runtime.error();
           * x.getCause().printStackTrace(); } catch (Throwable x) {
           * runtime.error(); x.printStackTrace(); } }
           */
        }
      }
    }
    
    Stopwatch timerStop = timer.stop();
    double elapsedTime = timerStop.elapsed(TimeUnit.MILLISECONDS)/1000.0;
    IOUtils.out().println("Cascade took time: " + elapsedTime + "s");
    IOUtils.stats().pln("Cascade took time: " + elapsedTime + "s");
    IOUtils.err().println("Cascade took time: " + elapsedTime + "s");
  }

  public void setErrStream(PrintStream err) {
    IOUtils.setErrStream(err);
    runtime.setErrConsole(IOUtils.errPrinter());
  }

  public void setOutStream(PrintStream out) {
    IOUtils.setOutStream(out);
    runtime.setConsole(IOUtils.outPrinter());
  }
  
  public void setStatsStream(PrintStream out) {
    IOUtils.setStatsStream(out);
    runtime.setConsole(IOUtils.outPrinter());
  }
  
  /**
   * Take an C program input and pass it through the C preprocessor, returning
   * a {@link java.io.Reader Reader} for the output of the preprocessor.
   * 
   * @throws IOException if an I/O error occurs
   */
  private PipedInputProcess startPreprocessorThread(Reader source, File file)
      throws IOException {
    String cpp_command = Preferences.getString(C_PREPROCESSOR);
    assert (cpp_command != null);
    IOUtils.debug()
        .pln("cpp_command: \'" + cpp_command + "\'");

    ArgList argsList = CommandTokenizer.tokenize(cpp_command);
    argsList.append(file.toString());
    String args[] = argsList.toArray();
    IOUtils.debug()
        .pln("cpp args: [\'" + Joiner.on("' '").join(args) + "\']");

    /*
     * final File preprocessedSource = File.createTempFile(file.getName() +
     * ".", ".E");
     */
    PipedInputProcess preprocessor = new PipedInputProcess(args, source);
    /*
     * , new CleanupStrategy() {
     * 
     * @Override public void cleanUp() { preprocessedSource.delete(); } });
     */preprocessor.run();
    return preprocessor;
  }
}
