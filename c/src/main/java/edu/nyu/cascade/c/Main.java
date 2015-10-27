package edu.nyu.cascade.c;

import static com.google.inject.Guice.createInjector;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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

import xtc.lang.CParser;
import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.Runtime;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import com.google.inject.Injector;

import edu.nyu.cascade.c.mode.AbstractMode;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.datatypes.CompressedDomainNamesEncoding;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.SymbolTableFactory;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.LoopInfoUtil;
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
import edu.nyu.cascade.util.StatsTimer;
import edu.nyu.cascade.util.Unit;

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
  private static final String OPTION_CFG_ONLY = "cfg-only";
  private static final String OPTION_DRY_RUN = "dry-run";
  private static final String OPTION_PTR_ANALYSIS_ONLY = "ptr-analysis-only";
  private static final String OPTION_DEBUG = "debug";
  private static final String OPTION_STATS = "stats";
  private static final String OPTION_FEASIBILITY = "feasibility";
  private static final String OPTION_SMT2_FILE = "smt2-file";
  private static final String OPTION_MARK_AST = "optionMarkAST";
  private static final String OPTION_PEDANTIC = "pedantic";
  private static final String OPTION_INTERNAL_PEDANTIC = "optionPedantic";
  private static final String OPTION_CHECK_FUNC_INLINE = "check-func-inline";
	private static final String INSUFFICIENT_UNROLL = "insufficient_loop_unroll";
  
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
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_REACHABILITY) //
          .hasArg() //
          .withArgName("LABEL") //
          .withType(String.class) //
          .withDescription("Enable reachability of a LABEL") //
          .create("r")) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_INCREMENTAL) //
          .withDescription("Run reachability checking incrementally until"
          		+ "reach the bound set for function inline.") //
          .create("i")) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_CHECK_EXIT_UNROLL) //
      		.withDescription("Check if ERROR code unreachable is due to early loop exit.") //
      		.create()) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_CHECK_KEEP_UNROLL) //
      		.withDescription("Check if loop can keep unrolling after currrent iteration time, "
      				+ "error may exist in further loop unrolling") //
      		.create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_CHECK_FUNC_INLINE)
      		.withDescription("Check if the function inline bound is enough, will report unknown"
      				+ " if it is not") //
      		.create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_NO_THREADS) //
          .withDescription("Run all sub-processes in a single thread") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_CFG_ONLY) //
          .withDescription("Build and simplify cfg, then quit") //
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
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_TRACE) //
          .withDescription("Dump trace when detect failure.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_DEBUG) //
          .withDescription("Run in debug mode.") //
          .create("D")) //
      .addOption(OptionBuilder.withLongOpt(OPTION_STATS) //
          .withDescription("Enable statistics.") //
          .create("ST")) //
      .addOption(OptionBuilder.withLongOpt(OPTION_SMT2_FILE) //
          .withDescription("Dump theorem prover input file into FILE") //
          .hasArg() //
          .withArgName("FILE") //
          .withType(File.class) //
          .create())
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_MEM_CELL_SIZE) //
          .hasArg() //
          .withArgName("N") //
          .withType(Integer.class) //
          .withDescription("Set the size of memory model cell to N.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_FUNC_INLINE) //
          .hasArg() //
          .withArgName("N") //
          .withType(Integer.class) //
          .withDescription("Set effort level for the function inline to N.") //
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
          OptionBuilder.withLongOpt(Preferences.OPTION_M32) //
              .withDescription("Use a 32bit architecture.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_M64) //
              .withDescription("Use a 64bit architecture.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_VARI_CELL) //
              .withDescription("Enable the various size of cell based on type information (for field-sensitive partition model only).") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MODE) //
              .withDescription("Use a particular mode: Flat(default), Burstall, Partition") //
              .hasArg() //
              .withType(String.class)
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
          OptionBuilder.withLongOpt(Preferences.OPTION_SBE) //
              .withDescription("Small block-based encoding") //
              .create("sbe")) //
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
          OptionBuilder.withLongOpt(Preferences.OPTION_STMT) //
              .withDescription("Enable statement based lambda encoding.") //
              .create())
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_HOARE) //
              .withDescription("Enable hoare encoding (treate stack variables without & op as pure logic variable .") //
              .create())              
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_FIELD_SENSITIVE) //
              .withDescription("Enable field sensitive pointer analysis.") //
              .create("fs"))
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE) //
              .withDescription("Enable cell based field sensitive pointer analysis.") //
              .create("cfs"))
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_CFS_POINTER_ARITH) //
              .withDescription("Enable optimization of pointer arithmetic in cfs pointer analysis.") //
              .create())              
      .addOption(
      		OptionBuilder.withLongOpt(OPTION_PTR_ANALYSIS_ONLY) //
      				.withDescription("Run pointer analysis only") //
      				.create("ptr"));
          
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
    } else {
    	int timeout = Preferences.getInt(Preferences.OPTION_TIMEOUT);
    	main.runWithTimeLimit(files, timeout);
    }
  }

  /** The runtime. */
  protected final Runtime runtime;
  private TheoremProver theoremProver;
  
  private final Map<File, Node> asts;
  
  private final SymbolTableFactory symbolTableFactory;
  
  private SymbolTable symbolTable;
  
  private CAnalyzer cAnalyzer;

  private Map<Node, IRControlFlowGraph> cfgs;
  
  private SafeResult safeResult;

  @Inject
  private Main(SymbolTableFactory symbolTableFactory) {
    this.symbolTableFactory = symbolTableFactory;
    
    runtime = new Runtime();
    runtime.setConsole(IOUtils.outPrinter());
    runtime.setErrConsole(IOUtils.errPrinter());

    asts = Maps.newHashMap();
    cfgs = Maps.newLinkedHashMap();
  }

  private void failOnError(String msg) {
    runtime.error(msg);
    runtime.exit();
  }
  
  private void failOnException(Throwable e) {
  	IOUtils.err().println(e.getMessage());
    IOUtils.err().flush();
  	IOUtils.out().println(SafeResult.unknown(e.getMessage()));
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
    
		TheoremProver.Provider cvc4Tp = new edu.nyu.cascade.cvc4.TheoremProverImpl.Provider();
		TheoremProverFactory.register(cvc4Tp);
		TheoremProver.Provider z3Tp = new edu.nyu.cascade.z3.TheoremProverImpl.Provider();
		TheoremProverFactory.register(z3Tp);
		
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
        throw new ParseException("Preprocessor failed: " + e.getMessage(), e);
      }

      cppProcess.cleanup();
    }

    /* Everything's OK, return the parse result. */
    Node res = (Node) parser.value(result);
    return res;
  }

  private void prepare() {
  	Preconditions.checkArgument(asts.isEmpty());
  	Preconditions.checkArgument(cfgs.isEmpty());
  	Preconditions.checkArgument(cAnalyzer == null);
  	Preconditions.checkArgument(symbolTable == null);
    runtime.initDefaultValues();
    runtime.setValue(OPTION_INTERNAL_PEDANTIC,
        Preferences.isSet(OPTION_PEDANTIC));
    cAnalyzer = new CAnalyzer(CType.getInstance().c(), runtime);

    if (Preferences.isSet(OPTION_DEBUG)) {
      IOUtils.enableDebug();
      IOUtils.setDebugStream(IOUtils.out());
    }
    
    if (Preferences.isSet(OPTION_STATS)) {
    	IOUtils.enableStats();
    	IOUtils.setStatsStream(IOUtils.err());
    }
    
    try {
      if (Preferences.isSet(OPTION_SMT2_FILE)) {
        IOUtils.enableTpFile();
        IOUtils.setTpFileStream(new PrintStream(Preferences.getFile(OPTION_SMT2_FILE)));
      }
    } catch (FileNotFoundException e) {
    	failOnException(e);
    }
    
    /* Set the byte-based or value-based encoding */
    if(Preferences.isSet(Preferences.OPTION_MULTI_CELL) || 
    		Preferences.isSet(Preferences.OPTION_VARI_CELL)) {
    	Preferences.set(Preferences.OPTION_BYTE_BASED);
    }

    try {
    	theoremProver = TheoremProverFactory.getInstance();
    	
    	if( Preferences.isSet(OPTION_DRY_RUN)) {
    		theoremProver = new DryRunTheoremProver(theoremProver);
    	}
    	
    	/* Send options down to the theorem prover. */
    	theoremProver.setPreferences();
    } catch (TheoremProverException e) {
      failOnException(e);
    } catch (TheoremProverFactoryException e) {
    	failOnException(e);
		}
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
  
  private void printOptions() {
    StringBuilder menuBuilder = new StringBuilder().append("Options: {");
    for(Entry<String, Object> prop : Preferences.getProperties().entrySet()) {
    	String label = prop.getKey();
    	menuBuilder.append("\n\t").append(label).append(' ');
    	Object value = prop.getValue();
    	if(value instanceof Unit) continue;
    	menuBuilder.append(prop.getValue());
    }
    menuBuilder.append("\n}");
    IOUtils.stats()
    		.pln(menuBuilder.toString());
  }
  
  private void printTimeInfo(PrintStream out) {
  	long runTime = StatsTimer.cascadeElapseTime();
  	long solverTime = theoremProver.getStatsTime();
  	double encoding = (runTime - solverTime)/1000.0;
  	out.append("Encoding took ")
  			.append(String.valueOf(encoding))
  			.append('s')
  			.append('\n');
  	out.append(theoremProver.getProviderName())
  		 .append(" took ")
  		 .append(String.valueOf(solverTime/1000.0))
  		 .append('s')
  		 .append('\n');
  	out.append(getName())
  		 .append(" took ")
  		 .append(String.valueOf(runTime/1000.0))
  		 .append('s')
  		 .append('\n');
  	out.flush();
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
    symbolTable = CSymbolTable.create(file, symbolTableFactory, xtcSymbolTable);
    Map<Node, IRControlFlowGraph> currCfgs = CfgBuilder.getCfgs(symbolTable, ast);
    cfgs.putAll(currCfgs);
  }
  
  public void runWithTimeLimit(final List<String> files, long timeout) {
  	ExecutorService executor = Executors.newSingleThreadExecutor();
  	
  	Future<Void> future = executor.submit(new Callable<Void>() {
			@Override
      public Void call() throws Exception {
				run(files);
				return null;
      }
  	});
  	
  	try {
  		future.get(timeout, TimeUnit.SECONDS);
  	} catch(TimeoutException e) {
  		future.cancel(true);
//  		if(safeResult != null)
//  			IOUtils.out().println(safeResult);
      System.exit(0);
  	} catch (InterruptedException e) {
      e.printStackTrace();
    } catch (ExecutionException e) {
      e.printStackTrace();
    } finally {   	
    	executor.shutdown();
    }
  }

  public void run(List<String> files) throws ParseException, IOException {
  	StatsTimer.cascadeStart();
  	
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
      File file = new File(fileName);
      
      // Parse and process the file.
      if (null != file) {
        if (!file.exists()) failOnError("Cannot open file: " + file);

        assert (FileUtils.isCSourceFile(file) || FileUtils.isISourceFile(file));
      	
      	Preferences.set(OPTION_NO_THREADS); // threads will cause broken pipe in parse source file
      	
        try {
        	
      		Node ast = parseSourceFile(file);
      		processSourceFile(file, ast);
          printOptions();
        	
        	if (Preferences.isSet(OPTION_PARSEC)) return;
        	
          IRControlFlowGraph mainCfg = Iterables.find(cfgs.values(), 
          		new Predicate<IRControlFlowGraph>(){
          	@Override
          	public boolean apply(IRControlFlowGraph cfg) {
          		return cfg.getName().equals("main");
          	}
          }, null);
        	
          if(mainCfg == null) {
          	IOUtils.err().println("no main function."); return;
          }
          
          Mode mode = AbstractMode.getMode(theoremProver);
          
          RunProcessor runProcessor = RunProcessorImpl.create(mode, symbolTable, cfgs);
        	
          if (Preferences.isSet(Preferences.OPTION_TRACE))
          	IOUtils.enableTrace(file);
          
        	if(Preferences.isSet(Preferences.OPTION_REACHABILITY)) {
        		checkReachability(runProcessor, mainCfg);
          } else {
          	checkProperty(runProcessor, mainCfg);          	
        	}
        	
        } catch (RunProcessorException e) {
        	failOnException(e);
        } catch (ExpressionFactoryException e) {
          failOnException(e);
        }
      }
    }
		IOUtils.out().println(safeResult);
    StatsTimer.cascadeStop();
    printTimeInfo(IOUtils.err());
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
  
  private void checkReachability(RunProcessor runProcessor, IRControlFlowGraph mainCfg) 
  		throws RunProcessorException {
  	
		String funcInline = Preferences.isSet(Preferences.OPTION_FUNC_INLINE) ? 
      	Preferences.getString(Preferences.OPTION_FUNC_INLINE) : "all-inline";
  	
  	String label = Preferences.getString(Preferences.OPTION_REACHABILITY);
    
  	runProcessor.init(label);

  	if (Preferences.isSet(OPTION_CFG_ONLY)) return;
  	
  	runProcessor.preprocess();

	if( Preferences.isSet(OPTION_PTR_ANALYSIS_ONLY)) {
	    safeResult = SafeResult.unknown("Pointer analysis only");
	    printResult(0, funcInline, IOUtils.outPrinter());
	    return;
	}
    
    /* Merge graph and function inline */
    runProcessor.prepare(mainCfg);
    
    if(Preferences.isSet(OPTION_CHECK_FUNC_INLINE) && 
    		!runProcessor.isFullyFuncInlined(mainCfg)) {
    	safeResult = SafeResult.unknown("Insufficient_function_inline");
    	printResult(0, funcInline, IOUtils.outPrinter());
    	return;
    }
    
    /* Merge graph and function inline */
    runProcessor.prepare(mainCfg);
    
		/* Simplify mainCFG (function-inline may introduce dead blocks) */
		CfgProcessor.simplifyCFG(mainCfg, label);
		
		LoopInfo loopInfo = LoopInfoUtil.analyze(mainCfg);
		
		/* No Loop in mainCFG */
		if(loopInfo.getTopLevelLoops().isEmpty()) {
			int iterTime = 0;
			
			safeResult = runProcessor.processReachability(mainCfg, loopInfo, label, iterTime);
			
			printResult(iterTime, funcInline, IOUtils.outPrinter());
			
  		if(safeResult.isUnsafe()) runProcessor.dumpErrorTrace(mainCfg);
  		return;
		}
  	
  	if(!Preferences.isSet(Preferences.OPTION_INCREMENTAL)) {
  		int iterTime = Preferences.isSet(Preferences.OPTION_ITERATION_TIMES) ?
  				Preferences.getInt(Preferences.OPTION_ITERATION_TIMES) : 0;
  				
  		safeResult = runProcessor.processReachability(mainCfg, loopInfo, label, iterTime);
  		
  		printResult(iterTime, funcInline, IOUtils.outPrinter());
  		
  		if(safeResult.isUnsafe()) runProcessor.dumpErrorTrace(mainCfg);
  		
  	} else {
        
  		Collection<Integer> iterTimesSet = Sets.newTreeSet(Preferences.REACH_MAGIC_ITER_TIMES);
  		
  		boolean checkKeepUnroll = Preferences.isSet(Preferences.OPTION_CHECK_KEEP_UNROLL);
  		boolean checkExitUnroll = Preferences.isSet(Preferences.OPTION_CHECK_EXIT_UNROLL);
  		
  		for(int currIterTime : iterTimesSet) {
  			if(checkKeepUnroll)		runProcessor.enableCheckKeepUnroll();
  			if(checkExitUnroll)		runProcessor.enableCheckExitUnroll();
  			
  			safeResult = runProcessor.processReachability(mainCfg, loopInfo, label, currIterTime);
    		
  			if(safeResult.isUnsafe()) {
  				printResult(currIterTime, funcInline, IOUtils.outPrinter());
  				runProcessor.dumpErrorTrace(mainCfg); 
  				break;
  			}
  			
  			if(checkKeepUnroll || checkExitUnroll)  {
  				if(checkKeepUnroll && !runProcessor.checkKeepUnroll()) {
  					printResult(currIterTime, funcInline, IOUtils.outPrinter());
  					break;
  				}
  				if(checkExitUnroll && !runProcessor.checkExitUnroll()) {
  					printResult(currIterTime, funcInline, IOUtils.outPrinter());
  					break;
  				}
  				
  				safeResult = SafeResult.unknown(INSUFFICIENT_UNROLL); 
  			}
  			
  			printResult(currIterTime, funcInline, IOUtils.outPrinter());
  			runProcessor.reset();
  		}
  	}
  }
  
  private void printResult(int iterTime, String funcInline, Printer printer) {
		IOUtils.outPrinter().p('{')
		.p(iterTime).p(':').p(funcInline)
		.p("}..")
		.p(safeResult.toString())
		.pln();
  }
  
  private void checkProperty(RunProcessor runProcessor, IRControlFlowGraph mainCfg) 
  		throws RunProcessorException {
    
    if(Preferences.isSet(OPTION_FEASIBILITY))	
    	runProcessor.enableFeasibilityChecking();
    
		String funcInline = Preferences.isSet(Preferences.OPTION_FUNC_INLINE) ? 
      	Preferences.getString(Preferences.OPTION_FUNC_INLINE) : "all-inline";
    
    runProcessor.init();

    if (Preferences.isSet(OPTION_CFG_ONLY)) return;
    
    runProcessor.preprocess();
    
    if( Preferences.isSet(OPTION_PTR_ANALYSIS_ONLY)) {
	safeResult = SafeResult.unknown("Pointer analysis only");
	printResult(0, funcInline, IOUtils.outPrinter());
	return;
    }
    
    /* Merge graph and function inline */
    runProcessor.prepare(mainCfg);
    
    if(Preferences.isSet(OPTION_CHECK_FUNC_INLINE) && 
    		!runProcessor.isFullyFuncInlined(mainCfg)) {
    	safeResult = SafeResult.unknown("Insufficient_function_inline");
    	printResult(0, funcInline, IOUtils.outPrinter());
    	return;
    }
    
		/* Simplify mainCFG (function-inline may introduce dead blocks) */
		CfgProcessor.simplifyCFG(mainCfg);
		
		LoopInfo loopInfo = LoopInfoUtil.analyze(mainCfg);
		
		/* No Loop in mainCFG */
		if(loopInfo.getTopLevelLoops().isEmpty()) {
			int iterTime = 0;
			
			safeResult = runProcessor.processAssertion(mainCfg, loopInfo, iterTime);
			
			printResult(iterTime, funcInline, IOUtils.outPrinter());
			
  		if(safeResult.isUnsafe()) runProcessor.dumpErrorTrace(mainCfg);
  		return;
		}
    
  	if(!Preferences.isSet(Preferences.OPTION_INCREMENTAL)) {
  		int iterTime = Preferences.isSet(Preferences.OPTION_ITERATION_TIMES) ?
  				Preferences.getInt(Preferences.OPTION_ITERATION_TIMES) : 0;
  				
  		safeResult = runProcessor.processAssertion(mainCfg, loopInfo, iterTime);
  		
  		printResult(iterTime, funcInline, IOUtils.outPrinter());
  		
  		if(safeResult.isUnsafe()) runProcessor.dumpErrorTrace(mainCfg);
  		
  	} else {
        
  		Collection<Integer> iterTimesSet = Sets.newTreeSet(Preferences.MEM_MAGIC_ITER_TIMES);
  		
  		boolean checkKeepUnroll = Preferences.isSet(Preferences.OPTION_CHECK_KEEP_UNROLL);
  		boolean checkExitUnroll = Preferences.isSet(Preferences.OPTION_CHECK_EXIT_UNROLL);
  		
  		for(int currIterTime : iterTimesSet) {
  			if(checkKeepUnroll)		runProcessor.enableCheckKeepUnroll();
  			if(checkExitUnroll)		runProcessor.enableCheckExitUnroll();
  			
  			safeResult = runProcessor.processAssertion(mainCfg, loopInfo, currIterTime);
    		
  			if(safeResult.isUnsafe()) {
  				printResult(currIterTime, funcInline, IOUtils.outPrinter());
  				runProcessor.dumpErrorTrace(mainCfg); break;
  			}
  			
  			if(checkKeepUnroll || checkExitUnroll)  {
  				if(checkKeepUnroll && !runProcessor.checkKeepUnroll()) {
  					printResult(currIterTime, funcInline, IOUtils.outPrinter());
  					break;
  				}
  				
  				if(checkExitUnroll && !runProcessor.checkExitUnroll()) {
  					printResult(currIterTime, funcInline, IOUtils.outPrinter());
  					break;
  				}
  				
  				safeResult = SafeResult.unknown(INSUFFICIENT_UNROLL); 
  			}
  			
  			printResult(currIterTime, funcInline, IOUtils.outPrinter());
  			runProcessor.reset();
  		}
  	}
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
