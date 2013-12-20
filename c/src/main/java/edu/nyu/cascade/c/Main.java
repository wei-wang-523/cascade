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
import java.util.concurrent.ExecutionException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.PosixParser;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.Node;
import xtc.util.Runtime;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;
import com.google.inject.Inject;
import com.google.inject.Injector;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.control.ControlFile;
import edu.nyu.cascade.control.ControlFileException;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.TheoryId;
import edu.nyu.cascade.datatypes.CompressedDomainNamesEncoding;
import edu.nyu.cascade.ir.IRCallGraph;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTableFactory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.FlatMemoryModel;
import edu.nyu.cascade.ir.expr.IRDataFormatter;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.expr.HeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.OrderLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.expr.SingleCellLinearFormatter;
import edu.nyu.cascade.ir.expr.SingleHeapEncoderAdapter;
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
  private static final String OPTION_EFFORT_LEVEL = "effort-level";
  private static final String OPTION_SOLVER_TIMEOUT = "solver-timeout";
  private static final String OPTION_FEASIBILITY = "feasibility";
  private static final String OPTION_SMT2_FILE = "smt2-file";
  private static final String OPTION_MARK_AST = "optionMarkAST";
  private static final String OPTION_PEDANTIC = "pedantic";
  private static final String OPTION_INTERNAL_PEDANTIC = "optionPedantic";

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
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_COUNTER_EXAMPLE) //
          .withDescription("Enable counter example.") //
          .create()) //
      .addOption(OptionBuilder.withLongOpt(OPTION_SMT2_FILE) //
          .withDescription("Dump theorem prover input file into log FILE") //
          .hasArg() //
          .withArgName("FILE") //
          .withType(File.class) //
          .create()) //
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
          .create()) //
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
          OptionBuilder.withLongOpt(Preferences.OPTION_BURSTALL_MULTI_CELL_SIMP) //
              .withDescription("Simplified burstall multi-cell encoding.") //
              .create()) //
      .addOption(OptionBuilder.withLongOpt(Preferences.OPTION_UNSIGNED_OPERATION)
              .withDescription("Enable unsigned numeric operations.")
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_PARTIAL_INST) //
              .withDescription("Enable partial instantiation.") //
              .hasArg() //
              .withArgName("fld: field; elt: element; fld-of-elt: field of element") //
              .withType(String.class)
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_THEORY) //
              .withDescription("Use a particular theory: Flat(default), Burstall, Partition") //
              .hasArg() //
              .withType(String.class)
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MEM_ENCODING) //
              .withDescription("Use either encoding: linear(default), synchronous, or linearFix") //
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
          OptionBuilder.withLongOpt(Preferences.OPTION_TOTAL_INST) //
              .withDescription("Enable total instantiation.") //
              .create()) //
      .addOption(
          OptionBuilder.withLongOpt(Preferences.OPTION_MULTI_CELL) //
              .withDescription("Enable multi-cell datatype formatter.") //
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
              .create());

  public static void main(String[] args) throws IOException, ParseException, TheoremProverException {
    IOUtils.enableOut();
    IOUtils.enableErr();

    Injector myInjector = createInjector(new CModule(), new CascadeModule());
    final Main main = myInjector.getInstance(Main.class);
    
    // Initialize this tool.
    main.init();
    // Process the command line arguments
    final List<String> files = main.processCommandLine(args);
    
    if(Preferences.isSet(Preferences.OPTION_TIMEOUT)) {    	
    	Thread thread = new Thread(new Runnable() {
        @Override
        public void run() {
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
    	});
      
      long startTime = System.currentTimeMillis();
      int timeout = Preferences.getInt(Preferences.OPTION_TIMEOUT);
      try {
        thread.start();
        while(thread.isAlive()) {
        	Thread.sleep(30);
        	if(System.currentTimeMillis() - startTime > timeout * 1000) {
        		thread.stop();
        		IOUtils.err().println("Timeout");
        		break;
        	}
        }
      } catch (InterruptedException e) {
     // TODO Auto-generated catch block
				e.printStackTrace();
      }
    } else {
    	main.run(files);
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
  private Map<File, IRCallGraph> callGraphs;
  private int effortLevel = 0;
  private int tlimit = 0;

  @Inject
  public Main(SymbolTableFactory symbolTableFactory) {
    this.symbolTableFactory = symbolTableFactory;
    
    runtime = new Runtime();
    runtime.setConsole(IOUtils.outPrinter());
    runtime.setErrConsole(IOUtils.errPrinter());
    
    asts = Maps.newHashMap();
    symbolTables = Maps.newHashMap();
    cfgs = Maps.newHashMap();
    callGraphs = Maps.newHashMap();
  }

  private void failOnError(String msg) {
    runtime.error(msg);
    runtime.exit();
  }
  
  private void failOnException(Throwable e) {
    e.printStackTrace(IOUtils.err());
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
        Throwable cause = e.getCause();
        throw new ParseException("Preprocessor failed: " + cause.getMessage());
      }

      cppProcess.cleanup();
    }

    /* Everything's OK, return the parse result. */
    return (Node) parser.value(result);
  }

  public void prepare() {
    runtime.initDefaultValues();
    runtime.setValue(OPTION_INTERNAL_PEDANTIC,
        Preferences.isSet(OPTION_PEDANTIC));

    if (Preferences.isSet(OPTION_DEBUG)) {
      IOUtils.enableDebug();
      IOUtils.setDebugStream(IOUtils.out());
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
        tlimit  = Integer.parseInt(timeLimitStr);
        theoremProver.setTimeLimit(tlimit);
      } catch( NumberFormatException e ) {
        IOUtils.err().println("Invalid time level: " + timeLimitStr + "s.");
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
    CSymbolTable symbolTable = CSymbolTable.create(symbolTableFactory,
        xtcSymbolTable);
    Map<Node, IRControlFlowGraph> currCfgs = CfgBuilder.getCfgs(symbolTable, cAnalyzer, ast);
    cfgs.putAll(currCfgs);
    callGraphs.put(file, CallGraphBuilder.getCallGraph(symbolTable, ast));
    symbolTables.put(file, symbolTable);
  }

  public void run(List<String> files) throws IOException, ParseException, TheoremProverException {
    
    long time = System.currentTimeMillis();

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

        if (FileUtils.isCSourceFile(file)
            && !Preferences.isSet(OPTION_PARSEC)) {
          IOUtils.err()
              .println(
                  "Input appears to be a C source file: " + file.toString());
          IOUtils.err()
              .println(
                  "Parsing as C (using " + OPTION_PARSEC + " is recommended).");
          Preferences.set(OPTION_PARSEC);
        }

        if (Preferences.isSet(OPTION_PARSEC)) {
          Node ast = parseSourceFile(file);
          processSourceFile(file, ast);
        } else {
          try {
            ControlFile controlFile = ControlFile.fromXml(file);
            ImmutableList<File> sourceFiles = controlFile.getSourceFiles();
            for (File sourceFile : sourceFiles) {
              Node ast = parseSourceFile(sourceFile);
              processSourceFile(sourceFile, ast);
            }

            // final ITheoremProver theoremProver =
            // exprManager.getTheoremProver();

            if (Preferences.isSet(OPTION_PARSE_ONLY)) {
              return;
            }

            /*
             * ImmutableList.Builder<ITheory> listBuilder =
             * ImmutableList.builder(); for( TheoryId id :
             * controlFile.getTheories() ) { listBuilder.add(
             * id.toTheory(exprManager) ); } List<ITheory> theories =
             * listBuilder.build();
             */
            TheoryId theoryId = controlFile.getTheoryId();
            ExpressionEncoding encoding;
            MemoryModel memoryModel;
            PreProcessor.Builder<?> builder = null;
            CScopeAnalyzer.Builder scopeAnalyzerBuilder = null;
            
            if(Preferences.isSet(Preferences.OPTION_THEORY)) {
              // TODO: ugly way to append prefix of qname of theory
              StringBuffer sb = new StringBuffer().append("edu.nyu.cascade.c.theory.");
              sb.append(Preferences.getString(Preferences.OPTION_THEORY)).append("Theory");
              theoryId = new TheoryId(sb.toString());
            }
            
            if (theoryId != null) {
              Theory theory = theoryId.getInstance(theoremProver.getExpressionManager());
              encoding = theory.getEncoding();
              memoryModel = theory.getMemoryModel();
              builder = theory.getPreprocessorBuilder();
              scopeAnalyzerBuilder = theory.getScopeAnalyzerBuilder();
            } else {           
              // TODO: Fix bit-vector sizes to agree with encoding              
              encoding = PointerExpressionEncoding.create(theoremProver
                  .getExpressionManager()); 
              IRDataFormatter formatter = SingleCellLinearFormatter.create(encoding);   
              IRHeapEncoding heapEncoding = HeapEncoding.create(encoding, formatter);
              IROrderMemLayoutEncoding memLayout = OrderLinearMemLayoutEncoding
            			.create(heapEncoding);
            	PartitionHeapEncoder parHeapEncoder = PartitionHeapEncoder
            			.createOrderEncoding(heapEncoding, memLayout);
            	IRSingleHeapEncoder heapEncoder = SingleHeapEncoderAdapter.create(parHeapEncoder);
            	memoryModel = FlatMemoryModel.create(encoding, heapEncoder);
            }
            
            CExpressionEncoder encoder = CExpressionEncoder.create(encoding,
                memoryModel, symbolTables);

            RunProcessor runProcessor;
          	
            if( Preferences.isSet(Preferences.OPTION_SEQ_PATH) ) {
              runProcessor = new RunSeqProcessor(symbolTables, cfgs, callGraphs,
              		cAnalyzer, encoder, builder, scopeAnalyzerBuilder);
            } else {
            	runProcessor = new RunMergeProcessor(symbolTables, cfgs, callGraphs,
            			cAnalyzer, encoder, builder, scopeAnalyzerBuilder);
            }
            
            if( Preferences.isSet(OPTION_FEASIBILITY)) {
              runProcessor.enableFeasibilityChecking();
            }
            /*
             * public boolean handle(IBooleanExpression vc) { IOUtils.debug()
             * .pln("VC=" + vc) .flush(); QueryResult result =
             * theoremProver.isValid(vc); IOUtils.debug() .pln("VC is " +
             * result) .flush(); boolean isValid =
             * QueryResult.VALID.equals(result); if (!isValid) { if
             * (IOUtils.debugEnabled()) { List<IBooleanExpression>
             * counterExample = theoremProver.getCounterExample();
             * IOUtils.debug() .pln(counterExample.toString()) .flush(); } }
             * runIsValid &= isValid; return isValid; }
             */
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
    time = System.currentTimeMillis() - time;
    IOUtils.out().println("Cascade took time: " + time/1000.0 + "s");
    IOUtils.err().println("Cascade took time: " + time/1000.0 + "s");
  }

  public void setErrStream(PrintStream err) {
    IOUtils.setErrStream(err);
    runtime.setErrConsole(IOUtils.errPrinter());
  }

  public void setOutStream(PrintStream out) {
    IOUtils.setOutStream(out);
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
