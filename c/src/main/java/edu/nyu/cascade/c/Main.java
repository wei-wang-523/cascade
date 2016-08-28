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
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;

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
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
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
	private static final String OPTION_DRY_RUN = "dry-run";
	private static final String OPTION_DEBUG = "debug";
	private static final String OPTION_STATS = "stats";
	private static final String OPTION_FEASIBILITY = "feasibility";
	private static final String OPTION_SMT2_FILE = "smt2-file";
	private static final String OPTION_MARK_AST = "optionMarkAST";
	private static final String OPTION_PEDANTIC = "pedantic";
	private static final String OPTION_INTERNAL_PEDANTIC = "optionPedantic";
	private static final String OPTION_CHECK_FUNC_INLINE = "check-func-inline";
	private static final String INSUFFICIENT_UNROLL = "insufficient_loop_unroll";

	private static final Options options = new Options() //
			.addOption(OPTION_HELP_SHORT, OPTION_HELP, false, //
					"Print usage information") //
			.addOption(OPTION_VERSION_SHORT, OPTION_VERSION, false, //
					"Print version and exit") //
			.addOption(Option.builder().longOpt(OPTION_PROPERTIES) //
					.hasArg() //
					.argName("FILE") //
					.type(File.class) //
					.desc("Specify a user properties file").build()) //
			.addOption(Option.builder("r").longOpt(Preferences.OPTION_REACHABILITY) //
					.hasArg() //
					.argName("LABEL") //
					.type(String.class) //
					.desc("Enable reachability of a LABEL") //
					.build()) //
			.addOption(Option.builder("i").longOpt(Preferences.OPTION_INCREMENTAL) //
					.desc(
							"Run reachability checking incrementally until reach the bound set for function inline.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_CHECK_EXIT_UNROLL) //
					.desc("Check if ERROR code unreachable is due to early loop exit.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_CHECK_KEEP_UNROLL) //
					.desc(
							"Check if loop can keep unrolling after currrent iteration time, error may exist in further loop unrolling") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_CHECK_FUNC_INLINE).desc(
					"Check if the function inline bound is enough, will report unknown if it is not") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_NO_THREADS) //
					.desc("Run all sub-processes in a single thread") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_PARSEC) //
					.desc("Parse input as C source file") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_DRY_RUN) //
					.desc("Do a dry run (no theorem prover calls)") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_PEDANTIC) //
					.desc("Enforce strict C99 compliance.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_TRACE) //
					.desc("Dump trace when detect failure.") //
					.build()) //
			.addOption(Option.builder("D").longOpt(OPTION_DEBUG) //
					.desc("Run in debug mode.") //
					.build()) //
			.addOption(Option.builder("ST").longOpt(OPTION_STATS) //
					.desc("Enable statistics.") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_SMT2_FILE) //
					.desc("Dump theorem prover input file into FILE") //
					.hasArg() //
					.argName("FILE") //
					.type(File.class) //
					.build())
			.addOption(Option.builder().longOpt(Preferences.OPTION_MEM_CELL_SIZE) //
					.hasArg() //
					.argName("N") //
					.type(Integer.class) //
					.desc("Set the size of memory model cell to N.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_FUNC_INLINE) //
					.hasArg() //
					.argName("N") //
					.type(Integer.class) //
					.desc("Set effort level for the function inline to N.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_TIMEOUT) //
					.hasArg() //
					.argName("S") //
					.type(Integer.class) //
					.desc("Set timeout for Cascade to S sec.") //
					.build()) //
			.addOption(Option.builder().longOpt(OPTION_FEASIBILITY) //
					.desc("Check path feasibility for runs.") //
					.build()) //
			.addOption(Option.builder()
					.longOpt(CompressedDomainNamesEncoding.OPTION_EXPLICIT_UNDEFINED) //
					.desc("Use explicit unknowns in datatype theories.") //
					.build()) //
			.addOption(Option.builder()
					.longOpt(CompressedDomainNamesEncoding.OPTION_FRAME_AXIOM) //
					.desc("Omit the frame axiom in datatype theories.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_SOUND_ALLOC) //
					.desc("Use a sound allocation model (may be slow).") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_ORDER_ALLOC) //
					.desc("Use an ordered allocation model (unsound).") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_M32) //
					.desc("Use a 32bit architecture.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_M64) //
					.desc("Use a 64bit architecture.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_VARI_CELL) //
					.desc(
							"Enable the various size of cell based on type information (for field-sensitive partition model only).") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_MODE) //
					.desc("Use a particular mode: Flat(default), Burstall, Partition") //
					.hasArg() //
					.type(String.class).build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_MEMORY_CHECK) //
					.desc("Enable checking of memory manipulations") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_INLINE_ANNOTATION) //
					.desc("Eable annotation inlined in code.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_MULTI_CELL) //
					.desc("Enable multi-cell datatype formatter.") //
					.build()) //
			.addOption(Option.builder("sbe").longOpt(Preferences.OPTION_SBE) //
					.desc("Small block-based encoding") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_PLUGINS_DIRECTORY) //
					.desc("Directory where Cascade plugins are stored.") //
					.hasArg() //
					.argName("DIR") //
					.type(File.class) //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_ITERATION_TIMES)
					.desc("Default iteration times of loop unrolling.").hasArg() //
					.argName("N") //
					.type(Integer.class) //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_LAMBDA) //
					.desc("Enable lambda encoding.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_STMT) //
					.desc("Enable statement based lambda encoding.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_HOARE) //
					.desc("Enable hoare encoding (treate stack variables without" //
							+ " & op as pure logic variable .") //
					.build()) //
			.addOption(
					Option.builder("fs").longOpt(Preferences.OPTION_FIELD_SENSITIVE) //
							.desc("Enable field sensitive pointer analysis.") //
							.build()) //
			.addOption(Option.builder("cfs")
					.longOpt(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE) //
					.desc("Enable cell based field sensitive pointer analysis.") //
					.build()) //
			.addOption(Option.builder("cfscs")
					.longOpt(
							Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE_CONTEXT_SENSITIVE) //
					.desc("Enable cell based field sensitive and context sensitive " //
							+ "pointer analysis.") //
					.build()) //
			.addOption(Option.builder("dsa").longOpt(Preferences.OPTION_DSA) //
					.desc("Enable data-structure alias analysis.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_CFS_POINTER_ARITH) //
					.desc("Enable optimization of pointer arithmetic in cfs pointer "
							+ "analysis.") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_INLINE_MALLOC) //
					.desc("Inline malloc function") //
					.build()) //
			.addOption(Option.builder().longOpt(Preferences.OPTION_TWOROUND_MEMCHECK) //
					.desc("Two round memory check") //
					.build());

	public static void main(String[] args)
			throws IOException, ParseException, TheoremProverException {
		IOUtils.enableOut();
		IOUtils.enableErr();

		Injector myInjector = createInjector(new CModule(), new CascadeModule());
		final Main main = myInjector.getInstance(Main.class);

		// Initialize this tool.
		main.init();
		// Process the command line arguments
		final List<String> files = main.processCommandLine(args);

		if (!Preferences.isSet(Preferences.OPTION_TIMEOUT)) {
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
	private FunctionCallGraph callGraph;
	private SafeResult safeResult;

	interface EncodingStrategy {
		SafeResult apply(RunProcessor processor, IRControlFlowGraph cfg,
				LoopInfo loopInfo, Integer iterTimes) throws RunProcessorException;
	}

	@Inject
	private Main(SymbolTableFactory symbolTableFactory) {
		this.symbolTableFactory = symbolTableFactory;

		runtime = new Runtime();
		runtime.setConsole(IOUtils.outPrinter());
		runtime.setErrConsole(IOUtils.errPrinter());

		asts = Maps.newHashMap();
		cfgs = Maps.newLinkedHashMap();
		callGraph = new FunctionCallGraph();
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
		return "Copyright 2007-2016, New York University";
	}

	public String getName() {
		return "Cascade";
	}

	public String getVersion() {
		return "2.0";
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
				"Mark AST nodes with types.").bool(OPTION_PEDANTIC,
						OPTION_INTERNAL_PEDANTIC, false, "Enforce strict C99 compliance.");

		TheoremProverFactory.discover();

		TheoremProver.Provider cvc4Tp = new edu.nyu.cascade.cvc4.TheoremProverImpl.Provider();
		TheoremProverFactory.register(cvc4Tp);
		TheoremProver.Provider z3Tp = new edu.nyu.cascade.z3.TheoremProverImpl.Provider();
		TheoremProverFactory.register(z3Tp);

		for (Option opt : TheoremProverFactory.getOptions()) {
			options.addOption(opt);
		}
	}

	public Node parseSourceFile(File file) throws IOException, ParseException {
		Reader in = new FileReader(file);
		CParser parser = null;
		Result result = null;

		/* .i file is a preprocessed file, no need to further preprocessing */
		if (FileUtils.isISourceFile(file)) {
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
					throw new ParseException(
							"Preprocessor failed (retcode=" + returnCode + ")");
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

	public void prepare() {
		Preconditions.checkArgument(asts.isEmpty());
		Preconditions.checkArgument(cfgs.isEmpty());
		// Preconditions.checkArgument(cAnalyzer == null);
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
				IOUtils.setTpFileStream(
						new PrintStream(Preferences.getFile(OPTION_SMT2_FILE)));
			}
		} catch (FileNotFoundException e) {
			failOnException(e);
		}

		/* Set the byte-based or value-based encoding */
		if (Preferences.isSet(Preferences.OPTION_MULTI_CELL)
				|| Preferences.isSet(Preferences.OPTION_VARI_CELL)) {
			Preferences.set(Preferences.OPTION_BYTE_BASED);
		}

		try {
			theoremProver = TheoremProverFactory.getInstance();

			if (Preferences.isSet(OPTION_DRY_RUN)) {
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
		IOUtils.debug().pln("cpp_command: \'" + cpp_command + "\'");

		File preprocessedSource = File.createTempFile(file.getName() + ".", ".E");
		ArgList argsList = CommandTokenizer.tokenize(cpp_command);
		argsList.append(preprocessedSource.toString(), file.toString());
		String args[] = argsList.toArray();
		IOUtils.debug().pln("cpp args: [\'" + Joiner.on("' '").join(args) + "\']");

		Process preprocessor = java.lang.Runtime.getRuntime().exec(args);
		try {
			int returnCode = preprocessor.waitFor();
			if (returnCode != 0) {
				preprocessedSource.delete();
				throw new ParseException(
						"Preprocessor failed (retcode=" + returnCode + ")");
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
		new HelpFormatter().printHelp(writer, 78,
				name + " [OPTIONS...] FILE [FILES...]\n", "Options:", options, 2, 4,
				"");
		writer.flush();
	}

	private void printVersion() {
		IOUtils.out().println(getVersion());
	}

	private void printOptions() {
		StringBuilder menuBuilder = new StringBuilder().append("Options: {");
		for (Entry<String, Object> prop : Preferences.getProperties().entrySet()) {
			String label = prop.getKey();
			menuBuilder.append("\n\t").append(label).append(' ');
			Object value = prop.getValue();
			if (value instanceof Unit)
				continue;
			menuBuilder.append(prop.getValue());
		}
		menuBuilder.append("\n}");
		IOUtils.stats().pln(menuBuilder.toString());
	}

	private void printTimeInfo(PrintStream out) {
		long runTime = StatsTimer.cascadeElapseTime();
		long solverTime = theoremProver.getStatsTime();
		double encoding = (runTime - solverTime) / 1000.0;
		out.append("Encoding took ").append(String.valueOf(encoding)).append('s')
				.append('\n');
		out.append(theoremProver.getProviderName()).append(" took ")
				.append(String.valueOf(solverTime / 1000.0)).append('s').append('\n');
		out.append(getName()).append(" took ")
				.append(String.valueOf(runTime / 1000.0)).append('s').append('\n');
		out.flush();
	}

	public List<String> processCommandLine(String[] args) {
		CommandLineParser commandLineParser = new DefaultParser();
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
		IOUtils.debug().pln("<source>").incr().flush();
		IOUtils.debugC(ast);
		IOUtils.debug().decr().pln("\n</source>").pln("<ast>").incr().format(ast)
				.decr().pln("\n</ast>").flush();

		xtc.util.SymbolTable xtcSymbolTable = cAnalyzer.analyze(ast);
		symbolTable = CSymbolTable.create(file, symbolTableFactory, xtcSymbolTable);
		Map<Node, IRControlFlowGraph> currCfgs = CfgBuilder.getCfgs(symbolTable,
				ast, callGraph);
		FuncInlineProcessor<?> funcInliner = FuncInlineProcessor
				.create(symbolTable);
		funcInliner.inlineMalloc(currCfgs, callGraph);
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
		} catch (TimeoutException e) {
			future.cancel(true);
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
				if (!file.exists())
					failOnError("Cannot open file: " + file);

				assert (FileUtils.isCSourceFile(file) || FileUtils.isISourceFile(file));

				Preferences.set(OPTION_NO_THREADS); // threads will cause broken pipe in
																						// parse source file

				try {

					Node ast = parseSourceFile(file);
					processSourceFile(file, ast);
					printOptions();

					if (Preferences.isSet(OPTION_PARSEC))
						return;

					IRControlFlowGraph mainCfg = getControlFlowGraph(Identifiers.MAIN);

					if (mainCfg == null) {
						IOUtils.err().println("no main function.");
						return;
					}

					Mode mode = AbstractMode.getMode(theoremProver);

					RunProcessor runProcessor = RunProcessorImpl.create(mode, symbolTable,
							cfgs, callGraph);

					if (Preferences.isSet(Preferences.OPTION_TRACE))
						IOUtils.enableTrace(file);

					if (Preferences.isSet(Preferences.OPTION_REACHABILITY)) {
						final String label = Preferences
								.getString(Preferences.OPTION_REACHABILITY);
						runProcessor.init(label);
						if (!preprocess(runProcessor, mainCfg))
							return;

						/* Merge graph and function inline */
						runProcessor.prepare(mainCfg);

						/* Simplify mainCFG (function-inline may introduce dead blocks) */
						CfgProcessor.simplifyCFG(mainCfg, label);

						check(runProcessor, mainCfg, new EncodingStrategy() {
							@Override
							public SafeResult apply(RunProcessor processor,
									IRControlFlowGraph cfg, LoopInfo loopInfo, Integer iterTimes)
									throws RunProcessorException {
								return processor.processReachability(cfg, loopInfo, label,
										iterTimes);
							}
						});
					} else {
						runProcessor.init();
						if (!preprocess(runProcessor, mainCfg))
							return;

						/* Merge graph and function inline */
						runProcessor.prepare(mainCfg);

						/* Simplify mainCFG (function-inline may introduce dead blocks) */
						CfgProcessor.simplifyCFG(mainCfg);

						check(runProcessor, mainCfg, new EncodingStrategy() {
							@Override
							public SafeResult apply(RunProcessor processor,
									IRControlFlowGraph cfg, LoopInfo loopInfo, Integer iterTimes)
									throws RunProcessorException {
								return processor.processAssertion(cfg, loopInfo, iterTimes);
							}
						});
					}

				} catch (RunProcessorException e) {
					failOnException(e);
				} catch (ExpressionFactoryException e) {
					failOnException(e);
				}
			}
		}
		
		if (Preferences.isSet(OPTION_DRY_RUN)) return;
		
		IOUtils.out().println(safeResult);
		StatsTimer.cascadeStop();
		printTimeInfo(IOUtils.err());
	}

	private IRControlFlowGraph getControlFlowGraph(String filename) {
		return Iterables.find(cfgs.values(), new Predicate<IRControlFlowGraph>() {
			@Override
			public boolean apply(IRControlFlowGraph cfg) {
				return cfg.getName().equals(Identifiers.MAIN);
			}
		}, null);
	}

	public Collection<IRControlFlowGraph> getControlFlowGraphs() {
		return cfgs.values();
	}

	public SymbolTable getSymbolTable() {
		return symbolTable;
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

	private boolean preprocess(RunProcessor runProcessor,
			IRControlFlowGraph mainCfg) {
		if (Preferences.isSet(OPTION_FEASIBILITY))
			runProcessor.enableFeasibilityChecking();

		long preTime = StatsTimer.cascadeElapseTime();
		runProcessor.preprocess();

		double aliastime = StatsTimer.cascadeElapseTime() - preTime;
		IOUtils.err()
				.println("Points-to-analysis took " + aliastime / 1000.0 + "s");

		Pair<Integer, Integer> aliasStats = runProcessor.getAliasAnalysisStats();
		IOUtils.err().println("Total " + aliasStats.fst() + " lvals");
		IOUtils.err().println("Total " + aliasStats.snd() + " alias groups");

		/* Merge graph and function inline */
		runProcessor.prepare(mainCfg);

		if (Preferences.isSet(OPTION_CHECK_FUNC_INLINE)
				&& !runProcessor.isFullyFuncInlined(mainCfg)) {
			safeResult = SafeResult.unknown("Insufficient_function_inline");
			printResult(0, IOUtils.outPrinter());
			return false;
		}

		return true;
	}

	private void check(RunProcessor runProcessor, IRControlFlowGraph mainCfg,
			EncodingStrategy strategy) throws RunProcessorException {

		LoopInfo loopInfo = LoopInfoUtil.analyze(mainCfg);

		/* No Loop in mainCFG */
		if (loopInfo.getTopLevelLoops().isEmpty()) {
			int iterTime = 0;

			safeResult = strategy.apply(runProcessor, mainCfg, loopInfo, iterTime);
			printResult(iterTime, IOUtils.outPrinter());
			if (safeResult.isUnsafe())
				runProcessor.dumpErrorTrace(mainCfg);
			return;
		}

		if (!Preferences.isSet(Preferences.OPTION_INCREMENTAL)) {
			int iterTime = Preferences.isSet(Preferences.OPTION_ITERATION_TIMES)
					? Preferences.getInt(Preferences.OPTION_ITERATION_TIMES) : 0;

			safeResult = strategy.apply(runProcessor, mainCfg, loopInfo, iterTime);
			printResult(iterTime, IOUtils.outPrinter());
			if (safeResult.isUnsafe())
				runProcessor.dumpErrorTrace(mainCfg);
		} else {
			Collection<Integer> iterTimesSet = Sets
					.newTreeSet(Preferences.REACH_MAGIC_ITER_TIMES);
			boolean checkKeepUnroll = Preferences
					.isSet(Preferences.OPTION_CHECK_KEEP_UNROLL);
			boolean checkExitUnroll = Preferences
					.isSet(Preferences.OPTION_CHECK_EXIT_UNROLL);

			for (int currIterTime : iterTimesSet) {
				if (checkKeepUnroll)
					runProcessor.enableCheckKeepUnroll();
				if (checkExitUnroll)
					runProcessor.enableCheckExitUnroll();

				safeResult = strategy.apply(runProcessor, mainCfg, loopInfo,
						currIterTime);
				if (safeResult.isUnsafe()) {
					printResult(currIterTime, IOUtils.outPrinter());
					runProcessor.dumpErrorTrace(mainCfg);
					break;
				}

				if (checkKeepUnroll || checkExitUnroll) {
					if (checkKeepUnroll && !runProcessor.checkKeepUnroll()) {
						printResult(currIterTime, IOUtils.outPrinter());
						break;
					}

					if (checkExitUnroll && !runProcessor.checkExitUnroll()) {
						printResult(currIterTime, IOUtils.outPrinter());
						break;
					}

					safeResult = SafeResult.unknown(INSUFFICIENT_UNROLL);
				}

				printResult(currIterTime, IOUtils.outPrinter());
				runProcessor.reset();
			}
		}
	}

	private void printResult(int iterTime, Printer printer) {
		// Skip printing result for dry-run only
		if (Preferences.isSet(OPTION_DRY_RUN)) return;
		String funcInline = Preferences.isSet(Preferences.OPTION_FUNC_INLINE)
				? Preferences.getString(Preferences.OPTION_FUNC_INLINE) : "all-inline";
		IOUtils.outPrinter().p('{').p(iterTime).p(':').p(funcInline).p("}..")
				.p(safeResult.toString()).pln();
	}

	/**
	 * Take an C program input and pass it through the C preprocessor, returning a
	 * {@link java.io.Reader Reader} for the output of the preprocessor.
	 * 
	 * @throws IOException
	 *           if an I/O error occurs
	 */
	private PipedInputProcess startPreprocessorThread(Reader source, File file)
			throws IOException {
		String cpp_command = Preferences.getString(C_PREPROCESSOR);
		assert (cpp_command != null);
		IOUtils.debug().pln("cpp_command: \'" + cpp_command + "\'");

		ArgList argsList = CommandTokenizer.tokenize(cpp_command);
		argsList.append(file.toString());
		String args[] = argsList.toArray();
		IOUtils.debug().pln("cpp args: [\'" + Joiner.on("' '").join(args) + "\']");
		PipedInputProcess preprocessor = new PipedInputProcess(args, source);
		preprocessor.run();
		return preprocessor;
	}
}
