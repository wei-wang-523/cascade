package edu.nyu.cascade.c.pass.alias.dsa;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.Collection;

import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import com.google.common.base.Predicate;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.c.CPrinter;
import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.c.pass.alias.LeftValueCollectingPassImpl;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import xtc.parser.ParseException;
import xtc.tree.Node;
import xtc.tree.Printer;

@RunWith(Parameterized.class)
public class DSAAnalysisStatsTest {
	private static final File programs_syntax = FileUtils.absoluteResourcePath(
			"syntax");
	private static final File programs_c = FileUtils.absoluteResourcePath("c");
	private static final File mini_invalids = FileUtils.filePath(programs_c,
			"mini_bnc", "invalid");
	private static final File mini_valids = FileUtils.filePath(programs_c,
			"mini_bnc", "valid");
	private static final File nec_programs = FileUtils.filePath(programs_c,
			"nec_bnc");
	private static final File alias_programs = FileUtils.filePath(programs_c,
			"alias");

	private Main main;
	private File cfile;

	@Parameterized.Parameters
	public static Collection<File> cFiles() {
		File[] programs_dirs = { alias_programs };
		Collection<File> fileList = Lists.newArrayList();

		for (File programs_dir : programs_dirs) {
			// Make the C files filter
			FilenameFilter filter = new FilenameFilter() {
				public boolean accept(File dir, String name) {
					return name.endsWith(".c");
				}
			};

			// Get all C files
			String[] c_tests = programs_dir.list(filter);

			if (c_tests == null)
				continue;

			for (int i = 0; i < c_tests.length; i++) {
				fileList.add(new File(programs_dir, c_tests[i]));
			}
		}

		return fileList;
	}

	public DSAAnalysisStatsTest(File file) {
		main = getInjector().getInstance(Main.class);
		main.init();
		main.prepare();
		cfile = file;

		IOUtils.enableOut();
		Preferences.set(Preferences.OPTION_BYTE_BASED);
	}

	@After
	public void tearDown() throws Exception {
		ValueManager.reset();
		DSNodeImpl.reset();
	}

	@Test
	public void test() throws ParseException, IOException {
		Node ast = main.parseSourceFile(cfile);
		main.processSourceFile(cfile, ast);
		Collection<IRControlFlowGraph> CFGs = main.getControlFlowGraphs();

		IRControlFlowGraph globalCFG = Iterables.find(CFGs,
				new Predicate<IRControlFlowGraph>() {
					@Override
					public boolean apply(IRControlFlowGraph cfg) {
						return cfg.getName().equals(Identifiers.GLOBAL_CFG);
					}
				});
		CFGs.remove(globalCFG);

		SymbolTable symbolTable = main.getSymbolTable();
		DSAAnalysis dsa = DSAAnalysis.create(symbolTable);
		dsa.analysis(globalCFG, CFGs);

		LeftValueCollectingPassImpl lvalCollector = new LeftValueCollectingPassImpl();
		lvalCollector.analysis(globalCFG, CFGs);
		Collection<Pair<Node, String>> lvals = lvalCollector.getLeftValues();
		Multimap<DSNodeHandle, Pair<Node, String>> aliasMap = ArrayListMultimap
				.create();
		for (Pair<Node, String> lval : lvals) {
			DSNodeHandle NH = dsa.getRep(lval.fst());
			aliasMap.put(NH, lval);
		}

		Printer printer = IOUtils.outPrinter();
		Printer debugPrinter = IOUtils.outPrinter();
		CPrinter cprinter = new CPrinter(debugPrinter);

		printer.p(cfile.getName()).p(',').p(lvals.size()).p(',').p(aliasMap.keySet()
				.size()).pln();

		debugPrinter.incr();
		for (DSNodeHandle NH : aliasMap.keySet()) {
			Collection<Pair<Node, String>> aliasGroup = aliasMap.get(NH);
			if (aliasGroup.size() <= 1)
				continue;
			debugPrinter.p(NH.getNode().getID().intValue()).p(':').p(NH.getOffset());
			for (Pair<Node, String> lval : aliasGroup) {
				debugPrinter.pln().p('\t');
				cprinter.dispatch(lval.fst());
				debugPrinter.p(lval.snd());
			}
			debugPrinter.pln();
		}
		debugPrinter.decr().pln();

		printer.flush();
		debugPrinter.flush();
	}
}
