package edu.nyu.cascade.c.pass.alias.dsa;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.Collection;
import java.util.Map.Entry;

import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.CPrinter;
import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.c.pass.addrtaken.AddressTakenAnalysis;
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
public class RegionPassImplTest {
	private static final File programs_syntax = FileUtils.absoluteResourcePath(
			"syntax");
	private static final File programs_c = FileUtils.absoluteResourcePath("c");
	private static final File mini_invalids = FileUtils.filePath(programs_c,
			"mini_bnc", "invalid");
	private static final File mini_valids = FileUtils.filePath(programs_c,
			"mini_bnc", "valid");
	private static final File nec_programs = FileUtils.filePath(programs_c,
			"nec_bnc");

	private Main main;
	private File cfile;

	@Parameterized.Parameters
	public static Collection<File> cFiles() {
		File[] programs_dirs = { programs_syntax, mini_invalids, mini_valids,
				nec_programs };
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

	public RegionPassImplTest(File file) {
		Preferences.set(Preferences.OPTION_BYTE_BASED);
		main = getInjector().getInstance(Main.class);
		main.init();
		main.prepare();
		IOUtils.enableOut();
		cfile = file;
	}

	@After
	public void tearDown() {
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
		AddressTakenAnalysis addrTakenPass = AddressTakenAnalysis.create(
				symbolTable);
		addrTakenPass.analysis(globalCFG, CFGs);

		DataStructures localds = LocalDataStructureImpl.create(addrTakenPass).init(
				symbolTable);
		localds.analysis(globalCFG, CFGs);

		DataStructures steensds = SteensDataStructureImpl.create(localds).init(
				symbolTable);
		steensds.analysis(globalCFG, CFGs);

		RegionPassImpl regionPass = RegionPassImpl.create(steensds);
		regionPass.runOnModule(globalCFG, CFGs);

		Printer out = IOUtils.debug();
		out.pln(cfile.getName());

		out.incr();
		CPrinter cout = new CPrinter(out);
		for (Entry<Pair<Node, String>, Region> entry : regionPass.getRegionMap()
				.entrySet()) {
			out.indent().p(":" + entry.getValue());
			cout.dispatch(entry.getKey().fst());
			out.pln();
		}

		out.decr();
		out.flush();
	}
}
