package edu.nyu.cascade.c;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import xtc.parser.ParseException;

@RunWith(Parameterized.class)
public class DryRunInjectTest {
	private static final File programs_c = FileUtils.absoluteResourcePath("c");
	private static final File syntax = FileUtils.absoluteResourcePath("syntax");
	private static final File nec_bnc = FileUtils.filePath(programs_c, "nec_bnc");
	// TODO: inline-anno : nec_inline_bnc

	private Main main;
	private File cfile;

	@Parameterized.Parameters
	public static Collection<File> cFiles() {
		File[] dirs = { syntax, nec_bnc /* , nec_inline */ };
		Collection<File> fileList = Lists.newArrayList();

		// Make the C files filter
		FilenameFilter filter = new FilenameFilter() {
			public boolean accept(File dir, String name) {
				return name.endsWith(".c");
			}
		};

		for (File dir : dirs) {
			fileList.addAll(ImmutableList.copyOf(dir.listFiles(filter)));
		}

		return fileList;
	}

	public DryRunInjectTest(File file) {
		IOUtils.enableOut();
		main = getInjector().getInstance(Main.class);
		main.init();
		main.prepare();
		main.setErrStream(IOUtils.NULL_PRINT_STREAM);
		cfile = file;
	}

	@After
	public void tearDown() {
		ValueManager.reset();
	}

	@Test
	public void testDryRun() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--dry-run", cfile.toString() };
		IOUtils.out().println("Dry-run:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}

	@Test
	public void testLambda() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--lambda", "--dry-run", cfile
				.toString() };
		IOUtils.out().println("Dry-run lambda:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}

	@Test
	public void testVariCell() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--dry-run", "--vari-cell", cfile
				.toString() };
		IOUtils.out().println("Dry-run vari-cell:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}

	@Test
	public void testMultiCell() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--dry-run", "--multi-cell", cfile
				.toString() };
		IOUtils.out().println("Dry-run multi-cell:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}

	@Test
	public void testLambdaVariCell() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--lambda", "--dry-run",
				"--vari-cell", cfile.toString() };
		IOUtils.out().println("Dry-run vari-cell:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}

	@Test
	public void testLambdaMultiCell() throws ParseException, IOException {
		String[] args = { "--iter-times", "1", "--lambda", "--dry-run",
				"--multi-cell", cfile.toString() };
		IOUtils.out().println("Dry-run multi-cell:" + cfile.toString());
		List<String> cmds = main.processCommandLine(args);
		main.run(cmds);
	}
}
