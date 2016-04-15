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

import com.google.common.collect.Lists;

import edu.nyu.cascade.c.Main;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.util.FileUtils;
import edu.nyu.cascade.util.IOUtils;
import xtc.parser.ParseException;

@RunWith(Parameterized.class)
public class MainInjectTest {
	private static final File programs_syntax = FileUtils
			.absoluteResourcePath("syntax");
	private static final File programs_c = FileUtils
			.absoluteResourcePath("c");
	private static final File mini_invalids = FileUtils.filePath(programs_c,
			"mini_bnc", "invalid");
	private static final File mini_valids = FileUtils.filePath(programs_c,
			"mini_bnc", "valid");
	private static final File nec_programs = new File(programs_c,
			"nec_bnc");

	private Main main;
	private File cfile;
	
	@Parameterized.Parameters
	public static Collection<File> cFiles() {		
		File[] programs_dirs = { /* programs_syntax, mini_invalids, */ mini_invalids /*, nec_programs */};
		Collection<File> fileList = Lists.newArrayList();
		
		for(File programs_dir : programs_dirs) {
			// Make the C files filter
		    FilenameFilter filter = new FilenameFilter() {
		    	public boolean accept(File dir, String name) {
		    		return name.endsWith(".c");
		    	}
		    };

		    // Get all C files
		    String[] c_tests = programs_dir.list(filter);

		    if (c_tests == null) continue;
		    
		    for (int i = 0; i < c_tests.length; i++) {
		    	fileList.add(new File(programs_dir, c_tests[i]));
		    }
		}
		
    	return fileList;
	}
	
	public MainInjectTest(File file) {
        IOUtils.enableOut();
//        IOUtils.enableDebug();
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
	public void test() throws ParseException, IOException {
	  	String[] args = {
	  			"--inline-anno", 
	  			"--iter-times", "10", 
	  			"-m32", 
	  			"--vari-cell", 
	  			"--lambda", 
	  			"--memory-check", 
	  			"--hoare", 
	  			"-dsa",
	  			cfile.toString()};
	  	IOUtils.out().println(cfile.toString());
	  	List<String> cmds = main.processCommandLine(args);
	  	main.run(cmds);
	}
}
