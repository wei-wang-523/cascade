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
public class InjectTestMain {
	private static final File programs_c = FileUtils
			.absoluteResourcePath("c");
	private static final File mini_invalids = FileUtils.filePath(programs_c,
			"mini_bnc", "invalid");
	private static final File mini_valids = FileUtils.filePath(programs_c,
			"mini_bnc", "valid");

	private Main main;
	private File cfile;
	
	@Parameterized.Parameters
	public static Collection<File> cFiles() {
		Collection<File> fileList = Lists.newArrayList();
		
		// Make the C files filter
	    FilenameFilter filter = new FilenameFilter() {
	    	public boolean accept(File dir, String name) {
	    		return name.endsWith(".c");
	    	}
	    };
	    
	    FilenameFilter falseDerefFilter = new FilenameFilter() {
	        public boolean accept(File dir, String name) {
	          return name.endsWith("_false-valid-deref.c");
	        }
	    };
	      
	    FilenameFilter falseFreeFilter = new FilenameFilter() {
	        public boolean accept(File dir, String name) {
	          return name.endsWith("_false-valid-free.c");
	        }
	    };
	    
	    FilenameFilter falseMemtrackFilter = new FilenameFilter() {
	    	public boolean accept(File dir, String name) {
	    		return name.endsWith("_false-valid-memtrack.c");
	    	}
	    };
	      
	    FilenameFilter falseAssertFilter = new FilenameFilter() {
	    	public boolean accept(File dir, String name) {
	    		return name.endsWith("_false-valid-assert.c");
	    	}
	    };
		
		fileList.addAll(ImmutableList.copyOf(
				mini_invalids.listFiles(falseDerefFilter)));
		fileList.addAll(ImmutableList.copyOf(
				mini_invalids.listFiles(falseFreeFilter)));
		fileList.addAll(ImmutableList.copyOf(
				mini_invalids.listFiles(falseMemtrackFilter)));
		fileList.addAll(ImmutableList.copyOf(
				mini_invalids.listFiles(falseAssertFilter)));
		fileList.addAll(ImmutableList.copyOf(
				mini_valids.listFiles(filter)));
		
    	return fileList;
	}
	
	public InjectTestMain(File file) {
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
	public void testDSA() throws ParseException, IOException {
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
	  	IOUtils.out().println("DSA:" + cfile.toString());
	  	List<String> cmds = main.processCommandLine(args);
	  	main.run(cmds);
	}
	
	@Test
	public void testCFS() throws ParseException, IOException {
	  	String[] args = {
	  			"--inline-anno", 
	  			"--iter-times", "10", 
	  			"-m32", 
	  			"--vari-cell", 
	  			"--lambda", 
	  			"--memory-check", 
	  			"--hoare", 
	  			"-cfs",
	  			cfile.toString()};
	  	IOUtils.out().println("CFS:" + cfile.toString());
	  	List<String> cmds = main.processCommandLine(args);
	  	main.run(cmds);
	}
	
	@Test
	public void testCFSCS() throws ParseException, IOException {
	  	String[] args = {
	  			"--inline-anno", 
	  			"--iter-times", "10", 
	  			"-m32", 
	  			"--vari-cell", 
	  			"--lambda", 
	  			"--memory-check", 
	  			"--hoare", 
	  			"-cfscs",
	  			cfile.toString()};
	  	IOUtils.out().println("CFSCS:" + cfile.toString());
	  	List<String> cmds = main.processCommandLine(args);
	  	main.run(cmds);
	}
}
