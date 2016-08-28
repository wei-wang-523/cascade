package edu.nyu.cascade.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.regex.Pattern;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

/**
 * A global repository for runtime preferences.
 * 
 * NOTE: The data in this class is static, and thus is shared between all
 * threads.
 * 
 * @author Chris Conway (cconway@cs.nyu.edu)
 * @author Wei Wang (wwang1109@cims.nyu.edu)
 *
 */

public class Preferences {
	@SuppressWarnings("serial")
	public static class PreferencesException extends Exception {
		PreferencesException(Throwable e) {
			super(e);
		}
	}

	public static final File DEFAULT_CONFIG_DIRECTORY = new File(
			System.getProperty("user.home"), ".cascade");
	private static final String DEFAULT_PROPERTIES_FILE_NAME = "cascade.properties";
	private static final File DEFAULT_PROPERTIES_FILE = new File(
			DEFAULT_CONFIG_DIRECTORY, DEFAULT_PROPERTIES_FILE_NAME);

	/** User-defined properties */
	private static final Map<String, Object> PROPERTIES = Maps.newHashMap();

	public static final String OPTION_PLUGINS_DIRECTORY = "plugins";

	/** Give a trace is the assertion is invalid */
	public static final String OPTION_TRACE = "trace";

	/** Set the timeout of cascade */
	public static final String OPTION_TIMEOUT = "timeout";

	/** Enable in-line annotation */
	public static final String OPTION_INLINE_ANNOTATION = "inline-anno";

	/** Check safe memory access for all memory dereferences */
	public static final String OPTION_MEMORY_CHECK = "memory-check";

	/**
	 * Make variables are pure logic variables, if they with no the compound type
	 * and have no address-of op on it.
	 */
	public static final String OPTION_HOARE = "hoare";

	/**
	 * Incrementally check reachability until reach the function in-line bounds
	 */

	public static final String OPTION_INCREMENTAL = "incremental";

	public static final String OPTION_REACHABILITY = "reachability";

	/** Check if the unrolling bound is enough */
	public static final String OPTION_CHECK_KEEP_UNROLL = "check-keep-unroll";
	public static final String OPTION_CHECK_EXIT_UNROLL = "check-exit-unroll";

	public static final String OPTION_FUNC_INLINE = "function-inline";

	public static final String OPTION_ITERATION_TIMES = "iter-times";

	/** ------------- Options for pointer analysis ----------- */

	/** Enable field sensitive pointer analysis */
	public static final String OPTION_FIELD_SENSITIVE = "field-sensitive";

	/** Enable cell-based field sensitive pointer analysis */
	public static final String OPTION_CELL_BASED_FIELD_SENSITIVE = "cell-field-sensitive";

	/** Enable cell-based field sensitive pointer analysis */
	public static final String OPTION_CELL_BASED_FIELD_SENSITIVE_CONTEXT_SENSITIVE = "cell-field-sensitive-context-sensitive";

	/** Enable data-structure pointer analysis */
	public static final String OPTION_DSA = "dsa";

	/** -------------- memory layout encoding ----------------- */

	/**
	 * Memory layout encoding: sound (no assume an order between regions), order
	 * (assume an arbitrary order)
	 */
	public static final String OPTION_SOUND_ALLOC = "sound";
	public static final String OPTION_ORDER_ALLOC = "order";

	/** ------------------ memory cell --------------------- */

	/** Set the size of each memory cell, default value is 16 */
	public static final String OPTION_MEM_CELL_SIZE = "mem-cell-size";

	/**
	 * Enable multiple cells encoding of various data type in the real C, which is
	 * byte-unit and default cell size is 8.
	 */
	public static final String OPTION_MULTI_CELL = "multi-cell";

	/**
	 * Used the type information contained in Burstall memory model, to calculate
	 * the size of cell based on type information
	 */
	public static final String OPTION_VARI_CELL = "vari-cell";

	/**
	 * Option to set value-based or byte-based encoding: - For vari-cell and
	 * multi-cell, it is set to be true; - Otherwise, it is set to be false
	 * (value-based).
	 */
	public static final String OPTION_BYTE_BASED = "byte-based";

	/** ------------------ path encoding --------------------- */

	/**
	 * Path encoding: sequential (no ite-branch merge), merge (default),
	 * path-based
	 */
	public static final String OPTION_SBE = "small-block-encoding";

	/** ------------------ memory model theory -------------- */

	/** Options: Flat(default), Burstall, Partition */
	public static final String OPTION_MODE = "mode";

	/** Enable the lambda encoding */
	public static final String OPTION_LAMBDA = "lambda";

	/** Enable the statement lambda encoding */
	public static final String OPTION_STMT = "stmt";

	/** ------------- Theorem prover: z3, cvc4 ---------------- */
	public static final String PROVER_Z3 = "z3";
	public static final String PROVER_CVC4 = "cvc4";

	/** ------------- The 32bits machine ---------------------- */
	public static final String OPTION_M32 = "m32";

	/** ------------- The 64bits machine ---------------------- */
	public static final String OPTION_M64 = "m64";

	/** -- The pointer arithmetic optimization of cfs-pointer-analysis -- */
	public static final String OPTION_CFS_POINTER_ARITH = "cfs-ptrArith";

	/** -- Inline malloc functions in CFG -- */
	public static final String OPTION_INLINE_MALLOC = "inline-malloc";

	/** -- Memory leak check -- */
	public static final String OPTION_MEMTRACK = "memtrack";

	/** -- Two round of memory check -- */
	public static final String OPTION_TWOROUND_MEMCHECK = "two-round-check";

	/** ------------ The magic iteration times ---------------- */
	public static final List<Integer> MEM_MAGIC_ITER_TIMES = Lists.newArrayList(0,
			1, 6, 12, 17, 21, 40, 80, 100, 200);
	public static final List<Integer> REACH_MAGIC_ITER_TIMES = Lists
			.newArrayList(1, 6, 12, 17, 21, 40, 80, 100, 200, 400, 1024);

	public static void clearAll() {
		getProperties().clear();
	}

	public static void clearPreference(String option) {
		getProperties().remove(option);
	}

	public static Object get(String option) {
		return getProperties().get(option);
	}

	public static File getFile(String option) {
		String fileName = (String) getProperties().get(option);
		return fileName == null ? null : new File(fileName);
	}

	public static File[] getFiles(String option) {
		String fileNames = (String) getProperties().get(option);
		String[] fileNameArr = fileNames.split(Pattern.quote(","));
		File[] fileArr = new File[fileNameArr.length];
		int i = 0;
		for (String fileName : fileNameArr) {
			fileArr[i++] = fileName == null ? null : new File(fileName);
		}
		return fileArr;
	}

	public static int getInt(String option) {
		Object val = getProperties().get(option);
		if (val instanceof Integer) {
			return (Integer) val;
		} else if (val instanceof String) {
			return Integer.parseInt((String) val);
		} else {
			throw new ClassCastException(
					"Could not cast " + val.getClass() + "to int.");
		}
	}

	public static Map<String, Object> getProperties() {
		return PROPERTIES;
	}

	public static String getString(String option) {
		return (String) getProperties().get(option);
	}

	public static void init() throws IOException {
		if (DEFAULT_PROPERTIES_FILE.canRead()) {
			loadProperties(DEFAULT_PROPERTIES_FILE);
		} else {
			URL url = FileUtils.resourceURL(DEFAULT_PROPERTIES_FILE_NAME);

			if (url != null) {
				loadProperties(url);
			}
		}
	}

	public static boolean isSet(String option) {
		return getProperties().containsKey(option);
	}

	/*
	 * Assumes all option values are either null or singleton. Will also discard
	 * all but the last value of any option that appears more than once on the
	 * command line.
	 */
	public static void loadCommandLine(CommandLine commandLine) {
		for (Option opt : commandLine.getOptions()) {
			String val = opt.getValue();
			if (val == null) {
				set(opt.getLongOpt());
			} else {
				set(opt.getLongOpt(), val);
			}
		}
	}

	/**
	 * Load a line-formatted properties {@code file} (see
	 * {@link java.util.Properties#load(java.io.InputStream)}).
	 * 
	 * @param file
	 *          a properties file
	 * @throws IOException
	 */
	public static void loadProperties(File file) throws IOException {
		URL url = file.toURI().toURL();
		loadProperties(url);
	}

	/**
	 * Load a line-formatted properties file from the file at {@code path} (see
	 * {@link java.util.Properties#load(java.io.InputStream)}).
	 * 
	 * @param path
	 *          a properties file path
	 * @throws IOException
	 */
	public static void loadProperties(String path) throws IOException {
		loadProperties(new File(path));
	}

	/**
	 * Load a line-formatted properties file from {@code url} (see
	 * {@link java.util.Properties#load(java.io.InputStream)}).
	 * 
	 * @param url
	 *          a properties file resource
	 * @throws IOException
	 */
	public static void loadProperties(URL url) throws IOException {
		Properties p = new Properties();
		p.load(url.openStream());
		getProperties().putAll(Maps.fromProperties(p));
	}

	public static void set(String option) {
		getProperties().put(option, Unit.value());
	}

	public static void set(String option, Object value) {
		getProperties().put(option, value);
	}

	public static void setFromCommandLine(CommandLine commandLine,
			String option) {
		/*
		 * for( Option opt : commandLine.getOptions() ) { opt. }
		 */ if (commandLine.hasOption(option)) {
			set(option);
		}
	}

	public static void setPreference(String option, String value) {
		getProperties().put(option, value);
	}

	public static void setValueFromCommandLine(CommandLine commandLine,
			String option) {
		if (commandLine.hasOption(option)) {
			setPreference(option, commandLine.getOptionValue(option));
		}
	}

}
