package edu.nyu.cascade.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Map;
import java.util.Properties;
import java.util.regex.Pattern;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;

import com.google.common.collect.Maps;

/** A global repository for runtime preferences.
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

  public static final File DEFAULT_CONFIG_DIRECTORY = new File(System.getProperty("user.home"), ".cascade");
  private static final String DEFAULT_PROPERTIES_FILE_NAME = "cascade.properties";
  private static final File DEFAULT_PROPERTIES_FILE = new File(DEFAULT_CONFIG_DIRECTORY, DEFAULT_PROPERTIES_FILE_NAME);
  
  /** User-defined properties */
  private static final Map<String, Object> PROPERTIES = Maps.newHashMap();

  public static final String OPTION_SOUND_ALLOC = "sound-alloc";
  
  public static final String OPTION_COUNTER_EXAMPLE = "counter-example";

  public static final String OPTION_PLUGINS_DIRECTORY = "plugins";
  
  public static final String OPTION_ITERATION_TIMES = "iter-times";
  
  public static final String OPTION_ORDER_ALLOC = "order-alloc";
  
  public static final String OPTION_SIGNED_OPERATION = "signed";
  
  public static final String OPTION_MEM_CELL_SIZE = "mem-cell-size";
  
  public static final String OPTION_PARTIAL_INST = "partial-inst";
  
  public static final String OPTION_TOTAL_INST = "total-inst";
  
  public static final String OPTION_ENCODE_FIELD_ARRAY = "field-array";
  
  public static final String OPTION_THEORY = "theory";
  
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
    String fileName = (String)getProperties().get(option);
    return fileName==null ? null : new File(fileName);
  }
  
  public static File[] getFiles(String option) {
    String fileNames = (String)getProperties().get(option);
    String[] fileNameArr = fileNames.split(Pattern.quote(","));
    File[] fileArr = new File[fileNameArr.length];
    int i = 0;
    for(String fileName : fileNameArr) {
      fileArr[i++] = fileName==null ? null : new File(fileName);
    }
    return fileArr;
  }

  public static int getInt(String option) {
    Object val = getProperties().get(option);
    if( val instanceof Integer ) {
      return (Integer) val;
    } else if ( val instanceof String ) {
      return Integer.parseInt( (String)val );
    } else {
      throw new ClassCastException("Could not cast " + val.getClass() + "to int.");
    }
  }
  
  private static Map<String,Object> getProperties() { return PROPERTIES; }
  
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
  
  /* Assumes all option values are either null or singleton. 
   * Will also discard all but the last value of any option that appears
   * more than once on the command line. */
  public static void loadCommandLine(CommandLine commandLine) {
    for( Option opt : commandLine.getOptions() ) {
      String val = opt.getValue();
      if( val == null ) {
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
   * @param file a properties file
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
   * @param path a properties file path
   * @throws IOException 
   */
  public static void loadProperties(String path) throws IOException {
    loadProperties(new File(path));
  }
  
  /**
   * Load a line-formatted properties file from {@code url} (see
   * {@link java.util.Properties#load(java.io.InputStream)}).
   * 
   * @param url a properties file resource
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
/*    for( Option opt : commandLine.getOptions() ) {
      opt.
    }
*/    if (commandLine.hasOption(option)) {
      set(option);
    }
  }
  public static void setPreference(String option, String value) {
    getProperties().put(option, value);
  }

  public static void setValueFromCommandLine(CommandLine commandLine,
      String option) {
    if (commandLine.hasOption(option)) {
      setPreference(option,commandLine.getOptionValue(option));
    }
  }

}
