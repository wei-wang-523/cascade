package edu.nyu.cascade.util;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;

public class FileUtils {
  private static final String[] C_FILES_SUFFIXES = { ".c", ".C" };
  private static final String[] I_FILES_SUFFIXES = { ".i", ".I" };
  private static final String[] CONTROL_FILE_SUFFIXES = { ".ctrl" };
  
  protected static final String RESOURCES_DIRECTORY = "META-INF";

  private static final Joiner PATH_JOINER = Joiner.on(File.separator);
  
  public static boolean suffixIn(File file, String[] suffixes) {
    String path = file.getAbsolutePath();
    for (String suffix : suffixes) {
      if (path.endsWith(suffix)) {
        return true;
      }
    }
    return false;
  }
  
  public static boolean isCSourceFile(File file) {
    return suffixIn(file, C_FILES_SUFFIXES);
  }
  
  public static boolean isISourceFile(File file) {
  	return suffixIn(file, I_FILES_SUFFIXES);
  }

  public static boolean isControlFile(File file) {
    return suffixIn(file, CONTROL_FILE_SUFFIXES);
  }
  
  public static File filePath(File dir, String first, String... rest) {
    return new File(dir, path(first, rest));
  }

  public static String path(String dir, String... rest) {
    return PATH_JOINER.join(Lists.asList(dir,rest));
  }

  public static URL resourceURL(String... pathComponents) {
    return ClassLoader.getSystemResource(resourcePath(pathComponents).toString());
  }
  
  public static String resourcePath(String... pathComponents) {
    return path(RESOURCES_DIRECTORY, pathComponents);
  }

  public static File absoluteResourcePath(String... pathComponents) {
    try {
      URL url = resourceURL(pathComponents);
      return new File(url.toURI());
    } catch (URISyntaxException e) {
      throw new AssertionError("Unexpected URISyntaxException:" + e);
    }
  }
  
}
