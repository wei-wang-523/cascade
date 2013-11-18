package edu.nyu.cascade.util;

import java.io.File;
import java.io.FilenameFilter;
import java.security.Permission;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;

public class TestUtils {
  public static final String TEST_RESOURCES_DIRECTORY = FileUtils.RESOURCES_DIRECTORY;
  public static final String TEST_DATA_DIRECTORY = FileUtils.path(
      TEST_RESOURCES_DIRECTORY, "data");

  /** A function object for a JUnit tester. */
  public interface Tester<T> {
    /**
     * Run a test on the given input. This method should raise an
     * {@link AssertionError} if the test failed (e.g., by calling
     * {@link org.junit.Assert.fail}()) and otherwise return silently.
     */
    public void runTest(T in);
  }

  /**
   * Run a series of tests over the files in a directory. Prints "OK" if the
   * tests succeeds. Throws an {@link AssertionError} if any test fails.
   * 
   * @param dir
   *          the directory in which the test cases reside
   * @param filter
   *          a {@link FilenameFilter} that selects the relevant test cases from
   *          {@code dir}
   * @param tester
   *          a {@link File} tester
   * @param shouldFail
   *          {@literal true} if the tester <em>should fail</em> on the test
   *          cases, otherwise {@literal false}.
   * @throws AssertionError if any test fails (or, if {@code shouldFail} is
   *         {@literal true}, if any test succeeds).
   */
  public static void checkDirectory(File dir, FilenameFilter filter,
      Tester<File> tester, boolean shouldFail) {
    // Get all test files
    String[] tests = dir.list(filter);

    if (tests == null) {
      throw new AssertionError("No test cases found in directory: "
          + dir.getAbsolutePath());
    } else {
      for (String test : tests) {
        // Try to parse the file
        File testFile = new File(dir, test);

        // We catch any failure here so we can compare it to shouldFail below.
        AssertionError failure = null;
        try {
          tester.runTest(testFile);
        } catch (AssertionError e) {
          failure = e;
        }

        if (failure != null && !shouldFail) {
          // The test failed when it shouldn't have
          throw failure;
        } else if (failure == null && shouldFail) {
          // The test didn't fail when it should have
          throw new AssertionError("Expected failure succeeded: " + testFile);
        } else {
          // System.out.println("OK");
        }
      }
    }

  }
  
  public static void checkFile(File dir, Map<Tester<File>, String[]> optMap, 
      boolean shouldFail) {
    // Get all test files
    Preconditions.checkArgument(optMap != null);
    for (Entry<Tester<File>, String[]> optFiles : optMap.entrySet()) {
      Tester<File> tester = optFiles.getKey();
      for(String test : optFiles.getValue()) {
        // Try to parse the file
        File testFile = new File(dir, test);

        // We catch any failure here so we can compare it to shouldFail below.
        AssertionError failure = null;
        try {
          tester.runTest(testFile);
        } catch (AssertionError e) {
          failure = e;
        }

        if (failure != null && !shouldFail) {
          // The test failed when it shouldn't have
          throw failure;
        } else if (failure == null && shouldFail) {
          // The test didn't fail when it should have
          throw new AssertionError("Expected failure succeeded: " + testFile);
        } else {
          // System.out.println("OK");
        }
      }
    }
  }

  @SuppressWarnings("serial")
  public static final class ExitException extends SecurityException {
    private final int status;

    public ExitException(int status) {
      this.status = status;
    }

    public int getStatus() {
      return status;
    }
  };

  private static final SecurityManager noExitSecurityManager = new SecurityManager() {
    @Override
    public void checkPermission(Permission perm) {
      // allow anything.
    }

    @Override
    public void checkPermission(Permission perm, Object context) {
      // allow anything.
    }

    @Override
    public void checkExit(int status) {
      throw new ExitException(status);
    }
  };

  public static <T> T callMayExit(final Runnable runnable, long timeout) throws Exception {
    SecurityManager defaultSecurityManager = System.getSecurityManager();
    try {
      System.setSecurityManager(noExitSecurityManager);
      Thread thread = new Thread(runnable);
      
      long startTime = System.currentTimeMillis();
      thread.start();
      while(thread.isAlive()) {
      	Thread.sleep(30);
      	if(System.currentTimeMillis() - startTime > timeout * 1000) {
      		thread.stop();
      		IOUtils.err().println("Timeout");
      		break;
      	}
      }
      return null;
    } finally {
      System.setSecurityManager(defaultSecurityManager);
    }
    /*
     * FutureTask<T> task = new FutureTask<T>(callable); task.run(); return
     * task.get();
     */}

}
