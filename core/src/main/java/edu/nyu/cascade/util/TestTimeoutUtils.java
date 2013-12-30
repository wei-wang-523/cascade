package edu.nyu.cascade.util;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import xtc.parser.ParseException;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.TheoremProverException;

public class TestTimeoutUtils {
	
  /** A function object for a JUnit tester. */
  public interface Task<T> extends Callable<Void> {
  }
  
  public static class TaskBuilder<T> {
  	private Function<T, Void> function;
  	
  	public TaskBuilder() {}
  	
  	public TaskBuilder<T> setFunction(Function<T, Void> _function) {
  		function = _function;
  		return this;
  	}
  	
  	public Task<T> createTask(final T in) {
  		return new Task<T>() {
				@Override
        public Void call() 
        		throws IOException, ParseException, TheoremProverException {
	        return function.apply(in);
        }
  		};
  	}
  }
  
  /**
   * Add a series of tests over the files in a directory. Prints "OK" if the
   * tests succeeds.
   * 
   * @param builder
   * 					the builder to add task in
   * 
   * @param dir
   *          the directory in which the test cases reside
   * @param filter
   *          a {@link FilenameFilter} that selects the relevant test cases from
   *          {@code dir}
   * @param task
   *          a {@link File} task
   */
  public static void checkDirectory(Scheduler scheduler, File dir, FilenameFilter filter,
      TaskBuilder<File> builder) {
    // Get all test files
    String[] tests = dir.list(filter);

    if (tests == null) {
      throw new AssertionError("No test cases found in directory: "
          + dir.getAbsolutePath());
    } else {
      for (String test : tests) {
        // Try to parse the file
        File testFile = new File(dir, test);
        scheduler.addTask(builder.createTask(testFile));
      }
    }
  }
  
  public static class Scheduler {
  	private final List<Task<?>> tasks;
  	private long timeout;
  	
	  public Scheduler(long _timeout) {
	  	Preconditions.checkArgument(_timeout > 0);
			timeout = _timeout;
	  	tasks = Lists.newArrayList();
	  }
	  
		public TestTimeoutUtils.Scheduler addTask(Task<File> task) {
			Preconditions.checkNotNull(tasks);
			tasks.add(task);
	    return this;
    }
		
    public TestTimeoutUtils run() {
	    return TestTimeoutUtils.create(tasks, timeout);
    }
  }
  
  public static TestTimeoutUtils create(List<Task<?>> tasks, long timeout) {
    return new TestTimeoutUtils(tasks, timeout);
  }
  
  public TestTimeoutUtils(List<Task<?>> tasks, long timeout) {
  	Preconditions.checkNotNull(tasks);
  	Preconditions.checkArgument(timeout > 0);
  	final ExecutorService executor = Executors.newFixedThreadPool(tasks.size());
  	Iterable<Future<?>> futures = Iterables.transform(tasks, new Function<Task<?>, Future<?>>(){
			@Override
      public Future<?> apply(Task<?> task) {
	      return executor.submit(task);
      }
  	});
  	
  	for(Future<?> future : futures) {
  		try {
	      future.get(timeout, TimeUnit.SECONDS);
      } catch (InterruptedException e) {
	      // TODO Auto-generated catch block
	      e.printStackTrace();
      } catch (ExecutionException e) {
	      // TODO Auto-generated catch block
	      e.printStackTrace();
      } catch (TimeoutException e) {
	      IOUtils.err().println("Timeout");
	      future.cancel(true);
      }
  	}
  	
  	executor.shutdownNow();
  }
}