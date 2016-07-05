package edu.nyu.cascade.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.StringWriter;
import java.io.Writer;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * A process that takes its input from a given Reader.
 * 
 * @author Chris Conway
 *
 */
public class PipedInputProcess implements Runnable, Future<Integer> {
	// private static final int DEFAULT_BUFFER_SIZE = 4096;

	public static interface CleanupStrategy {
		public void cleanUp();
	}

	private final FutureTask<Integer> task;
	private final InputStream taskOutput;
	// private final Reader inputReader;
	// private final Process process;
	// private final Writer outputWriter;
	private final CleanupStrategy cleanupStrategy;

	public PipedInputProcess(final String[] command, final Reader inputReader,
			final CleanupStrategy cleanupStrategy) throws IOException {
		// this.inputReader = inputReader;
		final Process process = Runtime.getRuntime().exec(command);

		this.task = new FutureTask<Integer>(new Callable<Integer>() {
			@Override
			public Integer call() throws ExecutionException {
				try {
					Writer outputWriter = new OutputStreamWriter(process
							.getOutputStream());
					IOUtils.pipeReader(inputReader, outputWriter);
					outputWriter.close();
					int returnCode = process.waitFor();
					return returnCode; // Integer.valueOf(returnCode);
				} catch (IOException e) {
					throw new ExecutionException(e);
				} catch (InterruptedException e) {
					throw new ExecutionException(e);
				}
			}
		});
		this.taskOutput = process.getInputStream();
		this.cleanupStrategy = cleanupStrategy;
	}

	public PipedInputProcess(final String[] command, final Reader inputReader)
			throws IOException {
		this(command, inputReader, new CleanupStrategy() {
			@Override
			public void cleanUp() {
			}
		});
	}

	public Reader getOutputAsReader() {
		return new InputStreamReader(taskOutput);
	}

	public CharSequence getOutputAsSequence() throws IOException {
		Reader inputReader = getOutputAsReader();
		Writer outputWriter = new StringWriter();
		IOUtils.pipeReader(inputReader, outputWriter);
		return outputWriter.toString();
	}

	@Override
	public void run() {
		task.run();
	}

	@Override
	public boolean cancel(boolean mayInterruptIfRunning) {
		return task.cancel(mayInterruptIfRunning);
	}

	@Override
	public Integer get() throws InterruptedException, ExecutionException {
		return task.get();
	}

	@Override
	public Integer get(long timeout, TimeUnit unit) throws InterruptedException,
			ExecutionException, TimeoutException {
		return task.get(timeout, unit);
	}

	@Override
	public boolean isCancelled() {
		return task.isCancelled();
	}

	@Override
	public boolean isDone() {
		return task.isDone();
	}

	/*
	 * private final Process process; private Integer returnCode;
	 * 
	 * public Integer getReturnCode() { return returnCode; }
	 * 
	 * public PipedInputProcess(Process process) { this.process = process;
	 * this.returnCode = null; }
	 * 
	 * @Override public void run() { while( returnCode == null ) { try {
	 * returnCode = new Integer(process.waitFor()); } catch( InterruptedException
	 * e ) { } } }
	 */

	public void cleanup() {
		cleanupStrategy.cleanUp();
	}

}
