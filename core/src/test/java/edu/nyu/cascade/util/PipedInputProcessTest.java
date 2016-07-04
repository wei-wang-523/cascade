package edu.nyu.cascade.util;

import static org.junit.Assert.*;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.concurrent.ExecutionException;

import org.junit.Test;

import edu.nyu.cascade.util.PipedInputProcess;

public class PipedInputProcessTest {
	private static String tee[] = { "tee" };
	private static String echoFoo[] = { "echo", "foo" };

	@Test
	public void testCancel() throws IOException {
		PipedInputProcess p = new PipedInputProcess(echoFoo, new StringReader(
		    "bar"));
		assertTrue(p.cancel(true));
		assertTrue(p.isDone());
		assertTrue(p.isCancelled());
	}

	@Test
	public void testCancelFalse() throws IOException {
		PipedInputProcess p = new PipedInputProcess(echoFoo, new StringReader(
		    "bar"));
		assertTrue(p.cancel(false));
		assertTrue(p.isDone());
		assertTrue(p.isCancelled());
	}

	@Test
	// @Ignore
	public void testCancelFailure() throws IOException, InterruptedException,
	    ExecutionException {
		PipedInputProcess p = new PipedInputProcess(echoFoo, new StringReader(
		    "bar"));
		p.run();
		p.get();
		assertFalse(p.cancel(true));
		assertTrue(p.isDone());
		assertFalse(p.isCancelled());
	}

	// @Test
	public void testPipedInputProcessStringArrayReaderCleanupStrategy() {
		// Reader reader = new StringReader("bar");
		// PipedInputProcess process = new PipedInputProcess(echoFoo, reader, )
	}

	@Test
	public void testPipedInputProcessStringArrayReader() {
		try {
			Reader reader = new StringReader("bar");
			new PipedInputProcess(echoFoo, reader);
		} catch (IOException e) {
			fail("Error in PipedInputProcess: " + e.getMessage());
		}
	}

	@Test
	public void testGetOutputAsReader() throws IOException {
		// try {
		final String input = "bar";
		Reader reader = new StringReader(input);
		PipedInputProcess process = new PipedInputProcess(tee, reader);
		process.run();
		CharSequence chars = process.getOutputAsSequence();
		String output = chars.toString();
		// System.out.println(cbuf.toString());
		// System.out.println(new String(cbuf));
		assertEquals("Unexpected process output", input, output);
		// assertEquals("Expected EOF", processReader.read(), -1);
		// } catch (IOException e) {
		// fail("Error in PipedInputProcess: " + e.getMessage());
		// }
	}

}
