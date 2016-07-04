package edu.nyu.cascade.util;

import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;

import org.junit.Test;

import edu.nyu.cascade.util.IOUtils;

public class IOUtilsTest {
	@Test
	public void testPipeReader() throws IOException {
		StringWriter writer = new StringWriter();
		IOUtils.pipeReader(new StringReader("foo"), writer);
		assertEquals("foo", writer.toString());
	}

}
