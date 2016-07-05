package edu.nyu.cascade.util;

import junit.framework.TestCase;

import org.junit.Test;

import edu.nyu.cascade.util.CommandTokenizer;
import edu.nyu.cascade.util.CommandTokenizer.ArgList;

public class CommandTokenizerTest extends TestCase {
	public void doTestIsWord(String input, boolean expected) {
		assertEquals("isWord('" + input + "')", expected, CommandTokenizer.isWord(
				input));
	}

	@Test
	public void testIsWord() {
		doTestIsWord("foo", true);
		doTestIsWord("foo\\'bar\\'", true);
		doTestIsWord("foo\\\"bar\\\"", true);
		doTestIsWord("foo bar", false);
		doTestIsWord("foo\\ bar", true);
		doTestIsWord("foo\\\tbar", true);
		doTestIsWord("foo\\\\bar", true);
		doTestIsWord("foo\\ ", true);
		doTestIsWord("foo\\  ", false);
	}

	public void doTestTokenize(String args, String... expectedTokens) {
		ArgList expected = new ArgList(expectedTokens);
		ArgList actual = CommandTokenizer.tokenize(args);
		assertEquals(expected, actual);
	}

	public void tokenizeShouldFail(String args) {
		try {
			ArgList tokens = CommandTokenizer.tokenize(args);
			fail("Expected failure: '" + args + "' tokens: " + tokens.toString());
		} catch (IllegalArgumentException e) {
		}
	}

	@Test
	public void testTokenize() {
		doTestTokenize("foo", "foo");
		doTestTokenize("foo bar", "foo", "bar");
		doTestTokenize("  foo bar", "foo", "bar");
		doTestTokenize("  foo bar  ", "foo", "bar");
		doTestTokenize("\tfoo\tbar", "foo", "bar");
		// doTestTokenize( "foo'bar'", "foo'bar'");
		// doTestTokenize( "foo'bar baz'", "foo'bar baz'");
		doTestTokenize("foo 'b a r' \"b a z\"", "foo", "'b a r'", "\"b a z\"");
		doTestTokenize("foo 'b\"a\"r'", "foo", "'b\"a\"r'");
		doTestTokenize("foo\\ bar", "foo\\ bar");
		doTestTokenize("foo\\\tbar", "foo\\\tbar");

		doTestTokenize("gcc -E -", "gcc", "-E", "-");

		tokenizeShouldFail("'foo");
		tokenizeShouldFail("foo'");
		tokenizeShouldFail("foo'bar");
		tokenizeShouldFail("\"foo");
		tokenizeShouldFail("foo\"");
		tokenizeShouldFail("foo\"bar");
	}
}
