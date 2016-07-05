package edu.nyu.cascade.util;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;

public final class CommandTokenizer {
	private static final Pattern WORD = Pattern.compile(
			"(?:[^\\s'\"\\\\]|\\\\[\\s'\"\\\\])+");
	private static final Pattern SINGLE_QUOTED_STRING = Pattern.compile(
			"'[^']*'");
	private static final Pattern DOUBLE_QUOTED_STRING = Pattern.compile(
			"\"(?:[^\"]|\\\")*\"");

	/**
	 * Regex to match a command line token: a "word" or a quoted string. Matches
	 * whitespace at the beginning if the token is the first in an input and
	 * arbitrary whitespace after the token.
	 */
	private static final Pattern TOKEN = Pattern.compile("(?:^\\s*)?" + "("
			+ Joiner.on("|").join(WORD, SINGLE_QUOTED_STRING, DOUBLE_QUOTED_STRING)
			+ ")" + "(?:\\s+|\\s*$)");
	/** The matching group of the actual token in the TOKEN regex */
	private static final int TOKEN_GROUP = 1;

	public static boolean isWord(CharSequence input) {
		return WORD.matcher(input).matches();
	}

	public static boolean isSingleQuotedString(CharSequence input) {
		return SINGLE_QUOTED_STRING.matcher(input).matches();
	}

	public static boolean isDoubleQuotedString(CharSequence input) {
		return DOUBLE_QUOTED_STRING.matcher(input).matches();
	}

	/** Split a character sequence into a List of command line tokens. */
	public static ArgList tokenize(CharSequence input) {
		Matcher matcher = TOKEN.matcher(input);
		ArgList tokens = new ArgList();

		/* Match at the beginning of the region */
		while (matcher.lookingAt()) {
			String match = matcher.group(TOKEN_GROUP);
			tokens.append(match);

			/* Change the matcher region to start at the end of the last match */
			matcher.region(matcher.end(), input.length());
		}

		/* Tokenization has to match the whole input */
		if (matcher.regionStart() != input.length()) {
			throw new IllegalArgumentException(input.toString());
		}

		return tokens;
	}

	public static class ArgList {
		private final List<String> argList;

		private ArgList() {
			argList = Lists.newArrayList();
		}

		ArgList(String... tokens) {
			argList = Lists.newArrayList(tokens);
		}

		public void append(String token) {
			argList.add(token);
		}

		public void append(String... tokens) {
			argList.addAll(Lists.newArrayList(tokens));
		}

		public String[] toArray() {
			return argList.toArray(new String[0]);
		}

		public boolean equals(Object obj) {
			if (!(obj instanceof ArgList)) {
				return false;
			} else {
				return argList.equals(((ArgList) obj).argList);
			}
		}

		public String toString() {
			return argList.toString();
		}
	}

}
