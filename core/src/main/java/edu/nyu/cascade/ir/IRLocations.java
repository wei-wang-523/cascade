package edu.nyu.cascade.ir;

import java.io.File;

import xtc.tree.Location;
import xtc.tree.Node;

public class IRLocations {
	public static int compare(IRLocation a, IRLocation b) {
		File aFile = a.getFile();
		File bFile = b.getFile();

		int c = aFile != null && bFile != null ? aFile.compareTo(bFile)
				: (aFile == bFile ? 0 : (aFile == null ? -1 : 1));
		if (c == 0)
			c = a.getLine() - b.getLine();
		/*
		 * if (c == 0) c = a.getColumn() - b.getColumn();
		 */ return c;
	}

	public static IRLocation ofLocation(final Location loc) {
		return new AbstractLocation() {
			@Override
			public int getLine() {
				return loc.line;
			}

			@Override
			public File getFile() {
				return loc.file == null ? null : new File(loc.file);
			}

			/*
			 * @Override public int getColumn() { return loc.column; }
			 */
		};
	}

	public static IRLocation ofNode(Node node) {
		return ofLocation(node.getLocation());
	}

	public static IRLocation ofExpression(IRExpression expr) {
		return ofNode(expr.getSourceNode());
	}

	public static IRLocation ofStatement(IRStatement stmt) {
		return ofNode(stmt.getSourceNode());
	}

	public static void buildStringOf(IRLocation loc, StringBuilder builder) {
		if (loc.getFile() == null) {
			builder.append("<none>");
		} else {
			builder.append(loc.getFile().getName()).append(":").append(loc.getLine());
		}
	}

	public static String stringOf(IRLocation loc) {
		StringBuilder builder = new StringBuilder();
		buildStringOf(loc, builder);
		return builder.toString();
	}
}
