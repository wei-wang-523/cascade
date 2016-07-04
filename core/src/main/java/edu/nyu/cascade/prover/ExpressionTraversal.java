package edu.nyu.cascade.prover;

import java.util.LinkedList;

public final class ExpressionTraversal {
	public static interface Visitor<T> {
		void visit(Expression block);

		T getResult();
	}

	public static <T> T traverse(Expression expr, Visitor<T> visitor) {
		LinkedList<Expression> worklist = new LinkedList<Expression>();
		worklist.add(expr);

		while (!worklist.isEmpty()) {
			Expression e = worklist.remove();
			visitor.visit(e);
			worklist.addAll(e.getChildren());
		}

		return visitor.getResult();
	}
}
