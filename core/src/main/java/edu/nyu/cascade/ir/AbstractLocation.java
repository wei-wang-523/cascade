package edu.nyu.cascade.ir;

import com.google.common.base.Preconditions;

public abstract class AbstractLocation implements IRLocation {
	@Override
	public int compareTo(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return IRLocations.compare(this, loc);
	}

	@Override
	public boolean equals(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return compareTo(loc) == 0;
	}

	/*
	 * TODO: Could give the wrong answer when the location is within the last
	 * statement of the block...
	 */
	@Override
	public boolean follows(IRBasicBlock block) {
		Preconditions.checkNotNull(block);
		return block.getEndLocation() == null ? true
				: follows(block.getEndLocation());
	}

	@Override
	public boolean follows(IRBasicBlock block, boolean strict) {
		Preconditions.checkNotNull(block);
		return strict ? strictFollows(block) : follows(block);
	}

	@Override
	public boolean follows(IRExpression expr) {
		Preconditions.checkNotNull(expr);
		return follows(expr.getLocation());
	}

	@Override
	public boolean follows(IRExpression expr, boolean strict) {
		Preconditions.checkNotNull(expr);
		return strict ? strictFollows(expr) : follows(expr);
	}

	@Override
	public boolean follows(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return this.compareTo(loc) >= 0;
	}

	@Override
	public boolean follows(IRLocation loc, boolean strict) {
		Preconditions.checkNotNull(loc);
		return strict ? strictFollows(loc) : follows(loc);
	}

	@Override
	public boolean follows(IRStatement stmt) {
		Preconditions.checkNotNull(stmt);
		return follows(stmt.getLocation());
	}

	@Override
	public boolean follows(IRStatement stmt, boolean strict) {
		Preconditions.checkNotNull(stmt);
		return strict ? strictFollows(stmt) : follows(stmt);
	}

	@Override
	public boolean isWithin(IRBasicBlock block) {
		Preconditions.checkNotNull(block);
		if (!block.hasLocation())
			return false;

		return !strictFollows(block) && !strictPrecedes(block);
	}

	@Override
	public boolean precedes(IRBasicBlock block) {
		Preconditions.checkNotNull(block);
		return block.getEndLocation() == null ? true
				: precedes(block.getStartLocation());
	}

	@Override
	public boolean precedes(IRBasicBlock block, boolean strict) {
		Preconditions.checkNotNull(block);
		return strict ? strictPrecedes(block) : precedes(block);
	}

	@Override
	public boolean precedes(IRExpression expr) {
		Preconditions.checkNotNull(expr);
		return precedes(expr.getLocation());
	}

	@Override
	public boolean precedes(IRExpression expr, boolean strict) {
		Preconditions.checkNotNull(expr);
		return strict ? strictPrecedes(expr) : precedes(expr);
	}

	@Override
	public boolean precedes(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return this.compareTo(loc) <= 0;
	}

	@Override
	public boolean precedes(IRLocation loc, boolean strict) {
		Preconditions.checkNotNull(loc);
		return strict ? strictPrecedes(loc) : precedes(loc);
	}

	@Override
	public boolean precedes(IRStatement stmt) {
		Preconditions.checkNotNull(stmt);
		return precedes(stmt.getLocation());
	}

	@Override
	public boolean precedes(IRStatement stmt, boolean strict) {
		Preconditions.checkNotNull(stmt);
		return strict ? strictPrecedes(stmt) : precedes(stmt);
	}

	@Override
	public boolean strictFollows(IRBasicBlock block) {
		Preconditions.checkNotNull(block);
		return block.getEndLocation() == null ? true
				: strictFollows(block.getEndLocation());
	}

	@Override
	public boolean strictFollows(IRExpression expr) {
		Preconditions.checkNotNull(expr);
		return strictFollows(expr.getLocation());
	}

	@Override
	public boolean strictFollows(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return this.compareTo(loc) > 0;
	}

	@Override
	public boolean strictFollows(IRStatement stmt) {
		Preconditions.checkNotNull(stmt);
		return strictFollows(stmt.getLocation());
	}

	@Override
	public boolean strictPrecedes(IRBasicBlock block) {
		Preconditions.checkNotNull(block);
		return block.getEndLocation() == null ? true
				: strictPrecedes(block.getStartLocation());
	}

	@Override
	public boolean strictPrecedes(IRExpression expr) {
		Preconditions.checkNotNull(expr);
		return strictPrecedes(expr.getLocation());
	}

	@Override
	public boolean strictPrecedes(IRLocation loc) {
		Preconditions.checkNotNull(loc);
		return this.compareTo(loc) < 0;
	}

	@Override
	public boolean strictPrecedes(IRStatement stmt) {
		Preconditions.checkNotNull(stmt);
		return strictPrecedes(stmt.getLocation());
	}

	@Override
	public String toString() {
		return IRLocations.stringOf(this);
	}
}
