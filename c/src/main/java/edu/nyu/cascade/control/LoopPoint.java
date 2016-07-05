package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

public class LoopPoint {

	static edu.nyu.cascade.control.LoopPoint valueOf(
			edu.nyu.cascade.control.jaxb.LoopPoint loopPos,
			edu.nyu.cascade.control.jaxb.Position position,
			Map<BigInteger, File> sourceFiles) throws ControlFileException {
		if (loopPos == null)
			return null;
		BigInteger iterTimes = loopPos.getIterTimes();
		String invariant = loopPos.getInvariant();
		List<Position> wayPoint = Lists.newArrayList();
		for (edu.nyu.cascade.control.jaxb.Position pos : loopPos.getWayPoint())
			wayPoint.add(Position.valueOf(pos, sourceFiles));

		File file = sourceFiles.get(position.getFileId());
		BigInteger line = position.getLine();
		return new LoopPoint(file, line, iterTimes, invariant, wayPoint);
	}

	private File file;
	private BigInteger line;
	private int iterTimes;
	private String invariant;
	private final List<Position> wayPoint;
	private String asString;

	private LoopPoint(File file, BigInteger line, BigInteger iterTimes,
			String invariant, List<Position> wayPoint) {
		// Cannot be: iterTimes > 0 and invariant is not null
		Preconditions.checkArgument(!(iterTimes.intValue() > 0
				&& invariant != null));
		this.file = file;
		this.line = line;
		this.iterTimes = iterTimes.intValue();
		this.wayPoint = wayPoint;
		this.invariant = invariant;

		/* Build stringrep */
		StringBuilder builder = new StringBuilder();
		builder.append("loop:" + iterTimes).append(',');
		builder.append("invariant:" + invariant);
		this.asString = builder.toString();
	}

	public String toString() {
		return asString;
	}

	public File getFile() {
		return file;
	}

	public BigInteger getLine() {
		return line;
	}

	public int getIterTimes() {
		return iterTimes;
	}

	public String getInvariant() {
		return invariant;
	}

	public boolean hasInvariant() {
		return invariant != null;
	}

	public List<Position> getWayPoint() {
		return Collections.unmodifiableList(wayPoint);
	}
}
