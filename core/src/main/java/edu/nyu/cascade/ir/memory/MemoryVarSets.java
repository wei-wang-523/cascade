package edu.nyu.cascade.ir.memory;

import java.util.Collection;
import java.util.Map;

import xtc.type.Type;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.inject.Inject;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.Expression;

public class MemoryVarSets {
	private final Map<Expression, Type> stackVarsMap = Maps.newHashMap();
	private final Collection<Expression> heapRegions = Lists.newArrayList();
	private Expression lastRegion, lastRegionCand;
	
	@Inject
	public MemoryVarSets(ExpressionEncoding encoding) {
		lastRegion = encoding.getPointerEncoding().getNullPtr();
		lastRegionCand = encoding.getPointerEncoding().getNullPtr();
	}
	
	public void addHeapRegion(Expression region) {
		heapRegions.add(region);
	}
	
	public void addStackVar(final Expression expr, IRVarInfo info) {
		stackVarsMap.put(expr, info.getXtcType());
	}
	
	public Map<Expression, Type> getStackVarsMap() {
		return ImmutableMap.copyOf(stackVarsMap);
	}
	
	public Collection<Expression> getHeapRegions() {
		return heapRegions;
	}
	
	public Expression getLastRegion() {
		return lastRegion;
	}
	
	public Expression getLastRegionCand() {
		return lastRegionCand;
	}
	
	public void setLastRegion(Expression lastRegion) {
		this.lastRegion = lastRegion;
	}
	
	public void setLastRegionCand(Expression lastRegionCand) {
		this.lastRegionCand = lastRegionCand;
	}
}
