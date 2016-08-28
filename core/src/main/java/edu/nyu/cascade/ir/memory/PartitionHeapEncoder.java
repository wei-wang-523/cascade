package edu.nyu.cascade.ir.memory;

import java.util.Map;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.layout.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.OrderLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.SoundLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.safety.Strategy;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public final class PartitionHeapEncoder implements IRPartitionHeapEncoder {

	private final IRSoundMemLayoutEncoding soundMemEncoding;
	private final IROrderMemLayoutEncoding orderMemEncoding;
	private final ExpressionEncoding encoding;
	private final IRDataFormatter dataFormatter;
	private final Map<String, MemoryVarSets> memVarSetsMap = Maps.newHashMap();

	private PartitionHeapEncoder(ExpressionEncoding encoding,
			IRDataFormatter dataFormatter, IRSoundMemLayoutEncoding soundMemEncoding,
			IROrderMemLayoutEncoding orderMemEncoding) {
		this.soundMemEncoding = soundMemEncoding;
		this.orderMemEncoding = orderMemEncoding;
		this.encoding = encoding;
		this.dataFormatter = dataFormatter;
	}

	public static PartitionHeapEncoder create(ExpressionEncoding encoding,
			IRDataFormatter dataFormatter, Strategy strategy) {

		switch (strategy) {
		case ORDER: {
			IROrderMemLayoutEncoding memLayout = OrderLinearMemLayoutEncoding
					.create(encoding, dataFormatter);
			return new PartitionHeapEncoder(encoding, dataFormatter, null, memLayout);
		}
		case SOUND: {
			IRSoundMemLayoutEncoding memLayout = SoundLinearMemLayoutEncoding
					.create(encoding, dataFormatter);
			return new PartitionHeapEncoder(encoding, dataFormatter, memLayout, null);
		}
		default:
			throw new IllegalArgumentException("Unknown strategy: " + strategy);
		}
	}

	@Override
	public void reset() {
		memVarSetsMap.clear();
	}

	@Override
	public void addFreshAddress(String key, Expression address, IRVarInfo info) {
		MemoryVarSets memVarSets = getMemVarSets(key);
		memVarSets.addStackVar(address, info);
	}

	@Override
	public void addFreshRegion(String key, Expression region) {
		MemoryVarSets memVarSets = getMemVarSets(key);
		memVarSets.addHeapRegion(region);
		memVarSets.setLastRegionCand(region);
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(String key,
			ArrayExpression sizeArr) {
		MemoryVarSets memVarSets = getMemVarSets(key);
		if (soundMemEncoding != null) {
			return soundMemEncoding.disjointMemLayout(memVarSets, sizeArr);
		} else {
			Expression lastRegion = memVarSets.getLastRegion();
			return orderMemEncoding.disjointMemLayout(memVarSets, sizeArr,
					lastRegion);
		}
	}

	@Override
	public BooleanExpression validMalloc(String key, ArrayExpression sizeArr,
			Expression ptr, Expression size) {
		MemoryVarSets memVarSets = getMemVarSets(key);

		size = dataFormatter.castToSize(size);

		if (soundMemEncoding != null) {
			return soundMemEncoding.validMalloc(memVarSets, sizeArr, ptr, size);
		} else {
			Expression lastRegion = memVarSets.getLastRegion();

			BooleanExpression res = orderMemEncoding.validMalloc(sizeArr, lastRegion,
					ptr, size);

			Expression lastRegionCand = memVarSets.getLastRegionCand();
			Expression lastRegionPrime = encoding.getExpressionManager().ifThenElse(
					lastRegionCand.eq(dataFormatter.getNullAddress()), lastRegion,
					lastRegionCand);
			memVarSets.setLastRegion(lastRegionPrime);
			return res;
		}
	}

	@Override
	public BooleanExpression validFree(ArrayExpression markArr, Expression ptr) {
		if (soundMemEncoding != null)
			return soundMemEncoding.validFree(markArr, ptr);
		else
			return orderMemEncoding.validFree(markArr, ptr);
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(String key,
			ArrayExpression sizeArr, Expression ptr) {
		MemoryVarSets varSets = getMemVarSets(key);
		if (soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(varSets, sizeArr, ptr);
		else
			return orderMemEncoding.validMemAccess(varSets, sizeArr, ptr);
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(String key,
			ArrayExpression sizeArr, Expression ptr, Expression size) {
		MemoryVarSets varSets = getMemVarSets(key);

		size = dataFormatter.castToSize(size);

		if (soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(varSets, sizeArr, ptr, size);
		else
			return orderMemEncoding.validMemAccess(varSets, sizeArr, ptr, size);
	}

	private MemoryVarSets getMemVarSets(String key) {
		MemoryVarSets memVarSets;
		if (memVarSetsMap.containsKey(key)) {
			memVarSets = memVarSetsMap.get(key);
		} else {
			memVarSets = new MemoryVarSets(encoding);
			memVarSetsMap.put(key, memVarSets);
		}

		return memVarSets;
	}
}
