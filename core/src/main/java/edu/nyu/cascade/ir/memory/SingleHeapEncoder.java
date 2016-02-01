package edu.nyu.cascade.ir.memory;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.layout.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.OrderLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.layout.SoundLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.Strategy;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public class SingleHeapEncoder implements IRSingleHeapEncoder{

	private final IRSoundMemLayoutEncoding soundMemEncoding;
	private final IROrderMemLayoutEncoding orderMemEncoding;
	private final ExpressionEncoding encoding;
	private final IRDataFormatter dataFormatter;
	private MemoryVarSets memVarSets;
	
	private SingleHeapEncoder(ExpressionEncoding encoding, 
			IRDataFormatter dataFormatter,
			IRSoundMemLayoutEncoding soundMemEncoding, 
			IROrderMemLayoutEncoding orderMemEncoding) {
		this.soundMemEncoding = soundMemEncoding;
		this.orderMemEncoding = orderMemEncoding;
		this.encoding = encoding;
		this.dataFormatter = dataFormatter;
		this.memVarSets = new MemoryVarSets(encoding);
	}
	
	public static SingleHeapEncoder create(ExpressionEncoding encoding, 
			IRDataFormatter dataFormatter,
			Strategy strategy) {
		switch(strategy) {
		case ORDER: {
			IROrderMemLayoutEncoding memLayout = OrderLinearMemLayoutEncoding
    			.create(encoding, dataFormatter);
			return new SingleHeapEncoder(encoding, dataFormatter, null, memLayout);
		}
		case SOUND: {
			IRSoundMemLayoutEncoding memLayout = SoundLinearMemLayoutEncoding
					.create(encoding, dataFormatter);
			return new SingleHeapEncoder(encoding, dataFormatter, memLayout, null);
		}
		default: 
			throw new IllegalArgumentException("Unknown strategy: " + strategy);
		}
	}
	
	@Override
	public void reset() {
		memVarSets = new MemoryVarSets(encoding);
	}

	@Override
  public ImmutableSet<BooleanExpression> disjointMemLayout(
      ArrayExpression sizeArr) {		
		if(soundMemEncoding != null) {
			return soundMemEncoding.disjointMemLayout(memVarSets, sizeArr);
		} else {
			Expression lastRegion = memVarSets.getLastRegion();
			return orderMemEncoding.disjointMemLayout(memVarSets, sizeArr, lastRegion);
		}
  }

	@Override
  public BooleanExpression validMalloc(ArrayExpression sizeArr, Expression ptr,
      Expression size) {
		
		size = dataFormatter.castToSize(size);
		
		if(soundMemEncoding != null) {
			return soundMemEncoding.validMalloc(memVarSets, sizeArr, ptr, size);
		} else {
			Expression lastRegion = memVarSets.getLastRegion();
			BooleanExpression res = orderMemEncoding.validMalloc(sizeArr, lastRegion, ptr, size);
			
			Expression lastRegionCand = memVarSets.getLastRegionCand();
			Expression lastRegionPrime = encoding.getExpressionManager().ifThenElse(
					lastRegionCand.eq(dataFormatter.getNullAddress()), 
					lastRegion, 
					lastRegionCand);
			memVarSets.setLastRegion(lastRegionPrime);
			
			return res;
		}
  }

	@Override
  public BooleanExpression validFree(ArrayExpression markArr, Expression ptr) {
		if(soundMemEncoding != null) {
			return soundMemEncoding.validFree(markArr, ptr);
		} else {
			return orderMemEncoding.validFree(markArr, ptr);
		}
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
      ArrayExpression sizeArr, Expression ptr) {		
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(memVarSets, sizeArr, ptr);
		else
			return orderMemEncoding.validMemAccess(memVarSets, sizeArr, ptr);
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		size = dataFormatter.castToSize(size);
		
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(memVarSets, sizeArr, ptr, size);
		else
			return orderMemEncoding.validMemAccess(memVarSets, sizeArr, ptr, size);
  }
	
	@Override
  public void addFreshAddress(Expression lval, IRVarInfo info) {
		memVarSets.addStackVar(lval, info);
  }

	@Override
  public void addFreshRegion(Expression region) {
		memVarSets.addHeapRegion(region);
		memVarSets.setLastRegionCand(region);
  }
}
