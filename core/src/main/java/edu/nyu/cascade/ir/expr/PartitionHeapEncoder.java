package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public final class PartitionHeapEncoder implements IRPartitionHeapEncoder {
	
	private IRHeapEncoding heapEncoding;
	private IRSoundMemLayoutEncoding soundMemEncoding;
	private IROrderMemLayoutEncoding orderMemEncoding;
	
	private PartitionHeapEncoder (IRHeapEncoding heapEncoding,
			IRSoundMemLayoutEncoding soundMemEncoding, 
			IROrderMemLayoutEncoding orderMemEncoding) {
		this.heapEncoding = heapEncoding;
		this.soundMemEncoding = soundMemEncoding;
		this.orderMemEncoding = orderMemEncoding;
	}
	
	public static PartitionHeapEncoder createSoundEncoding(IRHeapEncoding heapEncoding,
			IRSoundMemLayoutEncoding soundMemEncoding) {
		Preconditions.checkArgument(soundMemEncoding != null);
		return new PartitionHeapEncoder(heapEncoding, soundMemEncoding, null);
	}
	
	public static PartitionHeapEncoder createOrderEncoding(IRHeapEncoding heapEncoding,
			IROrderMemLayoutEncoding orderMemEncoding) {
		Preconditions.checkArgument(orderMemEncoding != null);
		return new PartitionHeapEncoder(heapEncoding, null, orderMemEncoding);
	}

	@Override
  public ArrayType getSizeArrType() {
	  return heapEncoding.getSizeArrType();
  }

	@Override
  public Type getAddressType() {
		return heapEncoding.getAddressType();
  }

	@Override
  public Type getValueType() {
		return heapEncoding.getValueType();
  }

	@Override
  public Expression freshAddress(String varName, IRVarInfo info,
      xtc.type.Type type) {
		return heapEncoding.freshAddress(varName, info, type);
  }

	@Override
  public Expression freshRegion(String regionName, Node regionNode) {
		return heapEncoding.freshRegion(regionName, regionNode);
  }

	@Override
  public ArrayExpression updateSizeArr(ArrayExpression sizeArr,
      Expression lval, Expression rval) {
	  return heapEncoding.updateSizeArr(sizeArr, lval, rval);
  }
	
	@Override
  public ArrayExpression updateMemArr(ArrayExpression memArr,
      Expression lval, Expression rval) {
	  return heapEncoding.updateMemArr(memArr, lval, rval);
  }
	
	@Override
	public Expression indexMemArr(ArrayExpression memArr, Expression lval) {
		return heapEncoding.indexMemArr(memArr, lval);
	}

	@Override
  public ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
	  return heapEncoding.getConstSizeArr(sizeArrType);
  }

	@Override
  public Expression getValueZero() {
	  return heapEncoding.getValueZero();
  }

	@Override
  public Expression getUnknownValue(xtc.type.Type type) {
	  return heapEncoding.getUnknownValue(type);
  }

	@Override
  public Expression getNullAddress() {
	  return heapEncoding.getNullAddress();
  }
	
	@Override
	public Expression addressOf(Expression expr) {
		return heapEncoding.addressOf(expr);
	}

	@Override
  public ImmutableSet<BooleanExpression> disjointMemLayout(
  		IREquivClosure equivClass, ArrayExpression sizeArr) {
		MemoryVarSets multiSets = 
				heapEncoding.getCategorizedVars(equivClass.getElements());
		if(soundMemEncoding != null) {
			return soundMemEncoding.disjointMemLayout(multiSets, sizeArr);
		} else {
			String key = equivClass.getName();
			Expression lastRegion = heapEncoding.getLastRegion(key);
			return orderMemEncoding.disjointMemLayout(multiSets, sizeArr, lastRegion);
		}
  }
	
	@Override
  public BooleanExpression validMalloc(IREquivClosure equivClass, 
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		MemoryVarSets multiSets = 
				heapEncoding.getCategorizedVars(equivClass.getElements());
		if(soundMemEncoding != null) {
			Iterable<Expression> heapRegions = multiSets.getHeapRegions();
			return soundMemEncoding.validMalloc(heapRegions, sizeArr, ptr, size);
		} else {
	    String key = equivClass.getName();
			Expression lastRegion = heapEncoding.getLastRegion(key);
			BooleanExpression res = orderMemEncoding.validMalloc(sizeArr, lastRegion, ptr, size);
			// The region just allocated
			Expression newLastRegion = Iterables.getLast(heapEncoding.getMemVarSets().getHeapRegions());
			heapEncoding.updateLastRegion(key, newLastRegion);
			return res;
		}
  }

	@Override
  public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		if(soundMemEncoding != null)
			return soundMemEncoding.validFree(sizeArr, ptr);
		else
			return orderMemEncoding.validFree(sizeArr, ptr);
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
  		IREquivClosure equivClass, ArrayExpression sizeArr, Expression ptr) {
		MemoryVarSets varSets = 
				heapEncoding.getCategorizedVars(equivClass.getElements());
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(varSets, sizeArr, ptr);
		else
			return orderMemEncoding.validMemAccess(varSets, sizeArr, ptr);
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
  		IREquivClosure equivClass, ArrayExpression sizeArr, Expression ptr, Expression size) {
		MemoryVarSets varSets = 
				heapEncoding.getCategorizedVars(equivClass.getElements());
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(varSets, sizeArr, ptr, size);
		else
			return orderMemEncoding.validMemAccess(varSets, sizeArr, ptr, size);
  }
	
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		return heapEncoding.getArrayElemType(type);
	}
	
	protected IRHeapEncoding getHeapEncoding() {
		return heapEncoding;
	}

	protected IRSoundMemLayoutEncoding getSoundMemEncoding() {
		return soundMemEncoding;
	}

	protected IROrderMemLayoutEncoding getOrderMemEncoding() {
		return orderMemEncoding;
	}
}
