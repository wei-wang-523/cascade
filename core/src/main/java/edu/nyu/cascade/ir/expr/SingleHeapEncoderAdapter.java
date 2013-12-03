package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public class SingleHeapEncoderAdapter implements IRSingleHeapEncoder{

	private IRHeapEncoding heapEncoding;
	private IRSoundMemLayoutEncoding soundMemEncoding;
	private IROrderMemLayoutEncoding orderMemEncoding;
	
	private SingleHeapEncoderAdapter(PartitionHeapEncoder heapEncoder) {
		heapEncoding = heapEncoder.getHeapEncoding();
		soundMemEncoding = heapEncoder.getSoundMemEncoding();
		orderMemEncoding = heapEncoder.getOrderMemEncoding();
	}
	
	public static SingleHeapEncoderAdapter create(PartitionHeapEncoder heapEncoder) {
		return new SingleHeapEncoderAdapter(heapEncoder);
	}
	
	@Override
	public ArrayType getMemoryType() {
		return heapEncoding.getMemoryType();
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
	  return heapEncoding.freshAddress(Identifiers.uniquify(varName), info, type);
  }

	@Override
  public Expression freshRegion(String regionName, Node regionNode) {
	  return heapEncoding.freshRegion(regionName, regionNode);
  }

	@Override
  public ArrayExpression updateMemArr(ArrayExpression memArr,
      Expression lval, Expression rval) {
	  return heapEncoding.updateMemArr(memArr, lval, rval);
  }
	
	@Override
  public ArrayExpression updateSizeArr(ArrayExpression sizeArr,
      Expression lval, Expression rval) {
	  return heapEncoding.updateSizeArr(sizeArr, lval, rval);
  }

	@Override
  public Expression getConstSizeArr(ArrayType sizeArrType) {
	  return heapEncoding.getConstSizeArr(sizeArrType);
  }

	@Override
  public Expression getSizeZero() {
	  return heapEncoding.getSizeZero();
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
  public ImmutableSet<BooleanExpression> disjointMemLayout(
      ArrayExpression sizeArr) {
		MemoryVarSets multiSets = heapEncoding.getMemVarSets();
		
		if(soundMemEncoding != null) {
			return soundMemEncoding.disjointMemLayout(multiSets, sizeArr);
		} else {
			Expression lastRegion = heapEncoding.getLastRegion();
			return orderMemEncoding.disjointMemLayout(multiSets, sizeArr, lastRegion);
		}
  }

	@Override
  public BooleanExpression validMalloc(ArrayExpression sizeArr, Expression ptr,
      Expression size) {		
		if(soundMemEncoding != null) {
			Iterable<Expression> heapRegions = heapEncoding.getMemVarSets().getHeapRegions();
			return soundMemEncoding.validMalloc(heapRegions, sizeArr, ptr, size);
		} else {
			Expression lastRegion = heapEncoding.getLastRegion();
			BooleanExpression res = orderMemEncoding.validMalloc(sizeArr, lastRegion, ptr, size);
			// The region just allocated
			Expression newLastRegion = Iterables.getLast(heapEncoding.getMemVarSets().getHeapRegions());
			heapEncoding.updateLastRegion(newLastRegion);
			return res;
		}
  }

	@Override
  public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		if(soundMemEncoding != null) {
			return soundMemEncoding.validFree(sizeArr, ptr);
		} else {
			return orderMemEncoding.validFree(sizeArr, ptr);
		}
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
      ArrayExpression sizeArr, Expression ptr) {
		MemoryVarSets multiSets = heapEncoding.getMemVarSets();
		
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(multiSets, sizeArr, ptr);
		else
			return orderMemEncoding.validMemAccess(multiSets, sizeArr, ptr);
  }

	@Override
  public ImmutableSet<BooleanExpression> validMemAccess(
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		MemoryVarSets multiSets = heapEncoding.getMemVarSets();
		
		if(soundMemEncoding != null)
			return soundMemEncoding.validMemAccess(multiSets, sizeArr, ptr, size);
		else
			return orderMemEncoding.validMemAccess(multiSets, sizeArr, ptr, size);
  }

	@Override
  public Expression indexMemArr(ArrayExpression memArr, Expression p) {
	  return heapEncoding.indexMemArr(memArr, p);
  }
	
	@Override
	public Expression addressOf(Expression expr) {
		return heapEncoding.addressOf(expr);
	}
}
