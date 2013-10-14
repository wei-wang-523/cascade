package edu.nyu.cascade.ir.expr;

public class SoundMemLayoutEncodingFactory {
	
	public static IRSoundMemLayoutEncoding create(IRHeapEncoding heapEncoding) {
		if(heapEncoding.isLinear()) {
			return SoundLinearMemLayoutEncoding.create(heapEncoding.castToLinear());
		} else if(heapEncoding.isSync()) {
			return SoundSyncMemLayoutEncoding.create(heapEncoding.castToSync());
		} else {
			throw new ExpressionFactoryException("Unknown heap encoding ");
		}
	}
}