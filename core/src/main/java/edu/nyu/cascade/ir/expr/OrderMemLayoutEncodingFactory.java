package edu.nyu.cascade.ir.expr;

public class OrderMemLayoutEncodingFactory {
	public static IROrderMemLayoutEncoding create(IRHeapEncoding heapEncoding) {
		if(heapEncoding.isLinear()) {
			return OrderLinearMemLayoutEncoding.create(heapEncoding.castToLinear());
		} else if(heapEncoding.isSync()) {
			throw new ExpressionFactoryException(
					"Synchronous heap encoding not supports order memory layout.");
		} else {
			throw new ExpressionFactoryException(
					"Unknown heap encoding ");
		}
	}
}
