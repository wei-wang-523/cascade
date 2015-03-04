package edu.nyu.cascade.ir.state;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.type.ArrayType;

public final class SingleStateExpression extends AbstractStateExpression {
  
  private final String name;
  private ArrayExpression mem, size, mark;
  
  private SingleStateExpression(String _name, 
  		ArrayExpression _mem, ArrayExpression _size, ArrayExpression _mark) {
  	name = _name;
  	mem = _mem;
  	size = _size;
  	mark = _mark;
  }
  
  private SingleStateExpression(String _name) {
  	name = _name;
  }
  
  static SingleStateExpression create(String name, ArrayExpression mem, ArrayExpression size, ArrayExpression mark) {
  	return new SingleStateExpression(name, mem, size, mark);
  }
  
	@Override
	public boolean isSingle() {
		return true;
	}
	
	@Override
	public boolean isMultiple() {
		return false;
	}

	@Override
	public boolean isLambda() {
		return false;
	}
	
	@Override
	public String toStringShort() {
		StringBuilder sb = new StringBuilder();
		sb.append(mem).append("\n").append(size).append("\n").append(mark).append("\n");
		return sb.toString();
	}
	
	ArrayType[] getElemTypes() {
		return new ArrayType[]{mem.getType(), size.getType(), mark.getType()};
	}

	String getName() {
		return name;
	}

	ArrayExpression getMemory() {
		return mem;
	}
	
  void setMemory(ArrayExpression mem) {
  	this.mem = mem;
	}
	
	ArrayExpression getSize() {
		return size;
	}
	
  void setSize(ArrayExpression size) {
  	this.size = size;
	}
  
  ArrayExpression getMark() {
  	return mark;
  }
  
  void setMark(ArrayExpression mark) {
  	this.mark = mark;
  }
  
	int getElemSize() {
		return 3;
	}
}
