package edu.nyu.cascade.c.preprocessor;

import xtc.tree.Printer;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.util.HashCodeUtil;

public class ValueFlowEdge<T> {

	private final T source, target;
	private final IRStatement stmt;
	
	private ValueFlowEdge(T source, T target, IRStatement stmt) {
		this.source = source;
		this.target = target;
		this.stmt = stmt;
	}
	
	static <T> ValueFlowEdge<T> createEdge(T source, T target, IRStatement stmt) {
		return new ValueFlowEdge<T>(source, target, stmt);
	}
	
	public T getSource() {
		return source;
	}
	
	public T getTarget() {
		return target;
	}
	
	public IRStatement getStatement() {
		return stmt;
	}
	
  public void format(Printer printer) {
    printer.pln(toString());
  }
  
  public String toString() {
    return source + " --[" + stmt + "]" +
        "--> " + target;
  }
  
  @Override
  public boolean equals(Object o) {
  	if(!(o instanceof ValueFlowEdge)) return false;
  	
  	@SuppressWarnings("unchecked")
		ValueFlowEdge<T> edge = (ValueFlowEdge<T>) o;
  	if(!edge.source.equals(source)) return false;
  	if(!edge.target.equals(target)) return false;
  	if(!edge.stmt.equals(stmt)) return false;
  	return true;
  }
  
	@Override
	public int hashCode() {
		return HashCodeUtil.hash(
				HashCodeUtil.hash(
						HashCodeUtil.hash(HashCodeUtil.SEED, source), target), stmt);
	}
}
