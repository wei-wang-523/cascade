package edu.nyu.cascade.c.preprocessor;

import java.util.Set;

import xtc.tree.Node;

import com.google.common.collect.ImmutableMap;

import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;

/**
 * Pre-analysis statement
 * @author Wei
 *
 */
public abstract class PreProcessor<T> {
	
	public static abstract class Builder<T> {
		public Builder() {}
		public abstract Builder<T> setSymbolTable(SymbolTable _symbolTable);
		public abstract PreProcessor<T> build();	
	}
	
  /**
   * Pre analysis statement <code>stmt</code>
   * @param stmt
   */
	public abstract void analysis(IRStatement stmt);

  /**
   * Display the snap shot
   */
	public abstract String displaySnapShot();

	public abstract IREquivClosure getEquivClass(T arg);

	public abstract ImmutableMap<T, Set<IRVar>> getSnapShot();

	public abstract T getPointsToElem(Node node);

	public abstract IRVar getAllocateElem(Node node);

	public abstract String getRepName(T arg);

	public abstract T getRep(Node node);

	public abstract void buildSnapShot();
}
