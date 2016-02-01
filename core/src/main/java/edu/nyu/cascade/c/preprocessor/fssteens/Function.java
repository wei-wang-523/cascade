package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Collection;

public class Function {
	enum Kind {
		LAMBDA,
		BOTTOM
	}
	
	private final Kind kind;
	
	private Collection<ECR> args;
	private Collection<ECR> rets;
	
	Function(Kind kind) {
		this.kind = kind;
	}
	
	private static Function bottomInstance = null;
	
	static Function createLambda(Collection<ECR> args, Collection<ECR> rets) {
		Function func = new Function(Kind.LAMBDA);
		func.args = args;
		func.rets = rets;
		return func;
	}
	
	static Function getBottom() {
		if(bottomInstance != null)	return bottomInstance;
		bottomInstance = new Function(Kind.BOTTOM);
		return bottomInstance;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if(isBottom()) return sb.append("Bot ").toString();
		
		sb.append("Lam ( ");
		for(ECR ret : rets) {
			sb.append(ret).append(' ');
		}
		sb.append(')');
		
		sb.append('(');
		for(ECR arg : args) {
			sb.append(arg).append(' ');
		}
		sb.append(')');
		return sb.toString();
	}
	
	boolean isLambda() {
		return kind.equals(Kind.LAMBDA);
	}
	
	boolean isBottom() {
		return kind.equals(Kind.BOTTOM);
	}
	
	Collection<ECR> getArgs() {
		return args;
	}
	
	Collection<ECR> getRets() {
		return rets;
	}
}
