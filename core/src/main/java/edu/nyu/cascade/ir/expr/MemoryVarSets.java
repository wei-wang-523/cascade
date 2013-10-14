package edu.nyu.cascade.ir.expr;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.Expression;

public class MemoryVarSets {
	private final Iterable<Expression> stackVars;
	private final Iterable<Expression> stackRegions;
	private final Iterable<Expression> heapRegions;
	
	public static class Builder {
		private ImmutableList.Builder<Expression> stackVarsBuilder;
		private ImmutableList.Builder<Expression> stackRegionsBuilder;
		private ImmutableList.Builder<Expression> heapRegionsBuilder;
		
		public Builder() {
			stackVarsBuilder = new ImmutableList.Builder<Expression>();
			stackRegionsBuilder = new ImmutableList.Builder<Expression>();
			heapRegionsBuilder = new ImmutableList.Builder<Expression>();
		}
		
		public MemoryVarSets build() {
			return new MemoryVarSets(
					stackVarsBuilder.build(), 
					stackRegionsBuilder.build(), 
					heapRegionsBuilder.build());
		}
		
		public Builder addStackVar(Expression stackVar) {
			stackVarsBuilder.add(stackVar);
			return this;
		}

		public Builder addStackRegion(Expression stackRegion) {
			stackRegionsBuilder.add(stackRegion);
			return this;
		}

		public Builder addHeapRegion(Expression heapRegion) {
			heapRegionsBuilder.add(heapRegion);
			return this;
		}
		
		public Builder addStackVars(Iterable<Expression> stackVars) {
			stackVarsBuilder.addAll(stackVars);
			return this;
		}

		public Builder addStackRegions(Iterable<Expression> stackRegions) {
			stackRegionsBuilder.addAll(stackRegions);
			return this;
		}

		public Builder addHeapRegions(Iterable<Expression> heapRegions) {
			heapRegionsBuilder.addAll(heapRegions);
			return this;
		}
	}
	public MemoryVarSets(Iterable<Expression> stackVars, 
			Iterable<Expression> stackRegions,
			Iterable<Expression> heapRegions) {
		this.stackVars = stackVars;
		this.stackRegions = stackRegions;
		this.heapRegions = heapRegions;
	}

	public Iterable<Expression> getStackVars() {
		return stackVars;
	}

	public Iterable<Expression> getStackRegions() {
		return stackRegions;
	}

	public Iterable<Expression> getHeapRegions() {
		return heapRegions;
	}
}
