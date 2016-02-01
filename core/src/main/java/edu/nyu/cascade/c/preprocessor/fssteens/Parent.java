package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

public class Parent {
	
	enum Kind {
		TOP,
		BOTTOM
	}
	
  private final Kind kind;
	private final ECR ecr;
	
	Parent(Kind kind, ECR ecr) {
		this.kind = kind;
		this.ecr = ecr;
	}
	
	private static Parent emptyInstance = null, topInstance = null;
	
	/**
	 * Get the parent with uninitialized ecr for blank type only
	 * @return
	 */
	static Parent getEmpty() {
		if(emptyInstance != null)	return emptyInstance;
		emptyInstance = new Parent(Kind.BOTTOM, null);
		return emptyInstance;
	}
	
	/**
	 * Create the parent as <code>ecr</code>
	 * @param ecr
	 * @return
	 */
	static Parent createParent(ECR ecr) {
		Preconditions.checkNotNull(ecr);
		return new Parent(Kind.BOTTOM, ecr);
	}
	
	/**
	 * Create the parent with no parent, while allowing 
	 * use of least-upper-bound operators in the type
	 * inference algorithm
	 * 
	 * @return
	 */
	static Parent getTop() {
		if(topInstance != null)	return topInstance;
		topInstance = new Parent(Kind.TOP, null);
		return topInstance;
	}
	
	/**
	 * Compute the least-upper-bound operators for two
	 * parents <code>p1</code> and <code>p2</code>
	 * @param p1
	 * @param p2
	 * @return
	 */
	static Parent getLUB(Parent p1, Parent p2) {
		if(p1.equals(p2)) return p1;
		
		Parent top = getTop();
		if(p1.equals(top) || p2.equals(top))	return top;
		
		assert(p1.isEmpty() || p2.isEmpty());
		
		return p1.isEmpty() ? p2 : p1;
	}
	
	@Override
	public boolean equals(Object o) {
		if(!(o instanceof Parent)) return false;
		Parent that = (Parent) o;
		if(!that.kind.equals(kind)) return false;
		if(that.ecr == null && ecr == null) return true;
		if(that.ecr == null && ecr != null) return false;
		if(that.ecr != null && ecr == null) return false;
		return that.ecr.equals(ecr);
	}
	
	@Override
	public String toString() {
		if(isTop()) return "T";
		if(isEmpty()) return Character.toString((char) 216);
		return ecr.toString();
	}
	
	boolean isEmpty() {
		return this.equals(emptyInstance);
	}
	
	boolean isTop() {
		return this.equals(topInstance);
	}

	ECR getECR() {
	  return ecr;
  }
}
