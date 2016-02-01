package edu.nyu.cascade.c;

import java.util.Collection;

import edu.nyu.cascade.ir.state.StateExpression;

public interface PathStateClosure {
  PathStateClosure apply(PathStateClosure stateClosure);
  StateExpression getPathState();
  Collection<StateExpression> getStateVars();
  void setProperty(String label, Object o);
  Object getProperty(String label);
	boolean hasProperty(String srcpath);
}
