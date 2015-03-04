package edu.nyu.cascade.c.encoder;

import edu.nyu.cascade.ir.state.StateExpression;

public interface StateClosure {
	StateExpression apply(StateExpression stateArg);
  StateExpression getPostState();
  StateExpression getStateVar();
  void setProperty(String name, Object property);
  Object getProperty(String name);
  boolean hasProperty(String name);
}
