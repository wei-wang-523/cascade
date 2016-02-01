package edu.nyu.cascade.c.encoder;

import java.util.Collection;
import java.util.Map;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;

public class PathStateFactory {
	private final PathEncoding pathEncoding;
	
	private PathStateFactory(PathEncoding pathEncoding) {
		this.pathEncoding = pathEncoding;
	}
	
	public static PathStateFactory getInstance(PathEncoding pathEncoding) {
		return new PathStateFactory(pathEncoding);
	}
	
	public StateClosure getStateClosure(final StateExpression postState) {
  	return new StateClosure() {
  		StateExpression stateVar = pathEncoding.getStateFactory().getStateVar(postState);
  		Map<String, Object> properties = Maps.newHashMap();
  		
  		@Override
  		public String toString() {
  			return new StringBuilder()
  			.append("state var: ")
  			.append(stateVar)
  			.append("\n--------------\n")
  			.append("state: ")
  			.append(postState)
  			.toString();
  		}

			@Override
      public StateExpression getStateVar() {
	      return stateVar;
      }

			@Override
      public StateExpression getPostState() {
	      return postState;
      }

			@Override
      public StateExpression apply(StateExpression stateArg) {		
				StateFactory<?> stateFactory = pathEncoding.getStateFactory();
				StateExpression cleanState = stateFactory.copy(postState);
				stateFactory.propagateState(cleanState, stateVar, stateArg);
				return cleanState;
      }

			@Override
      public void setProperty(String name, Object property) {
	      properties.put(name, property);
      }

			@Override
      public Object getProperty(String name) {
	      return properties.get(name);
      }

			@Override
      public boolean hasProperty(String name) {
	      return properties.containsKey(name);
      }
  	};
  }
  
  StateClosure mergeStateClosure(Collection<StateClosure> preStateClosures) {
  	Preconditions.checkArgument(!preStateClosures.isEmpty());
  	int size = preStateClosures.size();
  	
  	StateClosure fstPreStateClosure = preStateClosures.iterator().next();
  	if(size == 1) return fstPreStateClosure;
  	
		/* Collect the post-state of preStateClosures */
    Collection<StateExpression> postStates = Lists.newArrayListWithCapacity(size);
    
    for(StateClosure preStateClosure : preStateClosures) {
    	StateExpression postState = preStateClosure.getPostState();
      postStates.add(postState);
    }
    
    StateExpression mergeState = pathEncoding.noop(postStates);
    return getStateClosure(mergeState);
  }
}
