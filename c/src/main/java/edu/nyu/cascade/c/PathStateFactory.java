package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Comparator;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.util.Identifiers;

public class PathStateFactory {
	private final PathEncoding pathEncoding;
	
	private PathStateFactory(PathEncoding pathEncoding) {
		this.pathEncoding = pathEncoding;
	}
	
	public static PathStateFactory getInstance(PathEncoding pathEncoding) {
		return new PathStateFactory(pathEncoding);
	}
	
	PathStateClosure suspend(final StateExpression pathState, 
  		final Collection<StateExpression> stateVars) {
  	return new PathStateClosure() {
  		private Map<String, Object> properties = Maps.newHashMap();
  		
  		@Override
  		public String toString() {
  			return pathState.toString();
  		}

			@Override
      public Collection<StateExpression> getStateVars() {
	      return stateVars;
      }

			@Override
      public StateExpression getPathState() {
	      return pathState;
      }

			@Override
      public PathStateClosure apply(PathStateClosure stateClosure) {
				Preconditions.checkArgument(stateVars.size() == 1);
				
				StateExpression stateVar = Iterables.getFirst(stateVars, null);
				StateExpression stateArg = stateClosure.getPathState();
				
				StateFactory<?> stateFactory = pathEncoding.getStateFactory();
				StateExpression stateCopy = pathState.copy();
				StateExpression statePrime = stateFactory.propagateState(stateCopy, stateVar, stateArg);
	      return suspend(statePrime, stateClosure.getStateVars());
      }

			@Override
      public void setProperty(String label, Object o) {
				properties.put(label, o);
      }

			@Override
      public Object getProperty(String label) {
				return properties.get(label);
      }

			@Override
      public boolean hasProperty(String label) {
	      return properties.containsKey(label);
      }
  	};
  }
  
  PathStateClosure mergePreStateClosure(Collection<PathStateClosure> preStateClosures) {
  	Preconditions.checkArgument(!preStateClosures.isEmpty());
  	int size = preStateClosures.size();
  	
  	if(size == 1) { // single pre-state
			return preStateClosures.iterator().next();
		} 
  	
    /* Add state variables based on the order of the source path */
    Set<StateExpression> stateVars = Sets.newTreeSet(new Comparator<StateExpression>(){
			@Override
      public int compare(StateExpression arg0, StateExpression arg1) {
	      Preconditions.checkArgument(arg0.hasProperty(Identifiers.SRCPATH));
	      Preconditions.checkArgument(arg1.hasProperty(Identifiers.SRCPATH));
	      
	      Path path0 = (Path) arg0.getProperty(Identifiers.SRCPATH);
	      Path path1 = (Path) arg1.getProperty(Identifiers.SRCPATH);
	      
	      return path0.compareTo(path1);
      }
    });
    
		/* Collect the preconditions of pre-paths */
    Collection<StateExpression> preStates = Lists.newArrayListWithCapacity(size);
    
    for(PathStateClosure preStateClosure : preStateClosures) {
    	StateExpression preState = preStateClosure.getPathState();     
      assert(preState.hasGuard());
      preStates.add(preState);
      
      for(StateExpression stateVar : preStateClosure.getStateVars()) {      	
      	stateVars.add(stateVar);
      }
    }
    
    StateExpression mergeState = pathEncoding.noop(preStates);
    return suspend(mergeState, stateVars);
  }
}
