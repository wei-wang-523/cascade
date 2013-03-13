package edu.nyu.cascade.fds;

import com.google.common.base.Function;
import com.google.common.collect.Iterables;

public class StateVariables {
  public static Iterable<StateVariable> prime(Iterable<? extends StateVariable> fs) {
    return Iterables.transform(fs, new Function<StateVariable, StateVariable>() {
      @Override
      public StateVariable apply(StateVariable f) {
        return f.prime();
      }
    });
  }
  
  public static Iterable<StateVariable> unprime(Iterable<? extends StateVariable> fs) {
    return Iterables.transform(fs, new Function<StateVariable, StateVariable>() {
      @Override
      public StateVariable apply(StateVariable f) {
        return f.unprime();
      }
    });
  }
}
