package edu.nyu.cascade.fds;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.Expression;

public class StateProperties {
  public static Iterable<StateProperty> prime(Iterable<? extends StateProperty> fs) {
    return Iterables.transform(fs, new Function<StateProperty, StateProperty>() {
      @Override
      public StateProperty apply(StateProperty f) {
        return f.prime();
      }
    });
  }
  
  public static StateProperty[] prime(StateProperty... fs) {
    return Iterables.toArray(prime(Arrays.asList(fs)),StateProperty.class);
  }
  
  public static StateProperty or(Iterable<? extends StateProperty> disjs) {
    Preconditions.checkArgument(!Iterables.isEmpty(disjs));
    List<StateProperty> disjList = Lists.newLinkedList(disjs);
    StateProperty p = disjList.remove(0);
    return p.or(disjList);
  }

  public static StateProperty and(Iterable<? extends StateProperty> conjs) {
    Preconditions.checkArgument(!Iterables.isEmpty(conjs));
    List<StateProperty> conjList = Lists.newLinkedList(conjs);
    StateProperty p = conjList.remove(0);
    return p.and(conjList);
  }

  public static StateProperty.Factory createFactory(
      final StateExpression.Factory exprFactory) {
    return new StateProperty.Factory() {
      @Override
      public StateProperty valueOf(Expression expr) {
        return exprFactory.valueOf(expr).asStateProperty();
      }
    };
  }
/*  public static IStateProperty preserved(Iterable<? extends IStateVariable> xs) {
    IStateProperty p = tt();
    for( IStateVariable x : xs ) {
      p.and( x.preserved() );
    }
    return p;
  }*/
}
