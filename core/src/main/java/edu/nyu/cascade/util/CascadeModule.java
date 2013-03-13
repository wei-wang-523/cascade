package edu.nyu.cascade.util;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;

import edu.nyu.cascade.fds.StateExpression;
import edu.nyu.cascade.fds.StateExpressionImpl;
import edu.nyu.cascade.fds.StateProperty;
import edu.nyu.cascade.fds.StatePropertyImpl;
import edu.nyu.cascade.fds.TemporalExpressionEncoding;
import edu.nyu.cascade.fds.TemporalExpressionEncodingImpl;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;

public class CascadeModule extends AbstractModule {
  @Override
  protected void configure() {
    bind(StateExpression.Factory.class).to(StateExpressionImpl.Factory.class);
    bind(StateProperty.Factory.class).to(StatePropertyImpl.Factory.class);
    bind(TemporalExpressionEncoding.Factory.class).to(
            TemporalExpressionEncodingImpl.Factory.class);
  }

  @Provides
  public TheoremProver provideTheoremProver() throws TheoremProverFactoryException {
    return TheoremProverFactory.getInstance();
  }

 @Provides
  public ExpressionManager provideExpressionManager(TheoremProver theoremProver) {
    return theoremProver.getExpressionManager();
  }

}
