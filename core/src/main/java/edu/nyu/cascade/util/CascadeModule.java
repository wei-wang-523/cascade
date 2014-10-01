package edu.nyu.cascade.util;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;

import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;

public class CascadeModule extends AbstractModule {
  @Override
  protected void configure() {
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
