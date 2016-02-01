/**
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>
 */
package edu.nyu.cascade.prover;

import org.apache.commons.cli.Option;

import edu.nyu.cascade.prover.TheoremProverFactory.Capability;

/**
 * Provides access to theorem prover services.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 */
public interface TheoremProver {
  static interface Provider {
    TheoremProver create();
    Iterable<Capability> getCapabilities();
    String getName();
    
    /**
     * Returns a list of implementation-specific options.
     */
    Iterable<Option> getOptions();
  }
  
  /**
   * Returns the theorem prover's expression manager. All the expressions of
   * that the IR uses should be constructed using the expression manager of a
   * corresponding theorem prover.
   * 
   * @return the expression manager.
   */
  ExpressionManager getExpressionManager();

  ValidityResult<?> checkValidity(Expression bool) ;

  SatResult<?> checkSat(Expression expr) ;
  
  void assume(Iterable<? extends Expression> propositions) ;
  void assume(Expression first, Expression... rest) ;
  void clearAssumptions() ;
  
  /**
   * Set implementation-specific properties, possibly by referring to 
   * <code>edu.nyu.cascade.util.Preferences</code>.
   */
  void setPreferences() ;
  
  String getProviderName();

	long getStatsTime();
	
	/**
	 * Get the evaluation of <code>expr</code> based on model
	 * @param expr
	 * @return
	 */
	Expression evaluate(Expression expr);
}
