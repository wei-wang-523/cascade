/**
 * This program is free software: you can redistribute it and/or modify it under the terms of the 
 * GNU Lesser General Public License as published by the Free Software Foundation, either version 
 * 3 of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; 
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. 
 * See the GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License along with this program.
 * If not, see <http://www.gnu.org/licenses/>
 */
package edu.nyu.cascade.fds;

import edu.nyu.cascade.util.Pair;

/**
 * Defines the Fair Discrete System structure.
 */
public interface FairDiscreteSystem extends TransitionSystem {
  /**
   * A set of state properties. Each property J represents the constraint that
   * any valid trace of the system must have infinitely many J-states.
   */
  StateProperty[] justiceRequirements();

  /**
   * A set of (p,q) pairs, where p and q are state properties. Each (p,q)
   * represents the constraint that any valid trace of the system with
   * infinitely many p-states will also have infinitely many q states.
   */
  Pair<? extends StateProperty, ? extends StateProperty>[] compassionRequirements();
}
