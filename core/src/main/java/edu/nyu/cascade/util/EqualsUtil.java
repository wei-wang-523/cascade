/*  
 Copyright (c) 2002-2009, Hirondelle Systems
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 * Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in the
       documentation and/or other materials provided with the distribution.
 * Neither the name of Hirondelle Systems nor the
       names of its contributors may be used to endorse or promote products
       derived from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY HIRONDELLE SYSTEMS ''AS IS'' AND ANY
 EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL HIRONDELLE SYSTEMS BE LIABLE FOR ANY
 DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package edu.nyu.cascade.util;

/**
 * Collected methods which allow easy implementation of <code>equals</code>.
 *
 * Example use case in a class called Car:
 * 
 * <pre>
 * public boolean equals(Object aThat) {
 * 	if (this == aThat)
 * 		return true;
 * 	if (!(aThat instanceof Car))
 * 		return false;
 * 	Car that = (Car) aThat;
 * 	return EqualsUtil.areEqual(this.fName, that.fName) && EqualsUtil.areEqual(
 * 			this.fNumDoors, that.fNumDoors) && EqualsUtil.areEqual(
 * 					this.fGasMileage, that.fGasMileage) && EqualsUtil.areEqual(
 * 							this.fColor, that.fColor) && Arrays.equals(
 * 									this.fMaintenanceChecks, that.fMaintenanceChecks); // array!
 * }
 * </pre>
 *
 * <em>Arrays are not handled by this class</em>. This is because the
 * <code>Arrays.equals</code> methods should be used for array fields.
 *
 * Code provided by: http://www.javapractices.com
 */
public final class EqualsUtil {

	static public boolean areEqual(boolean aThis, boolean aThat) {
		// System.out.println("boolean");
		return aThis == aThat;
	}

	static public boolean areEqual(char aThis, char aThat) {
		// System.out.println("char");
		return aThis == aThat;
	}

	static public boolean areEqual(long aThis, long aThat) {
		/*
		 * Implementation Note Note that byte, short, and int are handled by this
		 * method, through implicit conversion.
		 */
		// System.out.println("long");
		return aThis == aThat;
	}

	static public boolean areEqual(float aThis, float aThat) {
		// System.out.println("float");
		return Float.floatToIntBits(aThis) == Float.floatToIntBits(aThat);
	}

	static public boolean areEqual(double aThis, double aThat) {
		// System.out.println("double");
		return Double.doubleToLongBits(aThis) == Double.doubleToLongBits(aThat);
	}

	/**
	 * Possibly-null object field.
	 *
	 * Includes type-safe enumerations and collections, but does not include
	 * arrays. See class comment.
	 */
	static public boolean areEqual(Object aThis, Object aThat) {
		// System.out.println("Object");
		return aThis == null ? aThat == null : aThis.equals(aThat);
	}

	static public boolean areEqual(Object[] aThis, Object[] aThat) {
		// System.out.println("Array");
		if (aThis.length != aThat.length)
			return false;

		for (int i = 0; i < aThis.length; i++) {
			if (!aThis[i].equals(aThat[i]))
				return false;
		}

		return true;
	}
}
