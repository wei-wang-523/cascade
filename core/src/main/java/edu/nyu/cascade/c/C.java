/*
 * xtc - The eXTensible Compiler
 * Copyright (C) 2007-2009 Robert Grimm
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301,
 * USA.
 */
package edu.nyu.cascade.c;

import java.math.BigInteger;

/**
 * Common type operations for the C language.
 *
 * @author Robert Grimm
 * @version $Revision: 1.44 $
 */
public abstract class C extends xtc.type.C {

  /** Create a new instance. */
  public C() { /* Nothing to do. */ }
  
  abstract public boolean fitsInt(BigInteger num);
  
  abstract public boolean fitsUnsignedInt(BigInteger num);
  
  abstract boolean fitsLong(BigInteger num);
  
  abstract boolean fitsUnsignedLong(BigInteger num);
  
  abstract public boolean fitsLongLong(BigInteger num);
  
  abstract public boolean fitsUnsignedLongLong(BigInteger num);

  abstract public int BYTE_SIZE();
  
  abstract public BigInteger ARRAY_MAX();
  
  abstract public BigInteger INT_MAX();
  
  abstract public boolean IS_STRING_CONST();
 
	abstract long toWidth(long size);
}
