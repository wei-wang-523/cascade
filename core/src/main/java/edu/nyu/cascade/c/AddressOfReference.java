package edu.nyu.cascade.c;

import java.io.IOException;
import java.math.BigInteger;

import xtc.type.C;
import xtc.type.PointerT;
import xtc.type.Reference;
import xtc.type.RelativeReference;

/**
 * Representation of a address of reference. 
 * 
 * @author Wei
 *
 */
public class AddressOfReference extends RelativeReference {

  /**
   * Create a new address of reference.
   *
   * @param base The base reference.
   * @param type The type of base
   */
  public AddressOfReference(Reference base) {
    super(new PointerT(base.getType()), base);
  }
  
  @Override
  public boolean hasLocation() {
    return base.hasLocation();
  }

  @Override
  public BigInteger getLocation(C ops) {
    return base.getLocation(ops);
  }

  @Override
  public int hashCode() {
    return base.hashCode();
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (! (o instanceof AddressOfReference)) return false;
    AddressOfReference other = (AddressOfReference)o;
    return this.base.equals(other.base) && this.type.equals(other.type);
  }
  
  @Override
  public void write(Appendable out) throws IOException {
    out.append("&(");
    base.write(out);
    out.append(')');
  }
}
