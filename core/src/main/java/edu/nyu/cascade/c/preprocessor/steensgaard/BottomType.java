package edu.nyu.cascade.c.preprocessor.steensgaard;

class BottomType extends ValueType {

	ValueTypeKind getKind() {
		return ValueTypeKind.BOTTOM;
	}
	
  @Override
  public String toString() {
    return "BOT";
  }
  
  @Override
  public boolean equals(Object t) {
    if(!(t instanceof BottomType))   return false;
    return true;
  }
}
