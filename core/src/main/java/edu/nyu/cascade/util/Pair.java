package edu.nyu.cascade.util;

public class Pair<T,U> {
  public static <T,U> Pair<T,U> of(T t, U u) {
    return new Pair<T,U>(t,u);
  }
  
  private final T fst;
  private final U snd;
  
  private Pair(T fst, U snd) {
    this.fst = fst;
    this.snd = snd;
  }
  
  public T fst() {
    return fst;
  }
  
  public U snd() { 
    return snd;
  }
  
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof Pair))    return false;
    Pair pair = (Pair) o;
    if(fst == pair.fst()) {
      if(snd == pair.snd())     return true;
      if(snd.equals(pair.snd))  return true;
      return false;
    } else if(fst.equals(pair.fst())) {
      if(snd == pair.snd())     return true;
      if(snd.equals(pair.snd))  return true;
      return false;
    }
    return false;
  }
  
  @Override
  public String toString() {
    return "(" + fst + "," + snd + ")";
  }
  
  @Override
  public int hashCode() {
    int result = HashCodeUtil.SEED;
    //collect the contributions of various fields
    result = HashCodeUtil.hash(result, fst);
    result = HashCodeUtil.hash(result, snd);
    return result;
  }
}
