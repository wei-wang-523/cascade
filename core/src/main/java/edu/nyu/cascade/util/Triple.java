package edu.nyu.cascade.util;

public class Triple<T,U,V> {
  public static <T,U,V> Triple<T,U,V> of(T t, U u, V v) {
    return new Triple<T,U,V>(t,u,v);
  }
  
  private final T fst;
  private final U snd;
  private final V thd;
  
  private Triple(T fst, U snd, V thd) {
    this.fst = fst;
    this.snd = snd;
    this.thd = thd;
  }
  
  public T fst() {
    return fst;
  }
  
  public U snd() { 
    return snd;
  }
  
  public V thd() {
  	return thd;
  }
  
  @SuppressWarnings("rawtypes")
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof Triple))    return false;
    Triple triple = (Triple) o;
    if(fst == triple.fst()) {
      if(snd == triple.snd()) {
      	if(thd == triple.thd)					return true;
      	if(thd.equals(triple.thd()))	return true;
      	return false;
      }
      if(snd.equals(triple.snd)) {
      	if(thd == triple.thd)					return true;
      	if(thd.equals(triple.thd()))	return true;
      	return false;
      }
      return false;
    } else if(fst.equals(triple.fst())) {
      if(snd == triple.snd()) {
      	if(thd == triple.thd)					return true;
      	if(thd.equals(triple.thd()))	return true;
      	return false;
      }
      if(snd.equals(triple.snd)) {
      	if(thd == triple.thd)					return true;
      	if(thd.equals(triple.thd()))	return true;
      	return false;
      }
      return false;
    }
    return false;
  }
  
  @Override
  public String toString() {
    return "(" + fst + "," + snd + "," + thd + ")";
  }
  
  @Override
  public int hashCode() {
    int result = HashCodeUtil.SEED;
    //collect the contributions of various fields
    result = HashCodeUtil.hash(result, fst);
    result = HashCodeUtil.hash(result, snd);
    result = HashCodeUtil.hash(result, thd);
    return result;
  }
}
