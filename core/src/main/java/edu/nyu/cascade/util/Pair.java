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

  public String toString() {
    return "(" + fst + "," + snd + ")";
  }
}
