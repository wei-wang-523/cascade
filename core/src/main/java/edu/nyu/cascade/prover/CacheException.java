package edu.nyu.cascade.prover;

@SuppressWarnings("serial")
public class CacheException extends RuntimeException {
  public CacheException(String msg) {
    super(msg);
  }
  public CacheException(String msg, Throwable cause) {
    super(msg,cause);
  }
  public CacheException(Throwable cause) {
    super(cause);
  }
}
