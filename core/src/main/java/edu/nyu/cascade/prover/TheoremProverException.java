package edu.nyu.cascade.prover;

@SuppressWarnings("serial")
public class TheoremProverException extends RuntimeException {
  public TheoremProverException(String msg) {
    super(msg);
  }
  public TheoremProverException(String msg, Throwable cause) {
    super(msg,cause);
  }
  public TheoremProverException(Throwable cause) {
    super(cause);
  }
}
