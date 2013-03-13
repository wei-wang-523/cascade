package edu.nyu.cascade.ir.expr;

@SuppressWarnings("serial")
public class PathFactoryException extends Exception {
  public PathFactoryException(String message) {
    super(message);
  }

  public PathFactoryException(Throwable cause) {
    super(cause);
  }

  public PathFactoryException(String message, Throwable cause) {
    super(message, cause);
  }
}
