package edu.nyu.cascade.c;

@SuppressWarnings("serial")
public class CascadeException extends Exception {
  public CascadeException(String msg, Throwable cause) {
    super(msg,cause);
  }
}
