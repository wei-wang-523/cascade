package edu.nyu.cascade.c.pass;

@SuppressWarnings("serial")
public class PreProcessorException extends Exception {
	public PreProcessorException(String message) {
		super(message);
	}

	public PreProcessorException(Throwable cause) {
		super(cause);
	}

	public PreProcessorException(String message, Throwable cause) {
		super(message, cause);
	}
}
