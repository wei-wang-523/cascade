package edu.nyu.cascade.c;

@SuppressWarnings("serial")
class RunProcessorException extends Exception {
	public RunProcessorException(String msg) {
		super(msg);
	}

	public RunProcessorException(String msg, Throwable cause) {
		super(msg, cause);
	}

	public RunProcessorException(Throwable cause) {
		super(cause);
	}
}