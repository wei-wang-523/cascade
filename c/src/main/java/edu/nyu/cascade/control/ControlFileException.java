package edu.nyu.cascade.control;

@SuppressWarnings("serial")
public class ControlFileException extends Exception {
	public ControlFileException(String msg, Throwable cause) {
		super(msg, cause);
	}

	public ControlFileException(Throwable cause) {
		super(cause);
	}

	public ControlFileException(String msg) {
		super(msg);
	}
}
