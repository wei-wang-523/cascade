package edu.nyu.cascade.c;

@SuppressWarnings("serial")
public class CfgBuilderException extends Exception {

	public CfgBuilderException(String msg) {
		super(msg);
	}

	public CfgBuilderException(Throwable cause) {
		super(cause);
	}

	public CfgBuilderException(String msg, Throwable cause) {
		super(msg, cause);
	}
}
