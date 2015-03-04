package edu.nyu.cascade.util;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.StringWriter;
import java.io.Writer;
import java.nio.CharBuffer;

import xtc.lang.CPrinter;
import xtc.tree.Node;
import xtc.tree.Printer;

public class IOUtils {
  /** The default buffer size for the pipeReader. */
  private static final int DEFAULT_BUFFER_SIZE = 4096;

  /** "Pipes" all the data from a {@link java.io.Reader} into an {@link Appendable}.

      @param inputReader the reader from which to take the input data
      @param appendable the object to which the data is output
      @returns the Appendable object, after all of the data has been written.
   */
  public static Appendable pipeReader(Reader inputReader, Appendable appendable)
      throws IOException {
    int n;
    char[] buf = new char[DEFAULT_BUFFER_SIZE];
    while ((n = inputReader.read(buf)) >= 0) {
    	CharBuffer charBuf = CharBuffer.wrap(buf, 0, n);
      appendable.append(charBuf);
    }

    return appendable;
  }

  /** A "null" output stream. Discards all data written to it. */
  public static final OutputStream NULL_OUTPUT_STREAM;

  /** A Writer to /dev/null */
  public static final Writer NULL_WRITER;
  
  /** A PrintStream to /dev/null */
  public static final PrintStream NULL_PRINT_STREAM;

  /** A Printer to /dev/null */
  private static final Printer NULL_PRINTER;
 
  /** Set to true iff stdout output is enabled */
  private static boolean outFlag = false;

  /** Set to true iff stderr output is enabled */
  private static boolean errFlag = false;

  /** Set to true iff debugging is enabled. */
  private static boolean debugFlag = false;
  
  /** Set to true iff stats is enabled. */
  private static boolean statsFlag = false;
  
  /** Set to true iff tpFile is enabled. */
  private static boolean tpFileFlag = false;
  
  /** Set to true iff trace is enabled. */
  private static boolean traceFlag = false; 

  /** Set to true iff the user has specifically enabled output on stdout */
  private static boolean userEnabledOut = false;

  /** Set to true iff the user has specifically enabled output on stderr */
  private static boolean userEnabledErr = false;

  /** Cascade's stdout stream. */
  private static PrintStream out;

  /** Cascade's stderr stream. */
  private static PrintStream err;

  /** Cascade's debug stream. */
  private static PrintStream debug;
  
  /** Cascade's stats stream. */
  private static PrintStream stats;
  
  /** Cascade's tp-file stream. */
  private static PrintStream tpFile;
  
  /** Cascade's graph-xml-file stream */
  private static PrintStream traceXmlFile;
  
  /** Cascade's trace-file Printer */
  private static Printer traceFilePrinter;

  /** Cascade's stdout Printer. */
  private static Printer outPrinter;

  /** Cascade's stderr Printer. */
  private static Printer errPrinter;

  /** Cascade's debug Printer. */
  private static Printer debugPrinter;
  
  /** Cascade's stats Printer. */
  private static Printer statsPrinter;
  
  /** Cascade's tp-file Printer. */
  private static Printer tpFilePrinter;

  /** Cascade's debug Printer for C ASTs. */
  private static CPrinter cDebugPrinter;

  static {
    /* Set default out/err/debug */
    setOutStream(System.out);
    setErrStream(System.err);
    setDebugStream(System.err);

    /* Set up null outputs */
    NULL_OUTPUT_STREAM = new OutputStream() {
      @Override public void write(int b) { }
    };
    NULL_WRITER = new PrintWriter(NULL_OUTPUT_STREAM);
    NULL_PRINT_STREAM = new PrintStream(NULL_OUTPUT_STREAM);
    NULL_PRINTER = new Printer(NULL_WRITER);
  }

  /** Pretty-print a C AST node to the debug stream. */
  public static Printer debugC(Node node) {
    if (debugFlag) {
      cDebugPrinter.dispatch(node);
    }
    return debug();
  }

  /** Returns the debug printer, if debugging is enabled. Otherwise,
   * returns a null printer. */
  public static Printer debug() {
    return debugFlag ? debugPrinter : NULL_PRINTER;
  }
  
  /** Returns the stdstats stream, if output to stdstats is enabled. Otherwise,
  returns a null stream. */
  public static Printer stats() {
  	return statsFlag ? statsPrinter : NULL_PRINTER;
  }
  
  /** Returns the tp-file printer, if tp-file is enabled. Otherwise,
   * returns a null printer. */
  public static Printer tpFile() {
    return tpFileFlag ? tpFilePrinter : NULL_PRINTER;
  }
  
  /** Return the trace-file stream, if traceFlag is enabled. Otherwise,
   *   returna a null stream. */
  public static Printer traceFile() {
  	return traceFlag ? traceFilePrinter : NULL_PRINTER;
  }
  
  /** Return the trace-xml-file stream, if traceFlag is enabled. Otherwise,
   *   returna a null stream. */
  public static PrintStream traceXmlFileStream() {
  	return traceFlag ? traceXmlFile : NULL_PRINT_STREAM;
  }

  /** Returns true iff debugging is enabled. */
  public static boolean debugEnabled() {
    return debugFlag;
  }
  
  /** Returns true iff tpFile is enabled. */
  public static boolean tpFileEnabled() {
    return tpFileFlag;
  }
  
  /** Returns true iff tpFile is enabled. */
  public static boolean statsEnabled() {
    return statsFlag;
  }

  /** Returns the debug stream, if debugging is enabled. Otherwise,
      returns a null stream. */
  public static PrintStream debugStream() {
    return debugFlag ? debug: NULL_PRINT_STREAM;
  }
  
  /** Returns the stats stream, if stats is enabled. Otherwise,
  returns a null stream. */
  public static PrintStream statsStream() {
  	return statsFlag ? stats: NULL_PRINT_STREAM;
  }
  
  /** Returns the tp-file stream, if tp-file is enabled. Otherwrise,
       returns a null stream. */
  public static PrintStream tpFileStream() {
    return tpFileFlag ? tpFile: NULL_PRINT_STREAM;
  }
  
  /** Disables debugging output. Also disables output to stdout and stderr,
      if they have not been explicitly enabled by a call to 
      <code>enableOut()</code> or <code>enableErr()</code>. */
  public static void disableDebug() {
    debugFlag = false;
    outFlag = userEnabledOut;
    errFlag = userEnabledErr;
  }

  /** Disables output on stdout. */
	public static void disableStats() {
	  statsFlag = false;
	}

	/** Disables output on stderr. */
  public static void disableErr() {
    errFlag = false;
    userEnabledErr = false;
  }
  
  /** Disables output on tp-file. */
  public static void disableTpFile() {
    tpFileFlag = false;
  }

  /** Disables output on stdout. */
  public static void disableOut() {
    outFlag = false;
    userEnabledOut = false;
  }
  
  public static void disableTrace() {
  	if(traceFlag) {
  		traceFlag = false;
  		traceFilePrinter.flush().close();
  		traceXmlFile.close();
  	}
  }

  /** Enables debugging output. Also enables output on stdout and stderr, 
      if they were not previously enabled. */
  public static void enableDebug() {
    debugFlag = true;
    outFlag = true;
    errFlag = true;
  }
  
  /** Enables output on tp-file. */
  public static void enableTpFile() {
    tpFileFlag = true;
  }
  
  /** Enables output on tp-file. */
  public static void enableStats() {
    statsFlag = true;
  }

  /** Enables output on stderr. */
  public static void enableErr() {
    errFlag = true;
    userEnabledErr = true;
  }

	/** Enables output on stdout. */
  public static void enableOut() {
    outFlag = true;
    userEnabledOut = true;
  }

  public static void enableTrace(File file) {
  	traceFlag = true;
  	File dumpDir = FileUtils.createDumpDir(file.getName());
  	File witnessFile = FileUtils.filePath(dumpDir, "witness.out");
  	File witnessXmlFile = FileUtils.filePath(dumpDir, "witness.graphml");
  	
  	try {
  		if (!witnessFile.exists()) witnessFile.createNewFile();
  		if (!witnessXmlFile.exists()) witnessXmlFile.createNewFile();
  		
  		traceFilePrinter = new Printer(new PrintStream(witnessFile));
  		traceXmlFile = new PrintStream(witnessXmlFile);
  		
  	} catch (IOException e) {
			throw new RuntimeException("Unexpected witness dumping exception", e);
		}
	}

	/** Returns the stderr stream, if output to stderr is enabled. Otherwise,
      returns a null stream. */
  public static PrintStream err() {
    return errFlag ? err : NULL_PRINT_STREAM;
  }

  /** Returns the stderr printer, if output to stderr is enabled. Otherwise,
      returns a null printer. */
  public static Printer errPrinter() {
    return errFlag ? errPrinter : NULL_PRINTER;
  }

  /** Returns a string representing the C AST node in pretty-printed form. */
  public static String formatC(Node node) {
    StringWriter cStringWriter = new StringWriter();
    CPrinter cStringPrinter = new CPrinter(new Printer(cStringWriter));
    cStringPrinter.dispatch(node);
    return cStringWriter.toString();
  }

  /** Returns the stdout stream, if output to stdout is enabled. Otherwise,
      returns a null stream. */
  public static PrintStream out() {
    return outFlag ? out : NULL_PRINT_STREAM ;
  }
  
  /** Returns the stdout printer, if output to stdout is enabled. Otherwise,
      returns a null printer. */
  public static Printer outPrinter() {
    return outFlag ? outPrinter : NULL_PRINTER ;
  }
  
  /** Sets the debug stream. NOTE: this method does not <em>enable</em> debug
      output, it only modifies the output stream. Use <code>enableDebug()</code>
      to enable output. */
  public static void setDebugStream(PrintStream s) {
    debug = s;
    debugPrinter = new FlushingPrinter(s);
    cDebugPrinter = new CPrinter(debugPrinter);
  }
  
  /** Sets the tp-file stream. */
  public static void setTpFileStream(PrintStream s) {
    tpFile = s;
    tpFilePrinter = new FlushingPrinter(s); 
  }
  
  /** Sets the stderr stream. NOTE: this method does not <em>enable</em> stderr
      output, it only modifies the output stream. Use <code>enableErr()</code>
      to enable output. */
  public static void setErrStream(PrintStream err) {
    IOUtils.err = err;
    errPrinter = new FlushingPrinter(err);
  }

  /** Sets the stdout stream. NOTE: this method does not <em>enable</em> stdout
      output, it only modifies the output stream. Use <code>enableOut()</code>
      to enable output. */
  public static void setOutStream(PrintStream out) {
    IOUtils.out = out;
    outPrinter = new FlushingPrinter(out);
  }

	public static void setStatsStream(PrintStream s) {
    stats = s;
    statsPrinter = new FlushingPrinter(s);
  }
}
