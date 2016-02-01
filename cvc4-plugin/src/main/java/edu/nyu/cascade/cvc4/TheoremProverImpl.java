package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.DATATYPES;
import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.SMT;

import java.io.File;
import java.io.PrintStream;
//import java.lang.management.ManagementFactory;
import java.util.List;
import java.util.regex.Pattern;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Options;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.prover.TheoremProverFactory.Capability;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

/**
 * Implements the theorem prover interface using the cvc4 implementation.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 */
public class TheoremProverImpl implements TheoremProver {

	public static class Provider implements TheoremProver.Provider {

    @Override
    public TheoremProver create() {
      return new TheoremProverImpl();
    }

    @Override
    public Iterable<Capability> getCapabilities() {
      return Lists.newArrayList(SMT, DATATYPES);
    }

    @Override
    public String getName() {
      return Preferences.PROVER_CVC4;
    }

    @SuppressWarnings("static-access")
    @Override
    public ImmutableList<Option> getOptions() {
      return ImmutableList
          .of(OptionBuilder.withLongOpt(OPTION_DUMP_LOG) //
              .hasArg() //
              .withArgName("FILE") //
              .withType(File.class) //
              .withDescription("Dump CVC4 activity to log FILE") //
              .create(), //
              OptionBuilder.withLongOpt(OPTION_DUMP_TRACE) //
                  .hasArg() //
                  .withArgName("FILE") //
                  .withType(File.class) //
                  .withDescription("Dump CVC4 traces to log FILE") //
                  .create(), //
              OptionBuilder
                  .withLongOpt(OPTION_TRACE)
                  .hasArg()
                  .withArgName("TAGs")
                  .withDescription(
                      "Enable CVC4 trace FLAGS (comma-separated list)") //
                  .create(), //
              OptionBuilder.withLongOpt(OPTION_NO_TYPE_CORRECTNESS_CONDITIONS) //
                  .withDescription("Disable CVC4 type-correctness conditions") //
                  .create(), //
              OptionBuilder
                  .withLongOpt(OPTION_QUANT_LIMIT)
                  .hasArg()
                  .withArgName("N")
                  .withType(Integer.class)
                  .withDescription(
                      "Set CVC4 quantifier instantiation limit to N") //
                  .create());

    }

  }

/*  private static final int DEFAULT_MAX_QUANTIFIER_LEVEL = 10;
  private static final String FLAG_DUMP_LOG = "dump-log";
  private static final String FLAG_DUMP_TRACE = "dump-trace";
  private static final String FLAG_QUANT_MAX_INST_LEVEL = "quant-max-IL";
  private static final String FLAG_TRACE = "trace";
  private static final String FLAG_TYPE_CORRECTNESS_CONDITIONS = "tcc";*/

  private static final String OPTION_DUMP_LOG = "cvc4-log";
  private static final String OPTION_DUMP_TRACE = "cvc4-dump-trace";
  private static final String OPTION_TP_STATS = "cvc4-stats";
  private static final String OPTION_QUANT_LIMIT = "cvc4-quant-limit";
  private static final String OPTION_TRACE = "cvc4-trace";
  private static final String OPTION_DEBUG = "cvc4-debug";
  private static final String OPTION_NO_TYPE_CORRECTNESS_CONDITIONS = "cvc4-notcc";

  private static final Pattern p = Pattern.compile("(^|\\n|\\r\\n?)");

  static void debugCall(String string) {
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "CVC.API> ") + ";").flush();
    }
  }

  static void debugCall(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCall(String.format(format, objects));
    }
  }

  static void debugCommand(String string) {
    // p.matcher(string).replaceAll("\1CVC> ");
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "CVC> ") + ";").flush();
    }
  }
  
  static void tpFileCommand(String prefix, Expr cvc4Expr, String postfix) {
    if(IOUtils.tpFileEnabled()) {
    	PrintStream stream = IOUtils.tpFileStream().append(prefix);
    	cvc4Expr.toStream(stream);
      // cvc4Expr.toStream(stream, -1, false, 1, edu.nyu.acsys.CVC4.OutputLanguage.OUTPUT_LANG_SMTLIB_V2);
      stream.append(postfix).append('\n').flush();
    }
  }
  
	static void tpFileCommand(String prefix, Type cvc4Type, String postfix) {
    if(IOUtils.tpFileEnabled()) {
    	PrintStream stream = IOUtils.tpFileStream().append(prefix);
    	cvc4Type.toStream(stream);
      stream.append(postfix).append('\n').flush();
    }
  }
  
	static void tpFileCommand(String string) {
    if(IOUtils.tpFileEnabled()) {
      IOUtils.tpFile().pln(string).flush();
    }
  }
  
	static void debugCommand(String prefix, Expr cvc4Expr, String postfix) {
    if(IOUtils.debugEnabled()) {
    	PrintStream stream = IOUtils.debugStream().append(prefix);
      cvc4Expr.toStream(stream);
      stream.append(postfix).flush();
    }
  }
  
	static void debugCommand(String prefix, Type cvc4Type, String postfix) {
    if(IOUtils.debugEnabled()) {
    	PrintStream stream = IOUtils.debugStream().append(prefix);
    	cvc4Type.toStream(stream);
      stream.append(postfix).flush();
    }
  }

	static void debugCommand(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCommand(String.format(format, objects));
    }
  }
  
	static void tpFileCommand(String format, Object... objects) {
    if (IOUtils.tpFileEnabled()) {
      tpFileCommand(String.format(format, objects));
    }
  }

  private static String prefixLinesWith(String str, String prefix) {
    return p.matcher(str).replaceAll("$1" + prefix);
  }

  /* private ValidityChecker validityChecker; */
  
  /**
   * The cvc4 copy we will be using.
   */
  private ExprManager cvc4ExprManager;
  
  /**
   * The smt engine we will be using
   */
  private SmtEngine smtEngine;

  /**
   * The expression manager of this cvc4 instance
   */
  private ExpressionManagerImpl exprManager;

  /** A list of asserted expressions. */
  private final List<BooleanExpression> assumptions;

  /**
   * This constructor is an escape hatch for subclasses to do initialization
   * themselves.
   */
  protected TheoremProverImpl(ExprManager em) throws TheoremProverException {
    cvc4ExprManager = em;
    smtEngine = new SmtEngine(em);
    exprManager = null;
    assumptions = Lists.newArrayList();
    initializePreferences();
  }

  /**
   * Construct a new CVC4 theorem prover.
   */
  TheoremProverImpl() {
    
    // Create the cvc4 expression manager
    cvc4ExprManager = null;
    
    // Create the smt engine
    smtEngine = null;

    // Create the expression manager
    exprManager = null;

    assumptions = Lists.newArrayList();
  }

  @Override
  public void assume(Expression first,
      Expression... rest) {
    assume(Lists.asList(first, rest));
  }

  @Override
  public void assume(Iterable<? extends Expression> propositions) {
    for( Expression e : propositions ) {
      Preconditions.checkArgument(e.isBoolean());
      Expr assump = exprManager.toCvc4Expr(e);
      debugCommand("(assert ", assump, ")");
      tpFileCommand("(assert ", assump, ")");
      getSmtEngine().assertFormula( assump );
      assumptions.add(e.asBooleanExpression());
    }
  }
  
  @Override
  public SatResult<?> checkSat(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    try {
    	
      getSmtEngine().push();
      tpFileCommand("(push)");

      Expr cvc4Expr = exprManager.toCvc4Expr(expr);
      Expr cvc4ExprSimp = getSmtEngine().simplify(cvc4Expr);
      
      if (IOUtils.debugEnabled()) {        
        IOUtils.debug().pln(
                            "Simplified: "
                                + cvc4ExprSimp).flush();
      }
      
      debugCommand("(assert " + cvc4ExprSimp, ")");
      tpFileCommand("(assert ", cvc4Expr, ")");
      
      debugCommand("(check-sat)");
      tpFileCommand("(check-sat)");     
      Result cvc4SatResult = getSmtEngine().checkSat(cvc4Expr);
      IOUtils.debug().pln(cvc4SatResult.toString()).flush();
      SatResult.Type resultType = convertCvc4SatResult(cvc4SatResult);

      SatResult<?> res;
      if (SatResult.Type.UNSAT.equals(resultType)) {
        res = SatResult.unsat(expr);
      } else if (SatResult.Type.SAT.equals(resultType)){        
        /**
         * In theory, a query that returns INVALID instead of UNKNOWN should be
         * able to provide a model. For whatever reason, this sometimes fails,
         * so we catch any Exception in the model generation phase and
         * revert to using a counter-example.
         */
        List<BooleanExpression> ctrex = Lists.newLinkedList();
        boolean modelWorked = false;
        
        if(Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE)) {
          try {
            for (Expression e: exprManager.getVariables()) {
              Expr eValue = getSmtEngine().getValue(exprManager.toCvc4Expr(e));
              ctrex.add(e.eq((ExpressionImpl) exprManager.toExpression(eValue)));
            }   
            modelWorked = true;
          } catch (Exception e) {
            IOUtils.err().println("[WARNING] " + e.getMessage());
            ctrex.clear();
          }
          
          if (!modelWorked) {
            for (Expression e : exprManager.getVariables()) {
              ctrex.add(e.asBooleanExpression());
            }
          }
        }
        
        res = SatResult.valueOf(resultType, expr, assumptions, ctrex);
      } else { // resultType = UNKNOWN
        res = SatResult.valueOf(resultType, expr, assumptions, 
            cvc4SatResult.whyUnknown().toString()); 
      }

      if (Preferences.isSet(OPTION_TP_STATS)) {
        getSmtEngine().getStatistics().flushInformation(IOUtils.out());
      }
      
      getSmtEngine().pop();
      tpFileCommand("(pop)");

      return res;
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ValidityResult<?> checkValidity(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    try {
      
      getSmtEngine().push();
      tpFileCommand("(push)");
      
      Expr cvc4Expr = exprManager.toCvc4Expr(expr);
      Expr cvc4ExprSimp = getSmtEngine().simplify(cvc4Expr);
      
      if (IOUtils.debugEnabled()) {  
        IOUtils.debug().pln(
                            "Simplified: " + cvc4ExprSimp)
                                .flush();
      }
      
      debugCommand("(assert ", cvc4ExprSimp, ")");
      tpFileCommand("(assert ", cvc4Expr, ")");
      
      debugCommand("(check-sat)");
      tpFileCommand("(check-sat)");
      
//      IOUtils.out().println(ManagementFactory.getRuntimeMXBean().getName());
      long start = System.currentTimeMillis(); 
      Result cvc4QueryResult = getSmtEngine().query(cvc4Expr);
      IOUtils.stats().pln("CVC4 took time: " + (System.currentTimeMillis() - start)/1000.0 + "s");
      IOUtils.debug().pln(cvc4QueryResult.toString());
      ValidityResult.Type resultType = convertCvc4QueryResult(cvc4QueryResult);

      ValidityResult<?> res;
      if (ValidityResult.Type.VALID.equals(resultType)) {
        res = ValidityResult.valid(expr);
      } else if (ValidityResult.Type.INVALID.equals(resultType)){        
        /**
         * In theory, a query that returns INVALID instead of UNKNOWN should be
         * able to provide a model. For whatever reason, this sometimes fails,
         * so we catch any Exception in the model generation phase and
         * revert to using a counter-example.
         */
        List<BooleanExpression> ctrex = Lists.newArrayList();
        boolean modelWorked = false;
        
        try {
          for (Expression e: exprManager.getVariables()) {
            Expr eValue = getSmtEngine().getValue(exprManager.toCvc4Expr(e));
            ctrex.add(e.eq((ExpressionImpl) exprManager.toExpression(eValue)));
          }   
          modelWorked = true;
        } catch (Exception e) {
          IOUtils.err().println("[WARNING] " + e.getMessage());
          ctrex.clear();
        }
        
        if (!modelWorked) {
          for (Expression e : exprManager.getVariables()) {
            ctrex.add(e.asBooleanExpression());
          }
        }
        
        res = ValidityResult.valueOf(resultType, expr, assumptions, ctrex);
          
      } else { // resultType = UNKNOWN
        res = ValidityResult.valueOf(resultType, expr, assumptions, 
            cvc4QueryResult.whyUnknown().toString()); 
      }

      if (Preferences.isSet(OPTION_TP_STATS)) {
        getSmtEngine().getStatistics().flushInformation(IOUtils.out());
      }
      
      getSmtEngine().pop();
      tpFileCommand("(pop)");
      
      return res;
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public void clearAssumptions() {
  	assumptions.clear();
  }

  private ValidityResult.Type convertCvc4QueryResult(Result validResult) {
    if(validResult.isUnknown()) {
      return ValidityResult.Type.valueOf("UNKNOWN");
    }
    return ValidityResult.Type.valueOf(validResult.toString().toUpperCase());
  }

  private SatResult.Type convertCvc4SatResult(Result satResult) {
    if(satResult.isUnknown()) {
      return SatResult.Type.valueOf("UNKNOWN");
    }
    return SatResult.Type.valueOf(satResult.toString().toUpperCase());
  }

/*  public Iterable<Capability> getCapabilities() {
    return Lists.newArrayList(SMT, DATATYPES) ;
  } */
  
  /**
   * Returns the cascade expression manager.
   */
  public ExpressionManagerImpl getExpressionManager() {
    // Return the expression manager of this instance
    if (exprManager == null) {
      exprManager = new ExpressionManagerImpl(this);
    }
    return exprManager;
  }

/*  public ValidityChecker getCvc4ExprManager() {
    if (validityChecker == null) {
      validityChecker = ValidityChecker.create(flags);
    }
    return validityChecker;
  }*/
  
  /**
   * Returns the cvc4 expression manager.
   * 
   * @return the expression manager
   */
  public ExprManager getCvc4ExprManager() {
    if(cvc4ExprManager == null) {
      /** 
       * FIXME: default loading library "cvc4" with linked error
       * to find edu.nyu.acsys.CVC4.CVC4JNI.new_ExprManager__SWIG_0()
       */
      System.loadLibrary("cvc4jni");

      Options opts = new Options();
      opts.parseOptions(2, new String[] { "cascade", "--output-lang=cvc4" });
      cvc4ExprManager = new ExprManager(opts);
    }
    return cvc4ExprManager;
  }
  
  /**
   * Returns the smt Engine.
   * 
   * @return the expression manager
   */
  SmtEngine getSmtEngine() {
    if(smtEngine == null) {
      smtEngine = new SmtEngine(getCvc4ExprManager());
      initializePreferences();
    }
    return smtEngine;
  }
  

  /**
   * Set an "effort level" for validity and satisfiability queries. In this
   * implementation, the CVC4 "resource limit" varies linearly and the
   * quantifier instantiation limit varies logarithmically with the effort
   * level. An effort level of <math>n</math> corresponds to a CVC4
   * "resource limit" <math>256n</math> and a maximum quantifier instantiation
   * level of <math>log(n)</code>. A value of 0 means no resource limit and a
   * default maximum quantifier instantiation level.
   */
  
  public void setEffortLevel(int level) {
    try {
      getSmtEngine().setResourceLimit(level << 8);
      
/*      FlagsMut flags = getCvc4ExprManager().getFlags();
      flags.setFlag(FLAG_QUANT_MAX_INST_LEVEL,
                    level > 0 ? (int) Math.log(level)
                        : DEFAULT_MAX_QUANTIFIER_LEVEL);      
*/    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  /**
   * Set an "time level" for validity and satisfiability queries. In this
   * implementation, the CVC4 "time limit" varies with the time
   * level. An time level of <math>n</math> corresponds to a CVC4
   * "time limit" <math>256n</math>. A value of 0 means no time limit.
   */

  public void setTimeLimit(int second) {
    try {
      getSmtEngine().setTimeLimit(second * 1000);
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  private void enableCvc4Stats() {
    try {
      getSmtEngine().setOption("statistics", new SExpr("true"));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  private void enableCvc4Trace(String s) {
    try {
      getSmtEngine().setOption("trace", new SExpr(s));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  private void enableCvc4Debug(String s) {
    try {
      getSmtEngine().setOption("debug", new SExpr(s));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  /*
   * private int getIntOption(Map<String,Object> properties, String option) {
   * String s = (String) properties.get(option); try { return
   * Integer.parseInt(s); } catch( NumberFormatException e ) { throw new
   * IllegalArgumentException("Invalid opt: " + s, e); } }
   */
  
  /**
   * Set implementation-specific properties from {@link Preferences}.
   */
  @Override
  public void setPreferences() {
    try {      
      if (Preferences.isSet(OPTION_TP_STATS)) {
        enableCvc4Stats();
      }
      
      if (Preferences.isSet(OPTION_TRACE)) {
        for( String flag : Preferences.getString(OPTION_TRACE).split(",") ) {
          enableCvc4Trace(flag);
        }
      }
      
      if (Preferences.isSet(OPTION_DEBUG)) {
        for( String flag : Preferences.getString(OPTION_DEBUG).split(",") ) {
          enableCvc4Debug(flag);
        }
      }
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  ImmutableList<Option> getOptions() {
    return new Provider().getOptions();
  }
  
  private void initializePreferences() {
    // always incremental and model-producing in cascade mode
    // also incrementally-simplifying and interactive
    smtEngine.setOption("incremental", new SExpr("true"));
    smtEngine.setOption("produce-models", new SExpr("true"));
    //    smtEngine.setOption("simplification-mode", new SExpr("incremental"));
    smtEngine.setOption("interactive-mode", new SExpr("true")); // support SmtEngine::getAssertions()
    smtEngine.setOption("produce-assignments", new SExpr("true"));
    smtEngine.setOption("statistics", new SExpr("false"));
    smtEngine.setOption("random-seed", new SExpr("91648253"));
    smtEngine.setOption("parse-only", new SExpr("false"));
    smtEngine.setOption("input-language", new SExpr("smt2"));
    smtEngine.setOption("output-language", new SExpr("smt2"));
  }

  @Override
  public String getProviderName() {
    return "cvc4";
  }
}
