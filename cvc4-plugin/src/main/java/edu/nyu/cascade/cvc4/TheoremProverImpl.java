package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.DATATYPES;
import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.SMT;

import java.io.File;
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
      return "cvc4";
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
              OptionBuilder.withLongOpt(OPTION_RESOURCE_LIMIT) //
                  .hasArg() //
                  .withArgName("N") //
                  .withType(Integer.class) //
                  .withDescription("Set CVC4 resource limit to N") //
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
                  .create(), //
              OptionBuilder
                  .withLongOpt(OPTION_CVC4_STATS)
                  .withDescription("Show cvc4 statistics.")
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
  private static final String OPTION_RESOURCE_LIMIT = "cvc4-resource-limit";
  private static final String OPTION_CVC4_STATS = "cvc4-stats";
  private static final String OPTION_QUANT_LIMIT = "cvc4-quant-limit";
  private static final String OPTION_TRACE = "cvc4-trace";
  private static final String OPTION_DEBUG = "cvc4-debug";
  private static final String OPTION_NO_TYPE_CORRECTNESS_CONDITIONS = "cvc4-notcc";

  private static final Pattern p = Pattern.compile("(^|\\n|\\r\\n?)");

  public static void debugCall(String string) {
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "CVC.API> ") + ";").flush();
    }
  }

  public static void debugCall(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCall(String.format(format, objects));
    }
  }

  public static void debugCommand(String string) {
    // p.matcher(string).replaceAll("\1CVC> ");
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "CVC> ") + ";").flush();
    }
  }
  
  public static void tpFileCommand(String string) {
    if(IOUtils.tpFileEnabled()) {
      IOUtils.tpFile().pln(string + ";").flush();
    }
  }

  public static void debugCommand(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCommand(String.format(format, objects));
    }
  }
  
  public static void tpFileCommand(String format, Object... objects) {
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
  
  /* private final FlagsMut flags; */

  /**
   * This constructor is an escape hatch for subclasses to do initialization
   * themselves.
   */
  protected TheoremProverImpl(ExprManager em) throws TheoremProverException {
    /* validityChecker = vc;
    flags = vc.getFlags(); */
    cvc4ExprManager = em;
    smtEngine = new SmtEngine(em);
    exprManager = null;
    assumptions = Lists.newArrayList();
    initializePreferences();
  }

  /**
   * Construct a new CVC4 theorem prover.
   */
  public TheoremProverImpl() {
    /* flags = ValidityChecker.createFlags(null); */

    // flags.setFlag("dag", 0);
    // flags.setFlag("quant-complete-inst",1);

    // Create a validity checker with these flags
    /* validityChecker = null; */
    
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
    /*
     * for (IExpression<IBooleanType> proposition : propositions) { Expr expr =
     * getExpressionManager().toCvc4Expr(proposition); // debugCommand("ASSERT "
     * + expr.toString()); // debugCall("vc.assertFormula(" + expr.toString() +
     * ");"); // cvc4_vc.assertFormula(expr); }
     */
    for( Expression e : propositions ) {
      Preconditions.checkArgument(e.isBoolean());
      assumptions.add(e.asBooleanExpression());
    }
  }

  private void addAssumptions() {
    for (Expression p : assumptions) {
      Expr expr = getExpressionManager().toCvc4Expr(p);
      debugCommand("ASSERT " + expr.toString());
      tpFileCommand("ASSERT " + expr.toString());
      /* debugCall("vc.assertFormula(" + expr.toString() + ");"); */
      /* getCvc4ExprManager().assertFormula(expr); */
      getSmtEngine().assertFormula( expr );
    }
  }
  
  @SuppressWarnings("unchecked")
  @Override
  public SatResult checkSat(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    try {      
      /* getCvc4ExprManager().push(); */
      getSmtEngine().push();

      addAssumptions();

      Expr cvc4Expr = getExpressionManager().toCvc4Expr(expr);
      
      if (IOUtils.debugEnabled()) {        
        IOUtils.debug().pln(
                            "Simplified: "
                                + getSmtEngine().simplify(cvc4Expr)
                                    .toString()).flush();
      }
      
      debugCommand("CHECKSAT " + getSmtEngine().simplify(cvc4Expr).toString());
      tpFileCommand("CHECKSAT " + getSmtEngine().simplify(cvc4Expr).toString());
      
      Result cvc4SatResult = getSmtEngine().checkSat(cvc4Expr);
      IOUtils.debug().pln(cvc4SatResult.toString()).flush();
      SatResult.Type resultType = convertCvc4SatResult(cvc4SatResult);

      SatResult res;
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
        
        try {
          for (Expression e: exprManager.getVariables()) {
            Expr eValue = getSmtEngine().getValue(exprManager.toCvc4Expr(e));
            ctrex.add(e.eq((ExpressionImpl) exprManager.toExpression(eValue)));
          }   
          modelWorked = true;
        } catch (Exception e) {
          IOUtils.err().println("[WARNING] " + e.getMessage());
          // e.printStackTrace(IOUtils.err());
          ctrex.clear();
        }
          
        if (!modelWorked) {
          for (Expression e : exprManager.getVariables()) {
            ctrex.add(e.asBooleanExpression());
          }
        }
        res = SatResult.valueOf(resultType, expr, assumptions, ctrex);
      } else { // resultType = UNKNOWN
        res = SatResult.valueOf(resultType, expr, assumptions, 
            cvc4SatResult.whyUnknown().toString()); 
      }

      if (Preferences.isSet(OPTION_CVC4_STATS)) {
        getSmtEngine().getStatistics().flushInformation(IOUtils.out());
      }
          
      /* getCvc4ExprManager().pop(); */
      getSmtEngine().pop();

      return res;
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ValidityResult<?> checkValidity(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    try {
      
      /* getCvc4ExprManager().push(); */
      getSmtEngine().push();

      addAssumptions();

      final ExpressionManagerImpl exprManager = getExpressionManager();
      Expr cvc4Expr = exprManager.toCvc4Expr(expr);
      
      if (IOUtils.debugEnabled()) {  
        IOUtils.debug().pln(
                            "Simplified: "
                                + getSmtEngine().simplify(cvc4Expr)
                                    .toString()).flush();
      }
      
//      debugCommand("QUERY " + getSmtEngine().simplify(cvc4Expr).toString());
//      tpFileCommand("QUERY " + getSmtEngine().simplify(cvc4Expr).toString());
      
//      IOUtils.out().println(ManagementFactory.getRuntimeMXBean().getName());
      Result cvc4QueryResult = getSmtEngine().query(cvc4Expr);
      IOUtils.debug().pln(cvc4QueryResult.toString());
      ValidityResult.Type resultType = convertCvc4QueryResult(cvc4QueryResult);

      ValidityResult res;
      if (ValidityResult.Type.VALID.equals(resultType)) {
        res = ValidityResult.valid(expr);
      } else if (ValidityResult.Type.INVALID.equals(resultType)){        
        /**
         * In theory, a query that returns INVALID instead of UNKNOWN should be
         * able to provide a model. For whatever reason, this sometimes fails,
         * so we catch any Exception in the model generation phase and
         * revert to using a counter-example.
         */
        List<BooleanExpression> ctrex = Lists.newLinkedList();
        boolean modelWorked = false;
        
        try {
          for (Expression e: exprManager.getVariables()) {
            Expr eValue = getSmtEngine().getValue(exprManager.toCvc4Expr(e));
            ctrex.add(e.eq((ExpressionImpl) exprManager.toExpression(eValue)));
          }   
          modelWorked = true;
        } catch (Exception e) {
          IOUtils.err().println("[WARNING] " + e.getMessage());
          // e.printStackTrace(IOUtils.err());
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

      if (Preferences.isSet(OPTION_CVC4_STATS)) {
        getSmtEngine().getStatistics().flushInformation(IOUtils.out());
      }
      
      /*  getCvc4ExprManager().pop();*/
      getSmtEngine().pop();

      return res;
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public void clearAssumptions() {
    try {
      assumptions.clear();
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
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
      System.loadLibrary("cvc4java");

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
  protected SmtEngine getSmtEngine() {
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
  
  public void enableCvc4Stats() {
    try {
      getSmtEngine().setOption("statistics", new SExpr("true"));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableCvc4Trace(String s) {
    try {
      getSmtEngine().setOption("trace", new SExpr(s));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableCvc4Debug(String s) {
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
      if (Preferences.isSet(OPTION_RESOURCE_LIMIT)) {
        setResourceLimit(Preferences.getInt(OPTION_RESOURCE_LIMIT));
      }
      
      if (Preferences.isSet(OPTION_CVC4_STATS)) {
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
    
      /** FIXME: other preferences are not supported in CVC4 */
      
      /** 
       * Some of these preferences (e.g., DUMP_LOG) must be set
       * before the ValidityChecker is created. Hence, setPreferences
       * *must* be called before that happens... 
       */
      
/*      if (Preferences.isSet(OPTION_DUMP_LOG)) {
        setLogFile(Preferences.getFile(OPTION_DUMP_LOG));
      }
      if (Preferences.isSet(OPTION_DUMP_TRACE)) {
        flags.setFlag(FLAG_DUMP_TRACE,Preferences.getFile(OPTION_DUMP_TRACE).getAbsolutePath());
      }
     if (Preferences.isSet(OPTION_QUANT_LIMIT)) {
        setQuantifierLimit(Preferences.getInt(OPTION_QUANT_LIMIT));
      }
      if (!Preferences.isSet(OPTION_NO_TYPE_CORRECTNESS_CONDITIONS)) {
        flags.setFlag(FLAG_TYPE_CORRECTNESS_CONDITIONS,true);
        new SExpr();
      }
*/
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  /** 
   * FIXME: Flags are not supported in cvc4
   */
  public void setLogFile(File logFile) {
    /* flags.setFlag(FLAG_DUMP_LOG, logFile.getAbsolutePath()); */
    throw new UnsupportedOperationException("Not supported flag in CVC4.");
  } 

  public void setQuantifierLimit(int limit) {
    /* flags.setFlag(FLAG_QUANT_MAX_INST_LEVEL, limit); */
    throw new UnsupportedOperationException("Not supported flag in CVC4.");
  }

  public void setResourceLimit(int limit) {
    getSmtEngine().setResourceLimit(limit);
  }

  ImmutableList<Option> getOptions() {
    return new Provider().getOptions();
  }
  
  private void initializePreferences() {
    // always incremental and model-producing in cascade mode
    // also incrementally-simplifying and interactive
    smtEngine.setOption("incremental", new SExpr("true"));
    smtEngine.setOption("produce-models", new SExpr("true"));
    smtEngine.setOption("simplification-mode", new SExpr("incremental"));
    smtEngine.setOption("interactive-mode", new SExpr("true")); // support SmtEngine::getAssertions()
    smtEngine.setOption("produce-assignments", new SExpr("true"));
    smtEngine.setOption("statistics", new SExpr("false"));
    smtEngine.setOption("random-seed", new SExpr("91648253"));
    smtEngine.setOption("parse-only", new SExpr("false"));
    smtEngine.setOption("input-language", new SExpr("presentation"));
    smtEngine.setOption("output-language", new SExpr("cvc4"));
  }

  @Override
  public String getProviderName() {
    return "cvc4";
  }
}
