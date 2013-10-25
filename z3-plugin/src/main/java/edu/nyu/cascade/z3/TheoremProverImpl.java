package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.DATATYPES;
import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.SMT;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.regex.Pattern;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Expr;

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
 * Implements the theorem prover interface using the z3 implementation.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 * @author <a href="mailto:wwang1109@cs.nyu.edu">Wei Wang</a>
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
      return "z3";
    }

    @SuppressWarnings("static-access")
    @Override
    public ImmutableList<Option> getOptions() {
      return ImmutableList
          .of(OptionBuilder.withLongOpt(OPTION_DUMP_LOG) //
              .hasArg() //
              .withArgName("FILE") //
              .withType(File.class) //
              .withDescription("Dump Z3 activity to log FILE") //
              .create(), //
              OptionBuilder.withLongOpt(OPTION_PBQI) //
              .withDescription("Enable Z3 pattern based quantifier instantiation") //
              .create(), //
              OptionBuilder.withLongOpt(OPTION_MBQI) //
              .withDescription("Enable Z3 model based quantifier instantiation") //
              .create(), //
              OptionBuilder
              .withLongOpt(OPTION_TP_STATS)
              .withDescription("Show z3 statistics.")
              .create());

    }

  }

  private static final String OPTION_DUMP_LOG = "z3-log";
  private static final String OPTION_TP_STATS = "z3-stats";
  private static final String OPTION_PBQI = "z3-pbqi";
  private static final String OPTION_MBQI = "z3-mbqi";
  private static long z3_time = 0;
  private static final Pattern p = Pattern.compile("(^|\\n|\\r\\n?)");

  public static void debugCall(String string) {
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "Z3.API> ") + ";").flush();
    }
  }

  public static void debugCall(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCall(String.format(format, objects));
    }
  }

  public static void debugCommand(String string) {
    if (IOUtils.debugEnabled()) {
      IOUtils.debug().pln(prefixLinesWith(string, "Z3> ") + ";").flush();
    }
  }
  
  public static void z3FileCommand(String string) {
    if(IOUtils.tpFileEnabled()) {
      IOUtils.tpFile().pln(string).flush();
    }
  }

  public static void debugCommand(String format, Object... objects) {
    if (IOUtils.debugEnabled()) {
      debugCommand(String.format(format, objects));
    }
  }
  
  public static void z3FileCommand(String format, Object... objects) {
    if (IOUtils.tpFileEnabled()) {
      z3FileCommand(String.format(format, objects));
    }
  }

  private static String prefixLinesWith(String str, String prefix) {
    return p.matcher(str).replaceAll("$1" + prefix);
  }

  /* private ValidityChecker validityChecker; */
  
  /**
   * The z3 copy we will be using.
   */
  private Context z3Context;
  
  /**
   * The z3 settings.
   */
  private HashMap<String, String> settings;
  
  /**
   * The smt engine we will be using
   */
  private Solver solver;

  /**
   * The expression manager of this z3 instance
   */
  private ExpressionManagerImpl exprManager;

  /** A list of asserted expressions. */
  private final List<BooleanExpression> assumptions;
  
  /* private final FlagsMut flags; */

  /**
   * This constructor is an escape hatch for subclasses to do initialization
   * themselves.
   * @throws Z3Exception
   */
  protected TheoremProverImpl(HashMap<String, String> cfg) 
      throws TheoremProverException, Z3Exception {
    settings = cfg;
    initializePreferences(settings);
    z3Context = new Context(settings);
    solver = z3Context.MkSolver();
    exprManager = null;
    assumptions = Lists.newArrayList();
  }

  /**
   * Construct a new Z3 theorem prover.
   */
  public TheoremProverImpl() {    
    // Create the z3 expression manager
    z3Context = null;
    
    // Create the settings
    settings = null;
    
    // Create the smt engine
    solver = null;

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
      assumptions.add(e.asBooleanExpression());
    }
  }

  private void addAssumptions() throws Z3Exception {
    for (Expression p : assumptions) {
      Expr expr = getExpressionManager().toZ3Expr(p);
      debugCommand("(assert " + expr.toString() + ")");
      z3FileCommand("(assert " + expr.toString() + ")");
      getSolver().Assert((BoolExpr) expr);
    }
  }
  
  @SuppressWarnings("unchecked")
  @Override
  public SatResult checkSat(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());
    try {
      getSolver().Push();
      z3FileCommand("(push)");
      addAssumptions();

      Expr z3Expr = getExpressionManager().toZ3Expr(expr);
      
      if (IOUtils.debugEnabled()) {        
        IOUtils.debug().pln(
                            "Simplified: "
                                + z3Expr.Simplify()
                                    .toString()).flush();
      }
      
      debugCommand("(assert " + z3Expr.Simplify().toString() + ")");
      z3FileCommand("(assert " + z3Expr.Simplify().toString() + ")");
      getSolver().Assert((BoolExpr) z3Expr);

      debugCommand("(check-sat)");
      z3FileCommand("(check-sat)");      
      Status z3SatResult = getSolver().Check();
      IOUtils.debug().pln(z3SatResult.toString()).flush();
      SatResult.Type resultType = convertZ3SatResult(z3SatResult);

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
        res = SatResult.valueOf(resultType, expr, assumptions, getSolver().Model().toString());
      } else { // resultType = UNKNOWN
        res = SatResult.valueOf(resultType, expr, assumptions, getSolver().ReasonUnknown()); 
      }

      if (Preferences.isSet(OPTION_TP_STATS)) {
        IOUtils.out().flush();
        IOUtils.out().println(getSolver().Statistics());
      }
      
      getSolver().Pop();
      z3FileCommand("(pop)");

      return res;
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ValidityResult<?> checkValidity(Expression expr) {
    Preconditions.checkArgument(expr.isBoolean());

    try {
      getSolver().Push();
      z3FileCommand("(push)");
      
      addAssumptions();

      final ExpressionManagerImpl exprManager = getExpressionManager();
      Expr z3Expr = exprManager.toZ3Expr(exprManager.not(expr));
      
      if (IOUtils.debugEnabled()) {        
        IOUtils.debug().pln(
                            "Simplified: "
                                + z3Expr.Simplify()
                                    .toString()).flush();
      }      
//      IOUtils.out().println(ManagementFactory.getRuntimeMXBean().getName());
      
      debugCommand("(assert " + z3Expr.Simplify().toString() + ")");
      z3FileCommand("(assert " + z3Expr.Simplify().toString() + ")");      
      getSolver().Assert((BoolExpr) exprManager.toZ3Expr(exprManager.not(expr)));
      
      debugCommand("(check-sat)");
      z3FileCommand("(check-sat)");
      long time = System.currentTimeMillis();
      Status z3QueryResult = getSolver().Check();
      time = System.currentTimeMillis() - time;
      z3_time += time;
      IOUtils.debug().pln("Z3 took time: " + z3_time/1000.0 + "s");
      IOUtils.debug().pln(z3QueryResult.toString());
      ValidityResult.Type resultType = convertZ3QueryResult(z3QueryResult);

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
        res = ValidityResult.valueOf(resultType, expr, assumptions, getSolver().Model().toString());         
      } else { // resultType = UNKNOWN
        res = ValidityResult.valueOf(resultType, expr, assumptions, getSolver().ReasonUnknown()); 
      }

      if (Preferences.isSet(OPTION_TP_STATS)) {
        IOUtils.out().flush();
        IOUtils.out().println(getSolver().Statistics());
      }
      
      getSolver().Pop();
      z3FileCommand("(pop)");

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

  private ValidityResult.Type convertZ3QueryResult(Status validResult) {
    if(validResult.equals(Status.UNKNOWN)) {
      return ValidityResult.Type.valueOf("UNKNOWN");
    } else if(validResult.equals(Status.UNSATISFIABLE)) {
      return ValidityResult.Type.valueOf("VALID");
    } else {
      return ValidityResult.Type.valueOf("INVALID");
    }
  }

  private SatResult.Type convertZ3SatResult(Status satResult) {
    if(satResult.equals(Status.UNKNOWN)) {
      return SatResult.Type.valueOf("UNKNOWN");
    } else if(satResult.equals(Status.UNSATISFIABLE)) {
      return SatResult.Type.valueOf("UNSAT");
    } else {
      return SatResult.Type.valueOf("SAT");
    }
  }
  
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
  
  /**
   * Returns the z3 expression manager.
   * 
   * @return the expression manager
   * @throws Z3Exception 
   */
  public Context getZ3Context() throws Z3Exception {
    if(z3Context == null) {
      System.loadLibrary("z3java");
      z3Context = new Context();
    }
    return z3Context;
  }
  
  /**
   * Returns the smt Engine.
   * 
   * @return the expression manager
   */
  protected Solver getSolver() {
    if(solver == null) {
      try {
        Context ctx = getZ3Context();
        solver = ctx.MkSolver();
        if(settings != null) {
          Params p = ctx.MkParams();
          for(Entry<String, String> pair : settings.entrySet()) {
            Symbol key = ctx.MkSymbol(pair.getKey());
            Symbol val = ctx.MkSymbol(pair.getValue());
            p.Add(key, val);
          }
          solver.setParameters(p);
        }
      } catch (Z3Exception e) {
        throw new TheoremProverException(e);
      }
    }
    return solver;
  }
  
  protected HashMap<String, String> getSettings() {
    if(settings == null) {
      settings = Maps.newHashMap();
    } 
    return settings;
  }
  

  /**
   * Set an "effort level" for validity and satisfiability queries. In this
   * implementation, the Z3 "resource limit" varies linearly and the
   * quantifier instantiation limit varies logarithmically with the effort
   * level. An effort level of <math>n</math> corresponds to a Z3
   * "resource limit" <math>256n</math> and a maximum quantifier instantiation
   * level of <math>log(n)</code>. A value of 0 means no resource limit and a
   * default maximum quantifier instantiation level.
   */
  
  public void setEffortLevel(int level) {
    try {
      getSettings().put("memory", Long.toString(level << 8));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  /**
   * Set an "time level" for validity and satisfiability queries. In this
   * implementation, the Z3 "time limit" varies with the time
   * level. An time level of <math>n</math> corresponds to a Z3
   * "time limit" <math>256n</math>. A value of 0 means no time limit.
   */

  public void setTimeLimit(int second) {
    try {
      getSettings().put("timeout", Long.toString(second * 1000));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableZ3Stats() {
    try {
      getSettings().put("st", "true");
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableZ3Trace(String s) {
    try {
      getSettings().put("trace", s);
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableZ3Debug(String s) {
    try {
      getSettings().put("debug", s);
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableZ3Pbqi() {
    try{
      getSettings().put("mbqi", "false");
      getSettings().put("auto-config", "false");
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  public void enableZ3Mbqi() {
    try{
      getSettings().put("mbqi", "true");
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }
  
  /**
   * Set implementation-specific properties from {@link Preferences}.
   */
  @Override
  public void setPreferences() {
    try {
      
      if (Preferences.isSet(OPTION_TP_STATS)) {
        enableZ3Stats();
      }
      
      if (Preferences.isSet(OPTION_PBQI)) {
        enableZ3Pbqi();
      }
    
      if (Preferences.isSet(OPTION_MBQI)) {
        enableZ3Mbqi();
      }
      
      /** FIXME: other preferences are not supported in Z3 */
      
      /** 
       * Some of these preferences (e.g., DUMP_LOG) must be set
       * before the ValidityChecker is created. Hence, setPreferences
       * *must* be called before that happens... 
       */
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  /** 
   * FIXME: Flags are not supported in z3
   */
  public void setLogFile(File logFile) {
    /* flags.setFlag(FLAG_DUMP_LOG, logFile.getAbsolutePath()); */
    throw new UnsupportedOperationException("Not supported flag in Z3.");
  } 

  public void setQuantifierLimit(int limit) {
    /* flags.setFlag(FLAG_QUANT_MAX_INST_LEVEL, limit); */
    throw new UnsupportedOperationException("Not supported flag in Z3.");
  }

  ImmutableList<Option> getOptions() {
    return new Provider().getOptions();
  }
  
  private void initializePreferences(HashMap<String, String> cfg) {
    // always incremental and model-producing in cascade mode
    // also incrementally-simplifying and interactive
    cfg.put("model", "true");
    cfg.put("incremental", "true");
  }

  @Override
  public String getProviderName() {
    return "z3";
  }
}
