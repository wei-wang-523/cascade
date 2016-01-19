package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.DATATYPES;
import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.SMT;

import java.io.PrintStream;
import java.util.List;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import org.apache.commons.cli.Option;
import org.apache.commons.lang.time.StopWatch;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Integer;
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
	
    private static final LoadingCache<TheoremProverImpl, ConcurrentMap<Expr, ValidityResult<?>>> queryCache = CacheBuilder
	.newBuilder().build(
			    new CacheLoader<TheoremProverImpl, ConcurrentMap<Expr, ValidityResult<?>>>(){
				public ConcurrentMap<Expr, ValidityResult<?>> load(TheoremProverImpl thereomProver) {
				    return new MapMaker().makeMap();
				}
			    });
    
    private static final LoadingCache<TheoremProverImpl, ConcurrentMap<Expr, SatResult<?>>> satCache = CacheBuilder
	.newBuilder().build(
			    new CacheLoader<TheoremProverImpl, ConcurrentMap<Expr, SatResult<?>>>(){
				public ConcurrentMap<Expr, SatResult<?>> load(TheoremProverImpl thereomProver) {
				    return new MapMaker().makeMap();
				}
			    });
    
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
	
	@Override
	    public ImmutableList<Option> getOptions() {
	    return ImmutableList
      		.of(Option.builder()
		    .longOpt(OPTION_CVC4_STATS) //
		    .desc("Enable CVC4 stats") //
		    .build(), //
		    Option.builder()
		    .longOpt(OPTION_CVC4_DECISION) //
		    .desc("Set CVC4 decision") //
		    .hasArg()
		    .argName("S")
		    .type(String.class) //
		    .build(), //
		    Option.builder()
		    .longOpt(OPTION_CVC4_ITE_SIMP) //
		    .desc("Enable CVC4 ite-simp") //
		    .build(), //
		    Option.builder()
		    .longOpt(OPTION_CVC4_NO_ITE_SIMP) //
		    .desc("Enable CVC4 no-ite-simp") //
		    .build() //
		    );
	}
    }
    
    private static final String OPTION_CVC4_STATS = "cvc4-stats";
    private static final String OPTION_CVC4_DECISION = "cvc4-decision";
    private static final String OPTION_CVC4_ITE_SIMP = "cvc4-ite-simp";
    private static final String OPTION_CVC4_NO_ITE_SIMP = "cvc4-no-ite-simp";
    
    static void cvc4FileCommand(String prefix, Expr cvc4Expr, String postfix) {
	if(IOUtils.tpFileEnabled()) {
	    PrintStream stream = IOUtils.tpFileStream().append(prefix);
	    cvc4Expr.toStream(stream);
	    stream.append(postfix).append('\n').flush();
	}
    }
    
    static void cvc4FileCommand(String prefix, Type cvc4Type, String postfix) {
	if(IOUtils.tpFileEnabled()) {
	    PrintStream stream = IOUtils.tpFileStream().append(prefix);
	    cvc4Type.toStream(stream);
	    stream.append(postfix).append('\n').flush();
	}
    }
    
    static void cvc4FileCommand(String prefix, Expr cvc4Expr, Type cvc4Type, String postfix) {
	if(IOUtils.tpFileEnabled()) {
	    PrintStream stream = IOUtils.tpFileStream().append(prefix);
	    cvc4Expr.toStream(stream);
	    stream.append(' ');
	    cvc4Type.toStream(stream);
	    stream.append(postfix).append('\n').flush();
	}
    }
    
    static void cvc4FileCommand(String string) {
	if(IOUtils.tpFileEnabled()) {
	    IOUtils.tpFile().pln(string).flush();
	}
    }
    
    static void cvc4FileCommand(String format, Object... objects) {
	if (IOUtils.tpFileEnabled()) {
	    cvc4FileCommand(String.format(format, objects));
	}
    }
    
    /** The cvc4 copy we will be using. */
    private ExprManager cvc4ExprManager;
    
    /** The smt engine we will be using */
    private SmtEngine smtEngine;
    
    /** The expression manager of this cvc4 instance */
    private ExpressionManagerImpl exprManager;
    
    /** A list of asserted expressions. */
    private final List<BooleanExpression> assumptions = Lists.newArrayList();
    
    /** A timer to record solver's total time taken */
    private final StopWatch timer = new StopWatch();
    
    /**
     * This constructor is an escape hatch for subclasses to do initialization
     * themselves.
   */
    TheoremProverImpl(ExprManager em) throws TheoremProverException {
	cvc4ExprManager = em;
	smtEngine = new SmtEngine(em);
	initializePreferences();
    }
    
    TheoremProverImpl() { }
    
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
    
    @Override
	public SatResult<?> checkSat(Expression expr) {
	Preconditions.checkArgument(expr.isBoolean());
	
	Expr cvc4Expr = exprManager.toCvc4Expr(expr);
	
	try {
	    
	    if(satCache.get(this).containsKey(cvc4Expr))
		return satCache.get(this).get(cvc4Expr);
	    
	    getSmtEngine().push();
	    cvc4FileCommand("(push)");
	    
	    for(BooleanExpression assumption: assumptions) {
		Expr assump = exprManager.toCvc4Expr(assumption);
		cvc4FileCommand("(assert ", assump, ")");
		getSmtEngine().assertFormula( assump );
	    }
	    
	    if (IOUtils.debugEnabled()) {
		Expr cvc4ExprSimp = getSmtEngine().simplify(cvc4Expr);
		IOUtils.debug().pln(
				    "Simplified: "
				    + cvc4ExprSimp).flush();
	    }
	    
	    cvc4FileCommand("(assert ", cvc4Expr, ")");
	    cvc4FileCommand("(check-sat)");
	    
	    timerStart();
	    Result cvc4SatResult = getSmtEngine().checkSat(cvc4Expr);
	    timerSuspend();
	    
	    IOUtils.debug().pln(cvc4SatResult.toString()).flush();
	    SatResult.Type resultType = convertCvc4SatResult(cvc4SatResult);
	    
	    SatResult<?> res;
	    if (SatResult.Type.UNSAT.equals(resultType)) {
		res = SatResult.unsat(expr);
	    } else if (SatResult.Type.SAT.equals(resultType)){
		res = SatResult.valueOf(resultType, expr, assumptions);
	    } else { // resultType = UNKNOWN
		res = SatResult.valueOf(resultType, expr, assumptions, 
					cvc4SatResult.whyUnknown().toString()); 
	    }
	    
	    if (Preferences.isSet(OPTION_CVC4_STATS)) {
		getSmtEngine().getStatistics().flushInformation(IOUtils.out());
	    }
	    
	    if (Preferences.isSet(Preferences.OPTION_TRACE) || res.isSatisfiable())
		return res;
	    
	    getSmtEngine().pop();
	    cvc4FileCommand("(pop)");
	    
	    satCache.get(this).put(cvc4Expr, res);
	    return res;
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	} catch (ExecutionException e) {
	    throw new TheoremProverException(e);
	}
    }
    
    @Override
	public ValidityResult<?> checkValidity(Expression expr) {
	Preconditions.checkArgument(expr.isBoolean());
	Expr cvc4Expr = exprManager.toCvc4Expr(expr);
	
	try {
	    
	    if(queryCache.get(this).containsKey(cvc4Expr))
    		return queryCache.get(this).get(cvc4Expr);
	    
	    getSmtEngine().push();
	    cvc4FileCommand("(push)");
	    
	    for(BooleanExpression assumption: assumptions) {
		Expr assump = exprManager.toCvc4Expr(assumption);
		cvc4FileCommand("(assert ", assump, ")");
		getSmtEngine().assertFormula( assump );
	    }
      
	    if (IOUtils.debugEnabled()) {
		Expr cvc4ExprSimp = getSmtEngine().simplify(cvc4Expr);
		IOUtils.debug().pln(
				    "Simplified: " + cvc4ExprSimp)
		    .flush();
	    }
	    
	    cvc4FileCommand("(assert ", cvc4Expr, ")");
	    cvc4FileCommand("(check-sat)");
	    
	    timerStart();
	    Result cvc4QueryResult = getSmtEngine().query(cvc4Expr);
	    timerSuspend();
      
	    IOUtils.debug().pln(cvc4QueryResult.toString());
	    ValidityResult.Type resultType = convertCvc4QueryResult(cvc4QueryResult);
	    
	    ValidityResult<?> res;
	    if (ValidityResult.Type.VALID.equals(resultType)) {
		res = ValidityResult.valid(expr);
	    } else if (ValidityResult.Type.INVALID.equals(resultType)) {
		res = ValidityResult.valueOf(resultType, expr, assumptions);
	    } else { // resultType = UNKNOWN
		res = ValidityResult.valueOf(resultType, expr, assumptions, 
					     cvc4QueryResult.whyUnknown().toString()); 
	    }
	    
	    if (Preferences.isSet(OPTION_CVC4_STATS)) {
		getSmtEngine().getStatistics().flushInformation(IOUtils.out());
	    }
	    
	    if (Preferences.isSet(Preferences.OPTION_TRACE) || res.isInvalid())
		return res;
	    
	    getSmtEngine().pop();
	    cvc4FileCommand("(pop)");
	    
	    queryCache.get(this).put(cvc4Expr, res);
	    return res;
	} catch (ExecutionException e) {
	    throw new TheoremProverException(e);
	}
    }
    
    @Override
	public void clearAssumptions() {
  	assumptions.clear();
    }
    
    @Override
	public Expression evaluate(Expression expr) {
	Expr cvc4Expr = exprManager.toCvc4Expr(expr);
  	Expr evalCvc4Expr = getSmtEngine().getValue(cvc4Expr);
  	edu.nyu.acsys.CVC4.Kind cvc4Kind = evalCvc4Expr.getKind();
  	if (cvc4Kind == edu.nyu.acsys.CVC4.Kind.CONST_BITVECTOR) {
	    Integer val = evalCvc4Expr.getConstBitVector().getValue();
	    return exprManager.constant(val.getLong());
  	} else if (cvc4Kind == edu.nyu.acsys.CVC4.Kind.CONST_BOOLEAN) {
	    boolean val = evalCvc4Expr.getConstBoolean();
	    return val ? exprManager.tt() : exprManager.ff();
  	} else {
	    return exprManager.toExpression(evalCvc4Expr);
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
    
    /** Set implementation-specific properties from {@link Preferences}. */
    @Override
	public void setPreferences() {
	try {      
	    if (Preferences.isSet(OPTION_CVC4_STATS)) {
		enableCvc4Stats();
	    }
	    
	    if(Preferences.isSet(OPTION_CVC4_DECISION)) {
	    	String param = Preferences.getString(OPTION_CVC4_DECISION);
	    	setCvc4DecisionMode(param);
	    }
	    
	    if(Preferences.isSet(OPTION_CVC4_ITE_SIMP)) {
	    	enableCvc4IteSimp();
	    }
	    
	    if(Preferences.isSet(OPTION_CVC4_NO_ITE_SIMP)) {
	    	enableCvc4NoIteSimp();
	    }
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	}
	}
    
    @Override
	public String getProviderName() {
	return "cvc4";
    }
    
    @Override
	public long getStatsTime() {
	return timer.getTime();
    }
    
    @Override
	public void reset() {
	getSmtEngine().reset();
    }
    
    /**
     * Returns the cvc4 expression manager.
     * 
     * @return the expression manager
     */
    ExprManager getCvc4ExprManager() {
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
    
    ImmutableList<Option> getOptions() {
	return new Provider().getOptions();
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
    
    private void enableCvc4Stats() {
	try {
	    getSmtEngine().setOption("statistics", new SExpr("true"));
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	}
    }
    
    private void enableCvc4IteSimp() {
	try {
	    getSmtEngine().setOption("ite-simp", new SExpr("true"));
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	}
    }
  
    private void enableCvc4NoIteSimp() {
	try {
	    getSmtEngine().setOption("no-ite-simp", new SExpr("true"));
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	}
    }
    
    private void setCvc4DecisionMode(String s) {
	try {
	    getSmtEngine().setOption("decision-mode", new SExpr(s));
	} catch (Exception e) {
	    throw new TheoremProverException(e);
	}
    }
    
    private void initializePreferences() {
	// always incremental and model-producing in cascade mode
	// also incrementally-simplifying and interactive
	smtEngine.setOption("incremental", new SExpr("true"));
	smtEngine.setOption("produce-models", new SExpr("true"));
	smtEngine.setOption("interactive-mode", new SExpr("true")); // support SmtEngine::getAssertions()
	smtEngine.setOption("produce-assignments", new SExpr("true"));
	smtEngine.setOption("statistics", new SExpr("false"));
	smtEngine.setOption("random-seed", new SExpr("91648253"));
	smtEngine.setOption("parse-only", new SExpr("false"));
	smtEngine.setOption("input-language", new SExpr("smt2"));
	smtEngine.setOption("output-language", new SExpr("smt2"));
    }
    
    private void timerStart() {
  	try {
	    timer.start();
  	} catch (java.lang.Exception e) {
	    timer.resume();
  	}
    }
    
    private void timerSuspend() {
  	timer.suspend();
    }
}