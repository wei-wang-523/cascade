package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.DATATYPES;
import static edu.nyu.cascade.prover.TheoremProverFactory.Capability.SMT;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentMap;

import org.apache.commons.cli.Option;
import org.apache.commons.lang.time.StopWatch;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.QueryResult;
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

	static final LoadingCache<TheoremProverImpl, ConcurrentMap<Expr, QueryResult<?>>> queryCache = CacheBuilder
			.newBuilder().build(
					new CacheLoader<TheoremProverImpl, ConcurrentMap<Expr, QueryResult<?>>>() {
						public ConcurrentMap<Expr, QueryResult<?>> load(
								TheoremProverImpl thereomProver) {
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
			return Preferences.PROVER_Z3;
		}

		@Override
		public ImmutableList<Option> getOptions() {
			return ImmutableList.of(
					Option.builder().longOpt(OPTION_PBQI) //
							.desc("Enable Z3 pattern based quantifier instantiation") //
							.build(), //
					Option.builder().longOpt(OPTION_MBQI) //
							.desc("Enable Z3 model based quantifier instantiation") //
							.build(), //
					Option.builder().longOpt(OPTION_Z3_STATS).desc("Show z3 statistics.")
							.build());
		}

	}

	private static final String OPTION_Z3_STATS = "z3-stats";
	private static final String OPTION_PBQI = "z3-pbqi";
	private static final String OPTION_MBQI = "z3-mbqi";

	static void z3FileCommand(String prefix, Expr z3Expr, String postfix) {
		if (IOUtils.tpFileEnabled()) {
			PrintStream stream = IOUtils.tpFileStream().append(prefix);
			stream.append(z3Expr.toString());
			stream.append(postfix).append('\n').flush();
		}
	}

	static void z3FileCommand(String prefix, Expr z3Expr, Sort z3Type,
			String postfix) {
		if (IOUtils.tpFileEnabled()) {
			PrintStream stream = IOUtils.tpFileStream().append(prefix);
			stream.append(z3Expr.toString());
			stream.append(" ");
			stream.append(z3Type.toString());
			stream.append(postfix).append('\n').flush();
		}
	}

	static void z3FileCommand(String prefix, Sort z3Type, String postfix) {
		if (IOUtils.tpFileEnabled()) {
			PrintStream stream = IOUtils.tpFileStream().append(prefix);
			stream.append(z3Type.toString());
			stream.append(postfix).append('\n').flush();
		}
	}

	static void z3FileCommand(String string) {
		if (IOUtils.tpFileEnabled()) {
			IOUtils.tpFile().pln(string).flush();
		}
	}

	static void z3FileCommand(String format, Object... objects) {
		if (IOUtils.tpFileEnabled()) {
			z3FileCommand(String.format(format, objects));
		}
	}

	/* private ValidityChecker validityChecker; */

	/**
	 * The z3 copy we will be using.
	 */
	private Context z3Context;

	/** The z3 settings. */
	private Map<String, String> settings;

	/** The smt engine we will be using */
	private Solver solver;

	/** The expression manager of this z3 instance */
	private ExpressionManagerImpl exprManager;

	/** A list of asserted expressions. */
	private List<BooleanExpression> assumptions = Lists.newArrayList();

	/** A timer to record solver's total time taken */
	private StopWatch timer = new StopWatch();

	/**
	 * Construct a new Z3 theorem prover.
	 */
	TheoremProverImpl() {
	}

	/**
	 * This constructor is an escape hatch for subclasses to do initialization
	 * themselves.
	 * 
	 * @throws Z3Exception
	 */
	TheoremProverImpl(HashMap<String, String> cfg)
			throws TheoremProverException, Z3Exception {
		settings = cfg;
		initializePreferences(settings);
		z3Context = new Context();
		solver = z3Context.mkSolver();
	}

	@Override
	public void assume(Expression first, Expression... rest) {
		assume(Lists.asList(first, rest));
	}

	@Override
	public void assume(Iterable<? extends Expression> propositions) {
		for (Expression prop : propositions) {
			Preconditions.checkArgument(prop.isBoolean());
			assumptions.add(prop.asBooleanExpression());
		}
	}

	@Override
	public SatResult<?> checkSat(Expression expr) {
		Preconditions.checkArgument(expr.isBoolean());

		Expr z3Expr = exprManager.toZ3Expr(expr);

		try {
			if (queryCache.get(this).containsKey(z3Expr))
				return (SatResult<?>) queryCache.get(this).get(z3Expr);

			getSolver().push();
			z3FileCommand("(push)");

			for (BooleanExpression assumption : assumptions) {
				Expr assump = exprManager.toZ3Expr(assumption);
				z3FileCommand("(assert ", assump, ")");
				getSolver().add((BoolExpr) assump);
			}

			if (IOUtils.debugEnabled()) {
				IOUtils.debug().pln("Simplified: " + z3Expr.simplify()).flush();
			}

			z3FileCommand("(assert ", z3Expr, ")");
			getSolver().add((BoolExpr) z3Expr);
			z3FileCommand("(check-sat)");

			timerStart();
			Status z3SatResult = getSolver().check();
			timerSuspend();

			IOUtils.debug().pln(z3SatResult.toString()).flush();
			SatResult.Type resultType = convertZ3SatResult(z3SatResult);

			SatResult<?> res;
			if (SatResult.Type.UNSAT.equals(resultType)) {
				res = SatResult.unsat(expr);
			} else if (SatResult.Type.SAT.equals(resultType)) {
				/**
				 * In theory, a query that returns INVALID instead of UNKNOWN should be
				 * able to provide a model. For whatever reason, this sometimes fails,
				 * so we catch any Exception in the model generation phase and revert to
				 * using a counter-example.
				 */
				res = SatResult.valueOf(resultType, expr, assumptions,
						getSolver().getModel().toString());
			} else { // resultType = UNKNOWN
				res = SatResult.valueOf(resultType, expr, assumptions,
						getSolver().getReasonUnknown());
			}

			if (Preferences.isSet(OPTION_Z3_STATS)) {
				IOUtils.out().flush();
				IOUtils.out().println(getSolver().getStatistics());
			}

			getSolver().pop();
			z3FileCommand("(pop)");

			queryCache.get(this).put(z3Expr, res);
			return res;

		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public ValidityResult<?> checkValidity(Expression expr) {
		Preconditions.checkArgument(expr.isBoolean());

		Expr z3Expr = exprManager.toZ3Expr(exprManager.not(expr));

		try {
			if (queryCache.get(this).containsKey(z3Expr))
				return (ValidityResult<?>) queryCache.get(this).get(z3Expr);

			getSolver().push();
			z3FileCommand("(push)");

			for (BooleanExpression assumption : assumptions) {
				Expr assump = exprManager.toZ3Expr(assumption);
				z3FileCommand("(assert ", assump, ")");
				getSolver().add((BoolExpr) assump);
			}

			if (IOUtils.debugEnabled()) {
				IOUtils.debug().pln("Simplified: " + z3Expr.simplify()).flush();
			}

			z3FileCommand("(assert ", z3Expr, ")");
			getSolver().add((BoolExpr) z3Expr);
			z3FileCommand("(check-sat)");

			timerStart();
			Status z3QueryResult = getSolver().check();
			timerSuspend();

			IOUtils.debug().pln(z3QueryResult.toString());
			ValidityResult.Type resultType = convertZ3QueryResult(z3QueryResult);

			ValidityResult<?> res;
			if (ValidityResult.Type.VALID.equals(resultType)) {
				res = ValidityResult.valid(expr);
			} else if (ValidityResult.Type.INVALID.equals(resultType)) {
				/**
				 * In theory, a query that returns INVALID instead of UNKNOWN should be
				 * able to provide a model. For whatever reason, this sometimes fails,
				 * so we catch any Exception in the model generation phase and revert to
				 * using a counter-example.
				 */
				res = ValidityResult.valueOf(resultType, expr, assumptions);
			} else { // resultType = UNKNOWN
				res = ValidityResult.valueOf(resultType, expr, assumptions,
						getSolver().getReasonUnknown());
			}

			if (Preferences.isSet(OPTION_Z3_STATS)) {
				IOUtils.out().flush();
				IOUtils.out().println(getSolver().getStatistics());
			}

			getSolver().pop();
			z3FileCommand("(pop)");

			queryCache.get(this).put(z3Expr, res);
			return res;
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public void clearAssumptions() {
		assumptions.clear();
	}

	@Override
	public Expression evaluate(Expression expr) {
		try {
			Expr z3Expr = exprManager.toZ3Expr(expr);
			Expr evalZ3Expr = getSolver().getModel().evaluate(z3Expr, true);
			return exprManager.toExpression(evalZ3Expr);
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	/**
	 * Returns the cascade expression manager.
	 */
	public ExpressionManagerImpl getExpressionManager() {
		if (exprManager == null) {
			exprManager = new ExpressionManagerImpl(this);
		}
		return exprManager;
	}

	/**
	 * Set implementation-specific properties from {@link Preferences}.
	 */
	@Override
	public void setPreferences() {
		try {
			if (Preferences.isSet(OPTION_PBQI)) {
				enableZ3Pbqi();
			}

			if (Preferences.isSet(OPTION_MBQI)) {
				enableZ3Mbqi();
			}
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public String getProviderName() {
		return "z3";
	}

	@Override
	public long getStatsTime() {
		return timer.getTime();
	}

	@Override
	public void reset() {
		try {
			getSolver().reset();
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	/**
	 * Returns the z3 expression manager.
	 * 
	 * @return the expression manager
	 * @throws Z3Exception
	 */
	Context getZ3Context() throws Z3Exception {
		if (z3Context == null) {
			System.loadLibrary("z3java");
			z3Context = new Context();
		}
		return z3Context;
	}

	ImmutableList<Option> getOptions() {
		return new Provider().getOptions();
	}

	private ValidityResult.Type convertZ3QueryResult(Status validResult) {
		if (validResult.equals(Status.UNKNOWN)) {
			return ValidityResult.Type.valueOf("UNKNOWN");
		} else if (validResult.equals(Status.UNSATISFIABLE)) {
			return ValidityResult.Type.valueOf("VALID");
		} else {
			return ValidityResult.Type.valueOf("INVALID");
		}
	}

	private SatResult.Type convertZ3SatResult(Status satResult) {
		if (satResult.equals(Status.UNKNOWN)) {
			return SatResult.Type.valueOf("UNKNOWN");
		} else if (satResult.equals(Status.UNSATISFIABLE)) {
			return SatResult.Type.valueOf("UNSAT");
		} else {
			return SatResult.Type.valueOf("SAT");
		}
	}

	/**
	 * Returns the smt Engine.
	 */
	private Solver getSolver() {
		if (solver != null)
			return solver;

		try {
			Context ctx = getZ3Context();
			solver = ctx.mkSolver();
			if (settings != null) {
				Params p = ctx.mkParams();
				for (Entry<String, String> pair : settings.entrySet()) {
					String key = pair.getKey();
					String value = pair.getValue();
					if (value.matches("-?\\d+(\\.\\d+)?")) { // is number
						int num = Integer.valueOf(value);
						p.add(key, num);
					} else if (value.equals("true") || value.equals("false")) {
						boolean bool = Boolean.valueOf(value);
						p.add(key, bool);
					} else {
						p.add(key, ctx.mkSymbol(value));
					}
				}
				solver.setParameters(p);
			}

			return solver;
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	private Map<String, String> getSettings() {
		if (settings == null) {
			settings = Maps.newHashMap();
		}
		return settings;
	}

	private void enableZ3Pbqi() {
		try {
			getSettings().put("mbqi", "false");
			getSettings().put("auto-config", "false");
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	private void enableZ3Mbqi() {
		try {
			getSettings().put("mbqi", "true");
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	private void initializePreferences(Map<String, String> settings) {
		// always incremental and model-producing in cascade mode
		// also incrementally-simplifying and interactive
		settings.put("model", "true");
		settings.put("incremental", "true");
		settings.put("macro-finder", "true");
	}

	private void timerStart() {
		try {
			timer.start();
		} catch (Exception e) {
			timer.resume();
		}
	}

	private void timerSuspend() {
		timer.suspend();
	}
}