package edu.nyu.cascade.c.mode;

import com.google.inject.Inject;

import edu.nyu.cascade.c.pass.alias.dsa.DSAAnalysis;
import edu.nyu.cascade.c.pass.alias.steens.Steensgaard;
import edu.nyu.cascade.c.pass.alias.steenscfs.SteensgaardCFS;
import edu.nyu.cascade.c.pass.alias.steenscfscs.SteensgaardCFSCS;
import edu.nyu.cascade.c.pass.alias.steensfs.SteensgaardFS;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.PartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.AbstractStmtMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.Strategy;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.state.AbstractStateFactory;
import edu.nyu.cascade.ir.state.HoareStateFactory;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class PartitionMode extends AbstractMode {
	private final ExpressionEncoding encoding;
	private StateFactory<?> stateFactory;

	@Inject
	public PartitionMode(ExpressionManager exprManager) {
		encoding = BitVectorExpressionEncoding.create(exprManager);

		Strategy strategy;
		if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
			strategy = Strategy.ORDER;
		} else { // sound alloc
			strategy = Strategy.SOUND;
		}

		IRDataFormatter formatter = getFormatter(encoding);

		if (Preferences.isSet(Preferences.OPTION_LAMBDA)) {
			IRMemSafetyEncoding memSafetyEncoding = Preferences.isSet(
					Preferences.OPTION_STMT) ? AbstractStmtMemSafetyEncoding.getInstance(
							encoding, formatter, strategy)
							: AbstractMemSafetyEncoding.getInstance(encoding, formatter,
									strategy);

			stateFactory = AbstractStateFactory.createMultipleLambda(encoding,
					formatter, memSafetyEncoding);

		} else {
			IRPartitionHeapEncoder heapEncoder = PartitionHeapEncoder.create(encoding,
					formatter, strategy);

			stateFactory = AbstractStateFactory.createMultiple(encoding, formatter,
					heapEncoder);
		}

		if (Preferences.isSet(Preferences.OPTION_HOARE)) {
			stateFactory = HoareStateFactory.create(
					(AbstractStateFactory<?>) stateFactory);
		}
	}

	@Override
	public ExpressionEncoding getEncoding() {
		return encoding;
	}

	@Override
	public StateFactory<?> getStateFactory() {
		return stateFactory;
	}

	@Override
	public boolean hasPreprocessor() {
		return true;
	}

	@Override
	public IRAliasAnalyzer<?> buildPreprocessor(SymbolTable symbolTable) {
		IRAliasAnalyzer<?> preProcessor;

		if (Preferences.isSet(Preferences.OPTION_FIELD_SENSITIVE)) {
			preProcessor = SteensgaardFS.create(symbolTable);
		} else if (Preferences.isSet(
				Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE)) {
			preProcessor = SteensgaardCFS.create(symbolTable);
		} else if (Preferences.isSet(
				Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE_CONTEXT_SENSITIVE)) {
			preProcessor = SteensgaardCFSCS.create(symbolTable);
		} else if (Preferences.isSet(Preferences.OPTION_DSA)) {
			preProcessor = DSAAnalysis.create(symbolTable);
		} else {
			preProcessor = Steensgaard.create(symbolTable);
		}

		stateFactory.setLabelAnalyzer(preProcessor);
		return preProcessor;
	}
}
