package edu.nyu.cascade.c.mode;

import com.google.inject.Inject;

import edu.nyu.cascade.c.pass.alias.typesafe.FSType;
import edu.nyu.cascade.c.pass.alias.typesafe.TypeAnalyzer;
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

public class BurstallMode extends AbstractMode {
	private final ExpressionEncoding encoding;
	private StateFactory<FSType> stateFactory;

	@Inject
	public BurstallMode(ExpressionManager exprManager) {
		encoding = BitVectorExpressionEncoding.create(exprManager);

		Strategy strategy;

		if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
			strategy = Strategy.ORDER;
		} else { // sound alloc
			strategy = Strategy.SOUND;
		}

		IRDataFormatter formatter = getFormatter(encoding);

		if (Preferences.isSet(Preferences.OPTION_LAMBDA)) {
			IRMemSafetyEncoding memSafetyEncoding = Preferences
					.isSet(Preferences.OPTION_STMT)
							? AbstractStmtMemSafetyEncoding.getInstance(encoding, formatter,
									strategy)
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
			stateFactory = HoareStateFactory
					.create((AbstractStateFactory<FSType>) stateFactory);
		}
	}

	@Override
	public ExpressionEncoding getEncoding() {
		return encoding;
	}

	@Override
	public StateFactory<FSType> getStateFactory() {
		return stateFactory;
	}

	@Override
	public boolean hasPreprocessor() {
		return true;
	}

	@Override
	public IRAliasAnalyzer<FSType> buildPreprocessor(SymbolTable symbolTable) {
		IRAliasAnalyzer<FSType> preProcessor = TypeAnalyzer.create();
		stateFactory.setLabelAnalyzer(preProcessor);
		return preProcessor;
	}
}