package edu.nyu.cascade.c.mode;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.formatter.MultiCellLinearFormatter;
import edu.nyu.cascade.ir.formatter.SingleCellLinearFormatter;
import edu.nyu.cascade.ir.formatter.VariCellLinearFormatter;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractMode implements Mode {

	public static Mode getMode(TheoremProver theoremProver) {
		ExpressionManager exprManager = theoremProver.getExpressionManager();

		if (!Preferences.isSet(Preferences.OPTION_MODE)) {
			Mode mode = new PartitionMode(exprManager);
			return mode;
		}

		String modeName = Preferences.getString(Preferences.OPTION_MODE);
		Mode mode;
		if ("Flat".equals(modeName))
			mode = new FlatMode(exprManager);
		else if ("Burstall".equals(modeName))
			mode = new BurstallMode(exprManager);
		else
			mode = new PartitionMode(exprManager);

		return mode;
	}

	IRDataFormatter getFormatter(ExpressionEncoding encoding) {
		if (Preferences.isSet(Preferences.OPTION_MULTI_CELL))
			return MultiCellLinearFormatter.create(encoding);

		if (Preferences.isSet(Preferences.OPTION_VARI_CELL))
			return VariCellLinearFormatter.create(encoding);

		return SingleCellLinearFormatter.create(encoding);
	}

}
