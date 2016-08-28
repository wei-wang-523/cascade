package edu.nyu.cascade.reachability;

import com.google.inject.Inject;

import edu.nyu.cascade.c.theory.Theory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class ListReachability implements Theory {
	private final ListReachabilityEncoding encoding;

	@Inject
	public ListReachability(ExpressionManager exprManager) {
		String tpProviderName = exprManager.getTheoremProver().getProviderName();
		if (Preferences.PROVER_Z3.equals(tpProviderName))
			encoding = ListReachabilityEncoding_Z3.create(exprManager);
		else if (Preferences.PROVER_CVC4.equals(tpProviderName))
			encoding = ListReachabilityEncoding_CVC4.create(exprManager);
		else
			throw new IllegalArgumentException(
					"Unknown theorem prover " + tpProviderName);
	}

	@Override
	public ListReachabilityEncoding getEncoding() {
		return encoding;
	}

}
