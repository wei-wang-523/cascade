package edu.nyu.cascade.c.mode;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.formatter.MultiCellLinearFormatter;
import edu.nyu.cascade.ir.formatter.MultiCellSyncFormatter;
import edu.nyu.cascade.ir.formatter.SingleCellLinearFormatter;
import edu.nyu.cascade.ir.formatter.SingleCellSyncFormatter;
import edu.nyu.cascade.ir.formatter.VariCellLinearFormatter;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractMode implements Mode {
	
	public static Mode getMode(ExpressionManager exprManager) {
		if(Preferences.isSet(Preferences.OPTION_MODE)) {
			String mode = Preferences.getString(Preferences.OPTION_MODE);
			if("Flat".equals(mode))
				return new FlatMode(exprManager);
			if("Burstall".equals(mode))
				return new BurstallMode(exprManager);
			if("Partition".equals(mode))
				return new PartitionMode(exprManager);
		}
		
		return new FlatMode(exprManager);
	}

	protected IRDataFormatter getFormatter(ExpressionEncoding encoding) {
		
  	if(Preferences.isSet(Preferences.OPTION_MEM_ENCODING) && 
  			Preferences.MEM_ENCODING_SYNC.equals(
  					Preferences.getString(Preferences.OPTION_MEM_ENCODING))) {
  		
  		assert(!Preferences.isSet(Preferences.OPTION_VARI_CELL));
  		
  		if(Preferences.isSet(Preferences.OPTION_MULTI_CELL))
  			return MultiCellSyncFormatter.create(encoding);
  		
  		return SingleCellSyncFormatter.create(encoding);
  	}
		
  	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
  		assert(!Preferences.isSet(Preferences.OPTION_VARI_CELL));
  		assert(!Preferences.isSet(Preferences.OPTION_MULTI_CELL));
  		
  		return SingleCellLinearFormatter.create(encoding);
  	}
  		
  	if(Preferences.isSet(Preferences.OPTION_MULTI_CELL))
  		return MultiCellLinearFormatter.create(encoding);
  	
  	if(Preferences.isSet(Preferences.OPTION_VARI_CELL))
  			return VariCellLinearFormatter.create(encoding);
  	
  	return SingleCellLinearFormatter.create(encoding);
	}

}
