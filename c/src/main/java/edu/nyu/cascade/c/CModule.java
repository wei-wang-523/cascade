package edu.nyu.cascade.c;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;
//import com.google.inject.assistedinject.FactoryProvider;

import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.SymbolTableFactory;
import edu.nyu.cascade.ir.impl.SymbolTableImpl;

public class CModule extends AbstractModule {
	@Override
	public void configure() {
		install(new FactoryModuleBuilder()
				.implement(SymbolTable.class, SymbolTableImpl.class)
				.build(SymbolTableFactory.class));
	}
}
