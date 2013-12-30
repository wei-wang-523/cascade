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
//    /*
//     * FIXME: Two use modes for SymbolTable: we care about the input XTC table or
//     * we don't. Is there a straight-forward way to configure Guice to handle both
//     * modes at once? (See also: edu.nyu.cascade.spl.SplModule)
//     */
//    bind(SymbolTableFactory.class).toProvider(
//        FactoryProvider.newFactory(SymbolTableFactory.class,
//            SymbolTableImpl.class));
  	install(new FactoryModuleBuilder().implement(
  			SymbolTable.class, SymbolTableImpl.class).build(SymbolTableFactory.class));
  }
}
