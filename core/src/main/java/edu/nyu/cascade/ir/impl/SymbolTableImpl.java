package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;

public class SymbolTableImpl implements SymbolTable {
	/*
	 * Using the same symbol for scopes let's us reuse XTC implementations (like
	 * CAnalyzer)
	 */
	private static final String SCOPE = xtc.Constants.SCOPE;

	private final xtc.util.SymbolTable xtcSymbolTable;

	@Inject
	public SymbolTableImpl(@Assisted xtc.util.SymbolTable xtcSymbolTable) {
		this.xtcSymbolTable = xtcSymbolTable;
	}

	@Override
	public void createAndEnterScope(String scopeName, Node node) {
		Preconditions.checkArgument(!hasScope(node));
		xtcSymbolTable.enter(scopeName);
		/* Scope property is the qualified name of the scope. */
		node.setProperty(SCOPE, getCurrentScope().getQualifiedName());
	}

	@Override
	public void createScope(String scopeName, Node node) {
		Preconditions.checkArgument(!hasScope(node));
		Scope oldScope = getCurrentScope();
		createAndEnterScope(scopeName, node);
		setScope(oldScope);
	}

	@Override
	public void define(String name, IRVarInfo info) {
		if (isDefined(name)) {
			IOUtils.err().println("Symbol \'" + name + "\' is already defined.");
		}
		getCurrentScope().define(name, info);
	}

	@Override
	public void defineLabel(String name, Object def) {
		String qLabel = toLabelName(name);
		getCurrentScope().define(qLabel, def);
	}

	@Override
	public void enterScope(IRControlFlowGraph cfg) {
		Preconditions.checkArgument(isValidScope(cfg.getScope()));
		setScope(cfg.getScope());
	}

	@Override
	public void enterScope(Node node) {
		Preconditions.checkArgument(hasScope(node));
		Preconditions.checkArgument(isValidScope(getScope(node)));
		setScope(getScope(node));
	}

	@Override
	public void format(Printer printer) {
		rootScope().dump(printer);
	}

	@Override
	public Scope getCurrentScope() {
		return xtcSymbolTable.current();
	}

	@Override
	public Scope getScope(Node node) {
		Preconditions.checkArgument(node.hasProperty(SCOPE));
		return (Scope) getScope((String) node.getProperty(SCOPE));
	}

	@Override
	public Scope getScope(String id) {
		return xtcSymbolTable.getScope(id);
	}

	private boolean isValidScope(Scope scope) {
		return xtcSymbolTable.getScope(scope.getQualifiedName()) != null;
	}

	@Override
	public boolean hasScope(Node node) {
		return node.hasProperty(SCOPE);
	}

	@Override
	public void mark(Node node) {
		xtcSymbolTable.mark(node);
	}

	@Override
	public boolean isDefined(String name) {
		return xtcSymbolTable.current().isDefined(name);
	}

	@Override
	public boolean isDefined(String name, String namespace) {
		String qName = namespace != null
				? xtc.util.SymbolTable.toNameSpace(name, namespace) : name;
		return xtcSymbolTable.current().isDefined(qName);
	}

	@Override
	public boolean labelIsDefined(String name) {
		String qLabel = toLabelName(name);
		return isDefined(qLabel);
	}

	@Override
	public IRVarInfo lookup(String name) {
		return (IRVarInfo) xtcSymbolTable.current().lookup(name);
	}

	@Override
	public Scope lookupScope(String name) {
		return getCurrentScope().lookupScope(name);
	}

	@Override
	public String qualify(String parameter) {
		return xtcSymbolTable.current().qualify(parameter);
	}

	@Override
	public Scope rootScope() {
		return xtcSymbolTable.root();
	}

	@Override
	public void setScope(Scope scope) {
		Preconditions.checkArgument(isValidScope(scope));
		xtcSymbolTable.setScope(scope);
	}

	@Override
	public String toLabelName(String name) {
		return xtc.util.SymbolTable.toLabelName(name);
	}

	@Override
	public String toNamespace(String name, String namespace) {
		return xtc.util.SymbolTable.toNameSpace(name, namespace);
	}

	@Override
	public xtc.util.SymbolTable toXtcSymbolTable() {
		return xtcSymbolTable;
	}

	@Override
	public void undefine(String name) {
		getCurrentScope().undefine(name);
	}

	@Override
	public Type lookupType(String name) {
		return (Type) xtcSymbolTable.lookup(name);
	}

	@Override
	public void enter(String name) {
		xtcSymbolTable.enter(name);
	}

	@Override
	public void exit() {
		xtcSymbolTable.exit();
	}

	@Override
	public xtc.util.SymbolTable getOriginalSymbolTable() {
		return xtcSymbolTable;
	}
}
