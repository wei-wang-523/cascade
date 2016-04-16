package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.Constants;
import xtc.tree.GNode;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.type.FunctionT;
import xtc.type.Type;
import xtc.type.Type.Tag;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.impl.BasicBlock;
import edu.nyu.cascade.ir.impl.CaseGuard;
import edu.nyu.cascade.ir.impl.DefaultCaseGuard;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALL;

public class FuncInlineProcessor<T> {
  private final Map<String, IRControlFlowGraph> cfgs;
  private final SymbolTable symbolTable;
  private final IRAliasAnalyzer<T> preprocessor;
  private final int effortLevel;
  private final xtc.type.C cop = CType.getInstance().c();
	
  private FuncInlineProcessor(
      Map<Node, IRControlFlowGraph> cfgs,
      SymbolTable symbolTable,
      IRAliasAnalyzer<T> preprocessor,
      int effortLevel) {
    this.symbolTable = symbolTable;
    this.effortLevel = effortLevel;
    this.preprocessor = preprocessor;
    this.cfgs = Maps.newHashMap();
    for(Entry<Node, IRControlFlowGraph> pair : cfgs.entrySet()) {
    	IRControlFlowGraph CFG = pair.getValue();
    	String funcName = CFG.getName();
    	this.cfgs.put(funcName, CFG);
    }
  }
  
  private FuncInlineProcessor(SymbolTable symbolTable) {
    this.symbolTable = symbolTable;
    this.effortLevel = 0;
    this.preprocessor = null;
    this.cfgs = null;
  }
  
  static <T> FuncInlineProcessor<T> create(
      Map<Node, IRControlFlowGraph> cfgs,
      SymbolTable symbolTable,
      IRAliasAnalyzer<T> preprocessor) {
  	int effortLevel = Integer.MAX_VALUE;
  	if(Preferences.isSet(Preferences.OPTION_FUNC_INLINE))
  		effortLevel = Preferences.getInt(Preferences.OPTION_FUNC_INLINE);
  	return new FuncInlineProcessor<T>(cfgs, symbolTable, preprocessor, effortLevel);
  }
  
  static <T> FuncInlineProcessor<T> create(SymbolTable symbolTable) {
  	return new FuncInlineProcessor<T>(symbolTable);
  }
  
  boolean functionInlineCFG(IRControlFlowGraph cfg) {
  	symbolTable.enterScope(cfg);
  	boolean res = functionInlineCFGWithLevel(cfg, 0);
  	symbolTable.exit();
  	return res;
	}
  
  /**
   * Check if there is any function call within cfg
   * @param cfg
   * @return
   */
	boolean hasFunctionCall(IRControlFlowGraph cfg) {
		for(IRBasicBlock block : cfg.getBlocks()) {
			for(IRStatement stmt : block.getStatements()) {
				if(!CALL.equals(stmt.getType())) continue;
				Node funNode = stmt.getOperand(0).getSourceNode();
				if(isFunctionCall(funNode)) {
					String funcName = CAnalyzer.toFunctionName(funNode);
	  			if(cfgs.containsKey(funcName)) return false;
				} else {
					Collection<IRControlFlowGraph> foundCFGs = lookupFuncCFG(funNode, stmt);
	      	if(!foundCFGs.isEmpty()) return false;
				}
			}
		}
		
		return true;
	}

	/**
	 * Inline functions with malloc statement into caller functions.
	 * @param cfgs
	 * @param callGraph
	 */
	void inlineMalloc(Map<Node, IRControlFlowGraph> cfgs, 
			FunctionCallGraph callGraph) {
		if(!Preferences.isSet(Preferences.OPTION_INLINE_MALLOC)) return;
		Collection<String> currCfgNames = getFuncNames(cfgs.values());
		List<String> worklist = Lists.newArrayList(ReservedFunction.MALLOC);
		while(!worklist.isEmpty()) {
	  	final String callee = worklist.remove(0);
			Collection<String> callers = Sets.newHashSet(callGraph.getCallers(callee));
			callers.retainAll(currCfgNames);
			if(callers.isEmpty()) continue;
			
			int callersSize = callers.size();
			if(callersSize == 1) worklist.addAll(callers);
			
			// Skip inlining ReservedFunction.MALLOC
			if(ReservedFunction.MALLOC.equals(callee)) continue;
			
  		IRControlFlowGraph calleeCfg = getCfg(cfgs, callee);
			for(String caller : callers) {
	  		IRControlFlowGraph callerCfg = getCfg(cfgs, caller);
	  		functionInlineCFG(callerCfg, calleeCfg);
	  		callGraph.removeCallerEdge(caller, callee);
			}
		}
		
		// Cannot cleanup currCfgs with function pointers
	}

	private boolean functionInlineCFGWithLevel(IRControlFlowGraph cfg, int level) {
		if(level >= effortLevel) return false;
		
		Iterable<? extends IRBasicBlock> funcCallBlocks = pickFuncCallBlocks(cfg);
		if(Iterables.isEmpty(funcCallBlocks)) return false;
		 
		Scope preScope = symbolTable.getCurrentScope();
		symbolTable.enterScope(cfg);
	  /* Function in-line for each path with function call */
		boolean changed = false;
	  for(IRBasicBlock funcBlock : ImmutableList.copyOf(funcCallBlocks))
	    changed |= functionInlineBlock(cfg, funcBlock, level);
	  
	  symbolTable.setScope(preScope);
	  return changed;
	}
  
  private IRControlFlowGraph getCfg(Map<Node, IRControlFlowGraph> currCfgs, final String name) {
    return Iterables.find(currCfgs.values(), 
    		new Predicate<IRControlFlowGraph>(){
    	@Override
    	public boolean apply(IRControlFlowGraph cfg) {
    		return cfg.getName().equals(name);
    	}
    });
  }
	
	private void functionInlineCFG(IRControlFlowGraph callerCfg, IRControlFlowGraph calleeCfg) {
		String funcName = calleeCfg.getName();
		Iterable<? extends IRBasicBlock> funcCallBlocks = pickFuncCallBlocks(callerCfg, funcName);
		Scope preScope = symbolTable.getCurrentScope();
		symbolTable.enterScope(callerCfg);
	  /* Function in-line for each path with function call */
	  for(IRBasicBlock funcBlock : ImmutableList.copyOf(funcCallBlocks))
	    functionInlineBlockWithFuncCFG(callerCfg, funcBlock, calleeCfg);
	  
	  callerCfg.format(IOUtils.debug());
	  symbolTable.setScope(preScope);
	}

	/** Pick function paths from <code>graph</code> */
	private Iterable<? extends IRBasicBlock> pickFuncCallBlocks(IRControlFlowGraph cfg) {
		return Iterables.filter(cfg.getBlocks(),
				new Predicate<IRBasicBlock>(){
			@Override
			public boolean apply(IRBasicBlock block) {
				return Iterables.any(block.getStatements(), new Predicate<IRStatement>(){
					@Override
					public boolean apply(IRStatement stmt) {
				    return CALL.equals(stmt.getType());
					}
				});			
			}
		});
	}
	
	/** Pick function paths from <code>graph</code> */
	private Iterable<? extends IRBasicBlock> pickFuncCallBlocks(
			IRControlFlowGraph cfg, final String funcName) {
		return Iterables.filter(cfg.getBlocks(),
				new Predicate<IRBasicBlock>(){
			@Override
			public boolean apply(IRBasicBlock block) {
				return Iterables.any(block.getStatements(), new Predicate<IRStatement>(){
					@Override
					public boolean apply(IRStatement stmt) {
				    if(!CALL.equals(stmt.getType())) return false;
				    IRExpression funExpr = stmt.getOperand(0);
				    Node funNode = funExpr.getSourceNode();
				    String funName = CAnalyzer.toFunctionName(funNode);
				    return funName.equals(funcName);
					}
				});			
			}
		});
	}
	
	/**
	 * Check if <code>funcNode</code> is function call not
	 * function pointer call
	 * @param funcNode
	 * @return
	 */
	private boolean isFunctionCall(Node funcNode) {
		String funcName = CAnalyzer.toFunctionName(funcNode);
		
		/* Cannot pick funcName from funcNode, since funcNode
		 * is at least not PrimaryIdentifier, thus not function
		 * global-defined
		 */
		if(null == funcName) return false;
		
		if(ReservedFunction.isReserved(funcName)) return true;
		
		if(!symbolTable.isDefined(funcName)) return false;
		
		xtc.type.Type type = symbolTable.lookupType(funcName);
		if(!type.resolve().isFunction()) return false;
		
		return true;
	}
  
	/**
   * Get the argument passing statements of function call nested
   * in the statement <code>stmt</code>
   * 
   * @return empty list if the function is not defined or 
   * without parameters
   */
	private Collection<IRStatement> assignArgToParam(IRStatement stmt,
			IRControlFlowGraph funcCFG, FunctionT funcType) {
		Preconditions.checkArgument(CALL.equals(stmt.getType()));
    
		Node defNode = funcCFG.getSourceNode();
    
		/* Find the parameter declare node */
		GNode declarator = defNode.getGeneric(2);
		GNode paramDeclare = CAnalyzer.getFunctionDeclarator(declarator).getGeneric(1);
		if( paramDeclare != null ) {
			paramDeclare = paramDeclare.getGeneric(0);
		}
		
		if(paramDeclare == null)    return Collections.emptyList();
		
		/* Pick all arguments */
		int operandSize = stmt.getOperands().size();
		List<IRExpression> args;
    
		if(funcType.getResult().isVoid()) {
			args = stmt.getOperands().subList(1, operandSize);
		} else {
			args = stmt.getOperands().subList(2, operandSize);
		}
		
	    /* Generate assign statement one by one */
    	int paramSize = funcType.getParameters().size();
    	
        Collection<IRStatement> assignments = Lists.newArrayListWithExpectedSize(paramSize);
      	
        for(int i = 0; i < paramSize; i++) {
        	Node paramNode = paramDeclare.getNode(i).getNode(1);
        	Node idNode = CAnalyzer.getDeclaredId(GNode.cast(paramNode));
        	GNode primaryId = GNode.create("PrimaryIdentifier", idNode.get(0));
        	Type paramType = CType.getType(idNode);
        	paramType.mark(primaryId); symbolTable.mark(primaryId);
          
        	IRExpressionImpl param = CExpression.create(primaryId, symbolTable.getCurrentScope());
        	IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
        	Node argNode = arg.getSourceNode();
        	Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
        	assignNode.setLocation(paramNode.getLocation());
        	Statement assignStmt = Statement.assign(assignNode, param, arg);
        	assignments.add(assignStmt);
        }
    
        if(funcType.isVarArgs()) {
        	int argSize = args.size();
        	assert (argSize >= paramSize);
    	
        	for(int i = argSize; i < paramSize; i++) {
        		GNode offsetNode = GNode.create("IntegerConstant", String.valueOf(argSize - i));
        		cop.typeInteger(String.valueOf(i)).mark(offsetNode); symbolTable.mark(offsetNode);
    		
        		Node varArgN = getVarArgNode(funcCFG.getName(), declarator.getLocation());
        		Type varArgTy = CType.getType(varArgN).resolve().toArray().getType();
        		GNode varArgElem = GNode.create("SubscriptExpression", varArgN, offsetNode);
        		varArgElem.setLocation(declarator.getLocation());
        		varArgTy.mark(varArgElem); symbolTable.mark(varArgElem);
        		preprocessor.analyzeVarArg(funcCFG.getName(), funcType, varArgElem);
    		
        		IRExpressionImpl param = CExpression.create(varArgElem, symbolTable.getCurrentScope());
        		IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
        		Node argNode = arg.getSourceNode();
    		
        		Node assignNode = GNode.create("AssignmentExpression", varArgElem, "=", argNode);
        		assignNode.setLocation(varArgElem.getLocation());
        		Statement assignStmt = Statement.assign(assignNode, param, arg);
        		
        		assignments.add(assignStmt);
        	}
        }
        
        return assignments; 
	}
  
  /**
   * Build function in-line graph for call statement of function call 
   * <code>stmt</code>
   * 0) function enter statement
   * 1) arguments passing 
	 * 2) function body
	 * 3) function return statement
   */
  private void inlineFuncCallGraph(IRControlFlowGraph funcCFG, IRStatement stmt) {
    Preconditions.checkArgument(CALL.equals(stmt.getType()));
    Scope preScope = symbolTable.getCurrentScope();
    symbolTable.enterScope(funcCFG);
    
    GNode declarator = funcCFG.getSourceNode().getGeneric(2);
		GNode identifier = CAnalyzer.getDeclaredId(declarator);
  	FunctionT funcType = symbolTable.lookupType(identifier.getString(0)).resolve().toFunction();
    
    if(!funcType.getParameters().isEmpty()) {
      /* Insert parameter-argument pass statements */
      Collection<IRStatement> paramPassStmts = assignArgToParam(stmt, funcCFG, funcType);
      CfgProcessor.insertParamArgAssignStmts(funcCFG, paramPassStmts);
    }
    
    /* Append assign statement to all the return statements. */
    if(!funcType.getResult().isVoid())
    	CfgProcessor.appendReturnStmt(funcCFG, stmt);
    
    symbolTable.setScope(preScope);
  }

  /**
   * Function inline for every the function call statement in <code>funcCallBlock</code>
   * into <code>CFG</code>, while <code>level</code> used to process function inline for 
   * the function call statements in the function CFG recursively.
   * 
   * @param CFG
   * @param funcCallBlock
   * @param level
   * 
   * @return if the CFG has been inlined any function CFG
   */
  private boolean functionInlineBlock(IRControlFlowGraph CFG, IRBasicBlock funcCallBlock, int level) {
  	boolean changed = false;
  	
  	IRBasicBlock currBlock = funcCallBlock;
  	
  	do {
  		int index = Iterables.indexOf(currBlock.getStatements(), new Predicate<IRStatement>() {
				@Override
        public boolean apply(IRStatement stmt) {
					return CALL.equals(stmt.getType());
        }
  		});
  		if(index == -1) break; // no such element;
  		
  		/* First statement in nextBlock is funcCall statement, currBlock is clean */
  		IRBasicBlock nextBlock = currBlock.splitAt(index);
  		
  		/* Isolate funcCall statement in nextBlock, restBlock contains the following statements */
  		IRBasicBlock restBlock = nextBlock.splitAt(1);
  		
  		IRBasicBlock newSuccCurrBlock; // The successor of the current block
  		
  		IRStatement funcCallStmt = nextBlock.getStatements().get(0);
  		Node funNode = funcCallStmt.getOperand(0).getSourceNode();
  		if(isFunctionCall(funNode)) {
  			String funcName = CAnalyzer.toFunctionName(funNode);
  			if(cfgs.containsKey(funcName)) {
  				changed = true;
  				
    			IRControlFlowGraph funcCFG = cfgs.get(funcName);
          IRControlFlowGraph funcCFGCopy = funcCFG.clone();
      		inlineFuncCallGraph(funcCFGCopy, funcCallStmt);
      		functionInlineCFGWithLevel(funcCFGCopy, level+1);
      		
    			newSuccCurrBlock = funcCFGCopy.getEntry();
    			
    			/* Merge funcCallCFG into cfg */
    			for(IREdge<? extends IRBasicBlock> edge : funcCFGCopy.getEdges()) 
    				CFG.addEdge(edge);
      	  
    			if(funcCFGCopy.getExit() != null)
    				CFG.addEdge(funcCFGCopy.getExit(), restBlock);
  			} else {
        	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
        	newSuccCurrBlock = nextBlock;
    			CFG.addEdge(nextBlock, restBlock);
  			}
  		} else { // function pointers call
      	newSuccCurrBlock = BasicBlock.switchBlock(funcCallStmt.getSourceNode().getLocation());
      	Collection<IRControlFlowGraph> funcCFGs = Lists.newArrayList();
      	Collection<IRControlFlowGraph> foundCFGs = lookupFuncCFG(funNode, funcCallStmt);
      	if(!foundCFGs.isEmpty()) {
      		changed = true;
      		
        	for(IRControlFlowGraph funcCFG : foundCFGs) {
        		IRControlFlowGraph funcCFGCopy = funcCFG.clone();
        		inlineFuncCallGraph(funcCFGCopy, funcCallStmt);
        		functionInlineCFGWithLevel(funcCFGCopy, level+1);
        		funcCFGs.add(funcCFGCopy);
        	}
        	
        	Collection<CaseGuard> caseGuards = Lists.newArrayList();
        	CExpression valExpr = CExpression.create(funNode, currBlock.getScope());
        	for(IRControlFlowGraph funcCFGCopy : funcCFGs) {
        		CaseGuard caseBranch = getCaseGuard(funcCFGCopy, valExpr);
        		caseGuards.add(caseBranch);
        		
        		/* Merge funcCallCFG into cfg */
        		for(IREdge<? extends IRBasicBlock> edge : funcCFGCopy.getEdges()) CFG.addEdge(edge);
        		
        		CFG.addEdge(newSuccCurrBlock, caseBranch, funcCFGCopy.getEntry());
        		if(funcCFGCopy.getExit() != null) CFG.addEdge(funcCFGCopy.getExit(), restBlock);
        	}
        	
        	IRBooleanExpression defaultCase = new DefaultCaseGuard(funNode, caseGuards);
        	CFG.addEdge(newSuccCurrBlock, defaultCase, restBlock);
      	} else {
        	IOUtils.errPrinter().pln("Function " + funcCallStmt + " cannot find any functions to inlined.");
        	newSuccCurrBlock = nextBlock;
    			CFG.addEdge(nextBlock, restBlock);
      	}
  		}
  		
  	  /* Replace all use with currBlock with restBlock */
  	  Collection<? extends IREdge<? extends IRBasicBlock>> outgoings
  				= ImmutableList.copyOf(CFG.getOutgoingEdges(currBlock));
  	  
  	  for(IREdge<? extends IRBasicBlock> outgoing : outgoings) {
  			IRBasicBlock dest = outgoing.getTarget();
  			CFG.removeEdge(outgoing);
  			CFG.addEdge(restBlock, outgoing.getGuard(), dest);
  	  }
  	  
  	  /* Connect current block to the entry of funcCFG */
  	  CFG.addEdge(currBlock, newSuccCurrBlock);
  	  
  	  /* Update the cfg's exit block */
  		if(currBlock.equals(CFG.getExit())) CFG.setExit(restBlock);
  	  
  		/* Continue inline the funcCall statements in the restBlock */
  		currBlock = restBlock;
  	} while(true);
  	
  	return changed;
  }
  
  /**
   * Function inline funcCFG for every the function call statement of the function 
   * in <code>funcCallBlock</code> into <code>CFG</code>.
   * 
   * @param CFG
   * @param funcCallBlock
   * @param funcName
   */
  private void functionInlineBlockWithFuncCFG(IRControlFlowGraph CFG, IRBasicBlock funcCallBlock,
  		IRControlFlowGraph funcCFG) {
  	final String functionName = funcCFG.getName();
  	IRBasicBlock currBlock = funcCallBlock;
  	
  	do {
  		int index = Iterables.indexOf(currBlock.getStatements(), new Predicate<IRStatement>() {
				@Override
        public boolean apply(IRStatement stmt) {
			    if(!CALL.equals(stmt.getType())) return false;
			    Node funNode = stmt.getOperand(0).getSourceNode();
			    if(!isFunctionCall(funNode)) return false;
			    String funName = CAnalyzer.toFunctionName(funNode);
			    return funName.equals(functionName);
        }
  		});
  		if(index == -1) break; // no such element;
  		
  		/* First statement in nextBlock is funcCall statement, currBlock is clean */
  		IRBasicBlock nextBlock = currBlock.splitAt(index);
  		
  		/* Isolate funcCall statement in nextBlock, restBlock contains the following statements */
  		IRBasicBlock restBlock = nextBlock.splitAt(1);
  		
  		IRBasicBlock newSuccCurrBlock; // The successor of the current block
  		
  		IRStatement funcCallStmt = nextBlock.getStatements().get(0);
      IRControlFlowGraph funcCFGCopy = funcCFG.clone();
      refreshScope(CFG, funcCFGCopy);
  		inlineFuncCallGraph(funcCFGCopy, funcCallStmt);
  		
			newSuccCurrBlock = funcCFGCopy.getEntry();
			
			/* Merge funcCallCFG into cfg */
			for(IREdge<? extends IRBasicBlock> edge : funcCFGCopy.getEdges()) 
				CFG.addEdge(edge);
  	  
			if(funcCFGCopy.getExit() != null)
				CFG.addEdge(funcCFGCopy.getExit(), restBlock);
  		
  	  /* Replace all use with currBlock with restBlock */
  	  Collection<? extends IREdge<? extends IRBasicBlock>> outgoings
  				= ImmutableList.copyOf(CFG.getOutgoingEdges(currBlock));
  	  
  	  for(IREdge<? extends IRBasicBlock> outgoing : outgoings) {
  			IRBasicBlock dest = outgoing.getTarget();
  			CFG.removeEdge(outgoing);
  			CFG.addEdge(restBlock, outgoing.getGuard(), dest);
  	  }
  	  
  	  /* Connect current block to the entry of funcCFG */
  	  CFG.addEdge(currBlock, newSuccCurrBlock);
  	  
  	  /* Update the cfg's exit block */
  		if(currBlock.equals(CFG.getExit())) CFG.setExit(restBlock);
  	  
  		/* Continue inline the funcCall statements in the restBlock */
  		currBlock = restBlock;
  	} while(true);
  }
  
  private void refreshScope(IRControlFlowGraph callerCFG, IRControlFlowGraph calleeCFG) {
	  String freshCalleeName = callerCFG.getName() + Constants.QUALIFIER
	  		+ Identifiers.uniquify(calleeCFG.getName());
	  
	  for(IRBasicBlock block : calleeCFG.getBlocks()) {
	  	for(IRStatement stmt : block.getStatements()) {
	  		if(stmt.hasProperty(Identifiers.SCOPE)) {
	  			assert(StatementType.FUNC_ENT.equals(stmt.getType()) ||
	  					StatementType.FUNC_EXIT.equals(stmt.getType()));
	  			String funcScopeName = (String) stmt.getProperty(Identifiers.SCOPE);
	  			String freshFuncScopeName = funcScopeName.replace(calleeCFG.getName(), freshCalleeName);
	  			stmt.setProperty(Identifiers.SCOPE, freshFuncScopeName);
	  		}
	  	}
	  }
  }
  
  private Node getVarArgNode(String funcName, Location loc) {
	  IRVarInfo funcInfo = symbolTable.lookup(funcName);
	  String varName = (String) funcInfo.getProperty(Identifiers.VAR_ARG);
	  IRVarInfo varInfo = symbolTable.lookup(varName);
	  String scopeName = varInfo.getScopeName();
	  Type varType = varInfo.getXtcType();
	  varType.scope(scopeName);
	  
	  Node varNode = GNode.create("PrimaryIdentifier", varName);
	  varNode.setLocation(loc);
	  varType.mark(varNode);
	  symbolTable.mark(varNode);
	  return varNode; 
  }

  private Collection<IRControlFlowGraph> lookupFuncCFG(Node funcNode,
  		IRStatement funcCallStmt) {
  	Preconditions.checkArgument(CALL.equals(funcCallStmt.getType()));
  	if(funcCallStmt.hasProperty(Identifiers.SCOPE)) {
    	String scopeName = (String) funcCallStmt.getProperty(Identifiers.SCOPE);
    	CScopeAnalyzer.pushScope(scopeName);
  	}

  	Collection<IRVar> funcVars = preprocessor.getEquivFuncVars(funcNode);
  	
  	if(funcCallStmt.hasProperty(Identifiers.SCOPE)) {
  		CScopeAnalyzer.popScope();
  	}
  	
  	Collection<IRControlFlowGraph> funcCFGs = Lists.newArrayListWithCapacity(funcVars.size());
  	
  	Type funcType = CType.getType(funcNode);
  	if(Tag.POINTER.equals(funcType.tag())) 
  		funcType = funcType.resolve().toPointer().getType();
  	
  	for(IRVar var : funcVars) {
  		String name = var.getName();
  		Type funcVarType = symbolTable.lookupType(name);
  		Type composeType = CType.getInstance().compose(funcType, funcVarType);
  		if(composeType.isError()) continue;
  		
  		IRControlFlowGraph funcCFG = cfgs.get(name);
  		if(null != funcCFG) funcCFGs.add(funcCFG);
  	}
  	
  	return funcCFGs;
  }
	
	private Collection<String> getFuncNames(final Collection<IRControlFlowGraph> currCfgs) {
		return ImmutableList.copyOf(Iterables.transform(currCfgs,
						new Function<IRControlFlowGraph, String>() {
					@Override
          public String apply(IRControlFlowGraph cfg) {
	          return cfg.getName();
          }
		}));
	}
  
  private CaseGuard getCaseGuard(IRControlFlowGraph funcCFG, IRExpression valExpr) {
  	GNode declarator = funcCFG.getSourceNode().getGeneric(2);
		GNode identifier = CAnalyzer.getDeclaredId(declarator);
		CExpression funcExpr = CExpression.create(identifier, funcCFG.getScope());
		
		Node funNode = valExpr.getSourceNode();
		xtc.type.Type funType = CType.getType(funNode).resolve();
		if(funType.isPointer()) { // For syntax sugar of function pointers funcPtr == f : *funcPtr == f
			GNode ptrToNode = GNode.create("IndirectionExpression", funNode);
			ptrToNode.setLocation(funNode.getLocation());
			funType.toPointer().getType().mark(ptrToNode);
			symbolTable.mark(ptrToNode);
			
			String scopeName = CType.getScopeName(funNode);
			ptrToNode.setProperty(xtc.Constants.SCOPE, scopeName);
			Scope scope = symbolTable.getScope(funNode);
			valExpr = CExpression.create(ptrToNode, scope);
		}
		
		CaseGuard caseBranch = new CaseGuard(valExpr, funcExpr);
		return caseBranch;
  }

  /**
   * Clean up the CFGs not referenced (directly or indirectly of the main CFG)
   */
	void cleanup(Map<Node, IRControlFlowGraph> cfgs, FunctionCallGraph callGraph) {
		// Function names referenced by the main function.
		Collection<String> callees = callGraph.getAllCallees(Identifiers.MAIN);
		// Cleanup callGraph with the call edges between functions within callees.
	  callGraph.retainFunctions(callees);
	  // The name of the global CFG should be added to callees.
	  callees.add(Identifiers.GLOBAL_CFG);
	  // Cleanup CFGs with names contained within callees.
	  for(Iterator<Map.Entry<Node, IRControlFlowGraph>> it = cfgs.entrySet().iterator(); it.hasNext(); ) {
	  	String funcName = it.next().getValue().getName();
      if(!callees.contains(funcName)) {
        it.remove();
      }
    }
  }
}
