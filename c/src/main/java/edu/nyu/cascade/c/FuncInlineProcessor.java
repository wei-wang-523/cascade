package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.FunctionT;
import xtc.type.NumberT;
import xtc.type.Type;
import xtc.type.Type.Tag;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.impl.BasicBlock;
import edu.nyu.cascade.ir.impl.CaseGuard;
import edu.nyu.cascade.ir.impl.DefaultCaseGuard;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALL;

public class FuncInlineProcessor<T> {
  private final Map<String, IRControlFlowGraph> cfgs;
  private final SymbolTable symbolTable;
  private final PreProcessor<T> preprocessor;
  private final int effortLevel;
	
  private FuncInlineProcessor(
      Map<Node, IRControlFlowGraph> cfgs,
      SymbolTable symbolTable,
      PreProcessor<T> preprocessor,
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
  
  static <T> FuncInlineProcessor<T> create(
      Map<Node, IRControlFlowGraph> cfgs,
      SymbolTable symbolTable,
      PreProcessor<T> preprocessor) {
  	int effortLevel = Integer.MAX_VALUE;
  	if(Preferences.isSet(Preferences.OPTION_FUNC_INLINE))
  		effortLevel = Preferences.getInt(Preferences.OPTION_FUNC_INLINE);
  	return new FuncInlineProcessor<T>(cfgs, symbolTable, preprocessor, effortLevel);
  }
  
  boolean functionInlineCFG(IRControlFlowGraph cfg) {
  	symbolTable.enterScope(cfg);
  	boolean res = functionInlineCFGWithLevel(cfg, 0);
  	symbolTable.exit();
  	return res;
	}
  
	
	boolean hasFunctionCall(IRControlFlowGraph cfg) {
		for(IRBasicBlock block : cfg.getBlocks()) {
			for(IRStatement stmt : block.getStatements()) {
				if(!CALL.equals(stmt.getType())) continue;
				Node funNode = stmt.getOperand(0).getSourceNode();
				if(isFunctionCall(funNode)) {
					String funcName = CAnalyzer.toFunctionName(funNode);
	  			if(cfgs.containsKey(funcName)) return false;
				} else {
					Collection<IRControlFlowGraph> foundCFGs = lookupFuncCFG(funNode);
	      	if(!foundCFGs.isEmpty()) return false;
				}
			}
		}
		
		return true;
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
  private Collection<IRStatement> assignArgToParam(IRStatement stmt, IRControlFlowGraph funcCFG, FunctionT funcType) {
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
    
    if(funcType.isVarArgs()) {
    	int argSize = args.size();
    	int paramSize = funcType.getParameters().size();
    	
    	Collection<IRStatement> assignments = Lists.newArrayListWithExpectedSize(paramSize);
    	assert (argSize >= paramSize);
    	
    	int i = 0;
    	for(; i < paramSize-1; i++) {
        Node paramNode = paramDeclare.getNode(i).getNode(1);
        Node idNode = CAnalyzer.getDeclaredId(GNode.cast(paramNode));
        GNode primaryId = GNode.create("PrimaryIdentifier", idNode.get(0));
        Type paramType = CType.getType(idNode);
        paramType.mark(primaryId);
        symbolTable.mark(primaryId);
        
        IRExpressionImpl param = CExpression.create(primaryId, symbolTable.getCurrentScope());
        IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
        Node argNode = arg.getSourceNode();
        Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
        assignNode.setLocation(paramNode.getLocation());
        Statement assignStmt = Statement.assign(assignNode, param, arg);
        assignments.add(assignStmt);
    	}
    	
      Node paramNode = paramDeclare.getNode(i).getNode(1);
      Node idNode = CAnalyzer.getDeclaredId(GNode.cast(paramNode));
      GNode primaryId = GNode.create("PrimaryIdentifier", idNode.get(0));
      Type paramType = CType.getType(idNode);
      paramType.mark(primaryId);
      symbolTable.mark(primaryId);
      
    	for(int j = 0; i< argSize; i++, j++) {
    		GNode offsetNode = GNode.create("IntegerConstant", String.valueOf(j));
    		NumberT.INT.mark(offsetNode);
    		GNode primaryIdPrime = GNode.create("AdditiveExpression", primaryId, "+", offsetNode);
    		paramType.mark(primaryIdPrime); symbolTable.mark(primaryId);
    		
    		IRExpressionImpl param = CExpression.create(primaryIdPrime, symbolTable.getCurrentScope());
    		IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
    		Node argNode = arg.getSourceNode();
    		
        Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
        assignNode.setLocation(paramNode.getLocation());
        Statement assignStmt = Statement.assign(assignNode, param, arg);
        assignments.add(assignStmt);
    	}
    	
    	return assignments; 
    } 
    
    else {
    	int argSize = args.size();
    	int paramSize = funcType.getParameters().size();
    	
      Collection<IRStatement> assignments = Lists.newArrayListWithExpectedSize(paramSize);
    	assert (argSize == paramSize);
    	
      for(int i=0; i < paramSize; i++) {
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
      
      return assignments; 
    }
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
      	Collection<IRControlFlowGraph> foundCFGs = lookupFuncCFG(funNode);
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
  
  private Collection<IRControlFlowGraph> lookupFuncCFG(Node funcNode) {  	
  	Collection<IRVar> funcVars = preprocessor.getEquivFuncVars(funcNode);
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
			
			String scopeName = CType.getScopeName(funNode);
			ptrToNode.setProperty(Identifiers.SCOPE, scopeName);
			Scope scope = symbolTable.getScope(funNode);
			valExpr = CExpression.create(ptrToNode, scope);
		}
		
		CaseGuard caseBranch = new CaseGuard(valExpr, funcExpr);
		return caseBranch;
  }
}
