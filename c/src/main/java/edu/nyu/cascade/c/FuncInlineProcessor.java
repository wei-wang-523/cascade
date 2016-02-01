package edu.nyu.cascade.c;

import java.io.File;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public class FuncInlineProcessor {
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final Map<String, Node> functions;
  private final Map<File, CSymbolTable> symbolTables;
  private final int effortLevel;
	
  private FuncInlineProcessor(
  		RunProcessor processor,
      Map<Node, IRControlFlowGraph> cfgs,
      Map<File, CSymbolTable> symbolTables,
      int effortLevel) {
    this.cfgs = cfgs;
    this.symbolTables = symbolTables;
    this.functions = Maps.newHashMap();
    this.effortLevel = effortLevel;
    for(Entry<Node, IRControlFlowGraph> pair : cfgs.entrySet()) {
    	String funcName = pair.getValue().getName();
    	Node funcDefNode = pair.getKey();
    	functions.put(funcName, funcDefNode);
    }
  }
  
  public static FuncInlineProcessor create(
  		RunProcessor processor,
      Map<Node, IRControlFlowGraph> cfgs,
      Map<File, CSymbolTable> symbolTables) {
  	int effortLevel = Integer.MAX_VALUE;
  	if(Preferences.isSet(Preferences.OPTION_FUNC_INLINE))
  		effortLevel = Preferences.getInt(Preferences.OPTION_FUNC_INLINE);
  	return new FuncInlineProcessor(processor, cfgs, symbolTables, effortLevel);
  }
  
  boolean functionInlineCFG(IRControlFlowGraph cfg) {
  	return functionInlineCFGWithLevel(cfg, 0);
	}
	
	boolean functionInlineCFGOneLevel(IRControlFlowGraph cfg) {
		Collection<IRBasicBlock> funcCallBlocks = ImmutableList.copyOf(pickFuncCallBlocks(cfg));
		if(Iterables.isEmpty(funcCallBlocks)) return false;
		
	  /* Function in-line for each path with function call */
	  for(IRBasicBlock funcBlock : funcCallBlocks)
	    functionInlineBlock(cfg, funcBlock);
	  
	  return true;
	}
	
	boolean hasFunctionCall(IRControlFlowGraph cfg) {
		Iterable<? extends IRBasicBlock> funcCallBlocks = pickFuncCallBlocks(cfg);
		return Iterables.isEmpty(funcCallBlocks);
	}

	private boolean functionInlineCFGWithLevel(IRControlFlowGraph cfg, int level) {
		if(level >= effortLevel) return false;
		
		Collection<IRBasicBlock> funcCallBlocks = ImmutableList.copyOf(pickFuncCallBlocks(cfg));
		if(Iterables.isEmpty(funcCallBlocks)) return false;
		
	  /* Function in-line for each path with function call */
	  for(IRBasicBlock funcBlock : funcCallBlocks) {
	    functionInlineBlock(cfg, funcBlock);
	    functionInlineCFGWithLevel(cfg, level+1);
	  }
	
	  return true;
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
				    if(stmt.hasProperty(Identifiers.STMTFUNC)
				    		|| stmt.hasProperty(Identifiers.STMTFUNCASSIGN)) {
				    	String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
				    	return isDefinedFunction(funcName);
				    }
				    return false;
					}
				});			
			}
		});
	}
  
	/** Check if function <code>funcName</code> is declared */
  private boolean isDefinedFunction(String funcName) {
  	if(functions.containsKey(funcName)) {
  		return functions.get(funcName) != null;
    }
    return false;
  }
  
  /** 
   * Get the graph of function with <code>funcName</code>.
   * 
   * The graph will be cloned before return it. It is
   * to make sure the function graphs inlined into different
   * call position, are not share the same paths, to
   * avoid fake phi-node inside the graph -- that multiple 
   * function call paths joined at the entry path of function
   * graph. 
   * 
   * TODO: in the function based encoding, the clone is not 
   * necessary.
   */
	private IRControlFlowGraph getFuncCFG(final String funcName) {
		IRControlFlowGraph cfg = Iterables.find(cfgs.values(), 
				new Predicate<IRControlFlowGraph>() {
			@Override
			public boolean apply(IRControlFlowGraph cfg) {
				return funcName.equals(cfg.getName());
			}
		});
		
		return cfg;
  }
  
	/**
   * Get the argument passing statements of function call nested
   * in the statement <code>stmt</code>
   * 
   * @return empty list if the function is not defined or 
   * without parameters
   */
  @SuppressWarnings("unchecked")
  private Collection<IRStatement> assignArgToParam(IRStatement stmt) {
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
    if(!stmt.hasProperty(Identifiers.ARGUMENTS)) return Collections.emptyList();
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    assert(isDefinedFunction(funcName));
    
    Node defNode = functions.get(funcName);
    
    /* Find the parameter declare node */
    Node paramDeclare = null;
    
    for(Object o : defNode.getNode(2)) {
      if(o != null && o instanceof Node && 
      		((Node) o).hasName("FunctionDeclarator")) {
          o = ((Node) o).get(1);
      }
      
      if(o != null && o instanceof Node && 
      		((Node) o).hasName("ParameterTypeList")) {
      	paramDeclare = ((Node) o).getNode(0);
      	break;
      }
    }
    
    if(paramDeclare == null)    return Collections.emptyList();
    
    /* Pick all arguments */
    List<IRExpression> args = (List<IRExpression>) stmt.getProperty(Identifiers.ARGUMENTS);
    int argSize = args.size();
    
    assert(paramDeclare.size() == argSize);
    
    Collection<IRStatement> assignments = Lists.newArrayListWithCapacity(argSize);
    
    /* Generate assign statement one by one */
    
    /* Pick the new scope for the function declaration */
    File file = new File(defNode.getLocation().file);
    CSymbolTable symbolTable = symbolTables.get(file);
    Scope paramScope = symbolTable.getScope(defNode);
    
    for(int i=0; i < argSize; i++) {
      Node paramNode = paramDeclare.getNode(i);
      paramNode = paramNode.getNode(1);
      /* Pointer parameter declaration */
      if(paramNode.hasName("PointerDeclarator"))
        paramNode = paramNode.getNode(1);
      
      if(paramNode.hasName("ArrayDeclarator"))
        paramNode = paramNode.getNode(0);
      
      assert(paramNode.hasName("SimpleDeclarator"));
      GNode primaryId = GNode.create("PrimaryIdentifier", paramNode.get(0));
      primaryId.setLocation(paramNode.getLocation());
      for(String label : paramNode.properties())
      	primaryId.setProperty(label, paramNode.getProperty(label));
      
      IRExpressionImpl param = CExpression.create(primaryId, paramScope);
      IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
      Node argNode = arg.getSourceNode();
      Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
      assignNode.setLocation(paramNode.getLocation());
      /* FIXME: assign node has no scope, we cannot attach it with the caller scope or 
       * the callee scope. assign node also has no type attached. In fact, we do not
       * bother to analyze it.
       */
//      cAnalyzer.analyze(assignNode);     
      Statement assignStmt = Statement.assign(assignNode, param, arg);
      assignments.add(assignStmt);
    }    
    return assignments; 
  }
  
  /**
   * Build function in-line graph for assign statement of function call 
   * <code>stmt</code>
   * 0) ent statement
   * 1) arguments passing 
	 * 2) graph built from the function declaration node.
	 * 3) return statement replacement
	 * 4) ret statement
   */
  private void inlineAssignFuncCallGraph(IRControlFlowGraph funcCFG, IRStatement stmt) {
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNCASSIGN));
  	Preconditions.checkArgument(stmt.getType().equals(StatementType.ASSIGN));
  	
    /* Insert parameter-argument pass statements */
    Collection<IRStatement> paramPassStmts = assignArgToParam(stmt);
    if(!paramPassStmts.isEmpty())
    	CfgProcessor.insertParamArgAssignStmts(funcCFG, paramPassStmts);
    
    /* Append assign statement to all the return statements. */
    CfgProcessor.appendReturnStmt(funcCFG, stmt);
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
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNC));
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    /* Insert parameter-argument pass statements */
    Collection<IRStatement> paramPassStmts = assignArgToParam(stmt);
    if(!paramPassStmts.isEmpty())
    	CfgProcessor.insertParamArgAssignStmts(funcCFG, paramPassStmts);
  }

  /** Build function in-lined graph for <code>funcCallBlock</code> */
  private void functionInlineBlock(IRControlFlowGraph cfg, IRBasicBlock funcCallBlock) {
  	IRBasicBlock currBlock = funcCallBlock;
  	
  	do {
  		int index = Iterables.indexOf(currBlock.getStatements(), new Predicate<IRStatement>() {
				@Override
        public boolean apply(IRStatement stmt) {
					return stmt.hasProperty(Identifiers.STMTFUNCASSIGN) || 
							stmt.hasProperty(Identifiers.STMTFUNC);
        }
  		});
  		if(index == -1) break; // no such element;
  		
  		/* First statement in nextBlock is funcCall statement, currBlock is clean */
  		IRBasicBlock nextBlock = currBlock.splitAt(index);
  		
  		/* Isolate funcCall statement in nextBlock, restBlock contains the following statements */
  		IRBasicBlock restBlock = nextBlock.splitAt(1);
  		
  		IRBasicBlock newSuccCurrBlock; // The successor of the current block
  		
  		IRStatement funcCallStmt = nextBlock.getStatements().get(0);
      String funcName = (String) funcCallStmt.getProperty(Identifiers.FUNCNAME);
      if(!isDefinedFunction(funcName))	{
      	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
      	newSuccCurrBlock = nextBlock;
  			cfg.addEdge(nextBlock, restBlock);
  			
  		} else {
        IRControlFlowGraph funcCFG = getFuncCFG(funcName).clone();
        
    		if(funcCallStmt.hasProperty(Identifiers.STMTFUNCASSIGN)){
    			inlineAssignFuncCallGraph(funcCFG, funcCallStmt);
    		} else {
    			inlineFuncCallGraph(funcCFG, funcCallStmt);
    		}
    		
  			newSuccCurrBlock = funcCFG.getEntry();
  			
  			/* Merge funcCallCFG into cfg */
  			for(IREdge<? extends IRBasicBlock> edge : funcCFG.getEdges()) 
  				cfg.addEdge(edge);
    	  
  			if(funcCFG.getExit() != null)
  				cfg.addEdge(funcCFG.getExit(), restBlock);
  		}
  		
  	  /* Replace all use with currBlock with restBlock */
  	  Collection<? extends IREdge<? extends IRBasicBlock>> outgoings
  				= ImmutableList.copyOf(cfg.getOutgoingEdges(currBlock));
  	  
  	  for(IREdge<? extends IRBasicBlock> outgoing : outgoings) {
  			IRBasicBlock dest = outgoing.getTarget();
  			cfg.removeEdge(outgoing);
  			cfg.addEdge(restBlock, outgoing.getGuard(), dest);
  	  }
  	  
  	  /* Connect current block to the entry of funcCFG */
  	  cfg.addEdge(currBlock, newSuccCurrBlock);
  	  
  	  /* Continue inline the funcCall statements in the restBlock */
  		currBlock = restBlock;
  	} while(true);
  }
}
