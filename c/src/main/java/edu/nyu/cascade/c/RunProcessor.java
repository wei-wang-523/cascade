package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.GNode;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.type.NumberT;
import xtc.util.Pair;
import xtc.util.SymbolTable.Scope;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.control.CallPoint;
import edu.nyu.cascade.control.LoopPoint;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.jaxb.InsertionType;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathEncoding;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.expr.SimplePathEncoding;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.VarInfo;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.c.CSpecParser;

@SuppressWarnings("serial")
class RunProcessorException extends Exception {
  public RunProcessorException(String msg) {
    super(msg);
  }

  public RunProcessorException(String msg, Throwable cause) {
    super(msg, cause);
  }

  public RunProcessorException(Throwable cause) {
    super(cause);
  }
}

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */
final class PathEncoder {
  private PathEncoding pathEncoding;  // the encoding to use for the path
  private Expression path;  // the expression representing the encoded path 
  private boolean runIsValid, runIsFeasible, checkFeasibility;

  PathEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathEncoder create(PathEncoding encoding) {
    return new PathEncoder(encoding);
  }

  ExpressionEncoder getExpressionEncoder() {
    return pathEncoding.getExpressionEncoder();
  }
  
  /**
   * Prepare this encoder for a new path.
   */
  void reset() {
    path = pathEncoding.emptyPath();
    runIsValid = true;
    runIsFeasible = true;
  }

  /**
   * Encode the given statement as an extension of the current path.
   * 
   * @param stmt
   *          the statement to encode
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  boolean encodeStatement(IRStatement stmt) throws PathFactoryException {

    /* Precondition is OK, encode the postcondition. */
    path = stmt.getPostCondition(pathEncoding, path);
    if(IOUtils.debugEnabled())
      IOUtils.debug().pln("Post-condition: " + path).flush();
    
    ExpressionClosure pre = stmt.getPreCondition(pathEncoding.getExpressionEncoder());
    
    if (pre != null) {
      /* If the statement has a precondition, we have to check it before continuing with 
       * the encoding.
       */
      IOUtils.debug().pln("Checking pre-condition: " + pre).flush();
      ValidityResult<?> result = pathEncoding.checkAssertion(path, pre);

      IOUtils.debug().pln("Result: " + result).flush();
      runIsValid = result.isValid();
      
      if (!runIsValid) {
        if ( result.isInvalid() ) {
          if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
            if(result.getCounterExample().isEmpty())
              IOUtils.out().println("\nCounter-example:\n" + result.getUnknown_reason());
            else
              IOUtils.out().println("\nCounter-example:\n" + result.getCounterExample());
        } else { // result.isUnknown()
          IOUtils.out().println("Unkown: " + result.getUnknown_reason());
        }
        return false;
      } else if (checkFeasibility) {
        IOUtils.out().println("Checking path feasibility.");
        SatResult<?> res = pathEncoding.checkPath(path);
        IOUtils.out().println("Result: " + res);
        runIsFeasible = !res.isUnsatisfiable();
      }
    }
    
    return true;
  }

  boolean runIsFeasible() throws PathFactoryException {
    return runIsFeasible;
  }

  /**
   * Returns true if all verification conditions passed to handle() since the
   * last call to reset() were valid.
   */
  boolean runIsValid() {
    return runIsValid;
  }
  
  void setFeasibilityChecking(boolean b) {
    checkFeasibility = b;
  }
}

/**
 * A processor for control file runs (i.e., non-looping paths annotated
 * through the program).
 */
class RunProcessor {
  
  public RunProcessor(Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs, CAnalyzer cAnalyzer,
      CExpressionEncoder exprEncoder)
      throws RunProcessorException {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.cAnalyzer = cAnalyzer;
    this.pathEncoder = PathEncoder.create(SimplePathEncoding.create(exprEncoder));
    this.TEMP_VAR_POSTFIX = 0;
  }
  
  private final static ArrayList<String> ReservedFunctions = 
      Lists.newArrayList("valid", "implies", "forall", "exists", "reach", 
          "allocated", "create_acyclic_list", "create_cyclic_list", 
          "create_acyclic_dlist", "create_cyclic_dlist", "is_root");
  private final static String TEMP_VAR_PREFIX = "TEMP_VAR_";
  private final static String TEST_VAR_PREFIX = "TEST_VAR_";
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final CAnalyzer cAnalyzer;
  private final PathEncoder pathEncoder;
  private int TEMP_VAR_POSTFIX;

  /**
   * Process a run: build the path through the CFG that it represents, convert
   * the path to a verification condition, then check the verification
   * condition.
   * 
   * @param run
   *          a run from a Cascade control file
   * @return true if all assertions in the run hold, false otherwise.
   * @throws RunProcessorException
   *           if an error occurred while processing the run. E.g., if the path
   *           was ill-defined, or if an unhandled statement was encountered.
   */
  protected boolean process(Run run) throws RunProcessorException {
    try {
      List<IRStatement> globalPath = CfgBuilder.getGlobalStmts(run);
      List<IRStatement> path = processRun(run.getStartPosition(), 
          run.getEndPosition(), run.getWayPoints());
      if(globalPath != null)    path.addAll(0, globalPath);
      
      if (IOUtils.debugEnabled()) {
        IOUtils.debug().pln("Complete path for run...");
        for (IRStatement stmt : path) {
          IOUtils
              .debug()
              .pln(stmt.getLocation() + " " + stmt.toString())
              .flush();
        }
      }
      
      for (IRStatement stmt : path) {
        IOUtils.out().println(stmt.getLocation() + " " + stmt); 
        if (!pathEncoder.encodeStatement(stmt))
          break;
      }

      if (pathEncoder.runIsValid() && !pathEncoder.runIsFeasible()) {
        IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
      }
      
      return pathEncoder.runIsValid();
    } catch (PathFactoryException e) {
      throw new RunProcessorException(e);
    }
  }

  /**
   * Incorporate the command for the given position into the given path.
   * 
   * @throws RunProcessorException
   */
  void processPosition(Position position, CSymbolTable symbolTable,
      List<IRStatement> path) throws RunProcessorException {
    List<Command> cmds = position.getCommands();
    for(Command cmd : cmds) {
      try {
        String funName = cmd.getCascadeFunction();
        CSpecParser funParser = new CSpecParser(new StringReader(funName),
            position.getFile().getPath());
        Result funResult = funParser.pCSpecExpression(0);
        Node fun = (Node) funParser.value(funResult);
      
        List<String> args = cmd.getArgument();
        List<CExpression> argExprs = Lists.newArrayList();
        
        for(String arg : args) {
          CSpecParser specParser = new CSpecParser(new StringReader(arg),
              position.getFile().getPath());
          Result specResults = specParser.pCSpecExpression(0);
          Node spec = (Node) specParser.value(specResults);
        
          /*
           * TODO: modifications to the symbol table by the analyzer are ignored.
           */
          cAnalyzer.analyze(spec, symbolTable.getOriginalSymbolTable());
          IOUtils
          .debug()
          .pln("<ast>")
          .incr()
          .format(spec)
          .decr()
          .pln("\n</ast>")
          .flush();
          CExpression argExpr = CExpression.create(spec,symbolTable.getCurrentScope());
          IOUtils.debug().pln(argExpr.toString()).flush();
          argExprs.add(argExpr);
        }
        
        if (funName.trim().equals("cascade_check")) {
          path.add(Statement.assertStmt(fun, argExprs.get(0)));
        } else if (funName.trim().equals("cascade_assume")) {
          path.add(Statement.assumeStmt(fun, argExprs.get(0)));
        } else {
          throw new RunProcessorException("Unknown Cascade function: " + funName);
        }
        
      } catch (IOException e) {
        throw new RunProcessorException("Specification parse failure", e);
      } catch (ParseException e) {
        throw new RunProcessorException("Specification parse failure", e);
      }
    }

  }

  /**
   * Find a path in the CFG to the given position and add the statements along
   * the path to the <code>List</code> <code>path</code>. If more than one path
   * to the position exists in the CFG, one will be chosen arbitrarily. Raises
   * <code>PathBuilderException</code> if no path to the position can be found.
   * 
   * The behavior if <code>position</code> is not within a basic block depends
   * on the property <code>position.matchAfter</code>: if <code>true</code>, the
   * path will terminate at the nearest subsequent block; if <code>false</code>,
   * it will terminate after the nearest preceding block.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   * @throws RunProcessorException
   */
  private IRBasicBlock buildPathToPosition(IRControlFlowGraph cfg,
      IRBasicBlock block, IRLocation pos, List<IRStatement> path) 
          throws RunProcessorException {
    IRBasicBlock target;
    if(pos instanceof Position) {
      target = cfg.splitAt(pos, InsertionType.AFTER.equals(
          ((Position)pos).getInsertionType()));
    } else {
      throw new RunProcessorException("Bad position: " + pos);
    }      

    if( target==null ) {
      throw new RunProcessorException("Bad position: " + pos);
    }
    IOUtils.debug().pln("Searching for path:").incr().pln(
        "Source: " + block + "\nTarget: " + target).decr().flush();
    return buildPathToBlock(cfg, block, target, path);
  }

  /**
   * Find a path in the CFG to the given start block and target block, and add
   * the statements along the path to the <code>list</code> <code>path</code>. 
   * If more than one path to the position exists in the CFG, one will be chosen
   * arbitrarily. Raises <code>PathBuilderException</code> if no path can be 
   * found.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   * @throws RunProcessorException
   */
  
  private IRBasicBlock buildPathToBlock(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target, List<IRStatement> path) 
          throws RunProcessorException {
    /*
     * Find the shortest path from block to target, using a backwards
     * breadth-first search. pathMap will associate each block with its
     * "next hop" in the shortest path.
     */
    Map<IRBasicBlock, IREdge<?>> pathMap = Maps.newHashMap();
    Set<IRBasicBlock> visited = Sets.newHashSet();
    Queue<IRBasicBlock> queue = Lists.newLinkedList();
    
    /* For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node. */
    if(start.equals(target) && start.getType().equals(IRBasicBlock.Type.LOOP)) {
      for (IREdge<?> e : cfg.getIncomingEdges(start)) {
        IRBasicBlock v = e.getSource();
        if (!visited.contains(v)) {
          queue.add(v);
          pathMap.put(v, e);
        }
      }
    } else {
      queue.add(target);
    }
    
    while (!(visited.contains(start) || queue.isEmpty())) {
      IRBasicBlock u = queue.remove();
      visited.add(u);
      for (IREdge<?> e : cfg.getIncomingEdges(u)) {
        IRBasicBlock v = e.getSource();
        if (!(visited.contains(v) || queue.contains(v))) {
          queue.add(v);
          pathMap.put(v, e);
        }
      }
    }

    if (!visited.contains(start)) {
      /* The two blocks aren't connected! */
      IOUtils.err().println("No path found.");
      throw new RunProcessorException("Invalid run");
    }

    /* Add statements along the shortest path */
    IRBasicBlock u = start;
    IOUtils.debug().pln("Shortest path:").incr().flush();
    
    /* For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node. */
    if(start.equals(target) && start.getType().equals(IRBasicBlock.Type.LOOP)) {
      IOUtils.debug().pln(u.toString()).flush();
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    
    while (!target.equals(u)) {
      IOUtils.debug().pln(u.toString()).flush();
      int iterTimes = u.getIterTimes();
      while(iterTimes > 0) {
        u.clearIterTimes();
        u = buildPathToBlock(cfg, u, u, path);
        iterTimes--;
      }
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    IOUtils.debug().decr().flush();

    return target;
  }
  
  private void addEdgeToPath(List<IRStatement> path, IREdge<?> e) {
    if (e.getGuard() != null) {
      path.add(Statement.assumeStmt(e.getSourceNode(), e.getGuard()));
    }
  }

  /**
   * Find the CFG that "contains" the given position. Since we don't track where
   * a function ends, we choose the closest match, defined as: a CFG starting on
   * line X in file F is the closest match for a position on line Y in file F
   * iff. X <= Y, and no other CFG in file F starts on line Z such that X < Z <=
   * Y.
   */
  private IRControlFlowGraph getCFGForLocation(IRLocation start) {
    IOUtils.debug().pln("Finding CFG for position: " + start);

    File file = start.getFile();
    int lineNum = start.getLine();

    Node bestNode = null;
    int bestDiff = Integer.MAX_VALUE;

    for (Node node : cfgs.keySet()) {
      Location loc = node.getLocation();
      IOUtils.debug().loc(node).p(' ');
      if (file.equals(new File(loc.file))) {
        int diff = lineNum - loc.line;
        IOUtils.debug().p("diff=" + diff + " ");
        if (diff == 0) {
          IOUtils.debug().pln("Exact match.");
          bestNode = node;
          break;
        } else if (diff > 0 && diff < bestDiff) {
          IOUtils.debug().pln("Best match so far.");
          bestNode = node;
          bestDiff = diff;
        } else {
          IOUtils.debug().pln("Not a match.");
        }
      } else {
        IOUtils.debug().pln("Wrong file.");
      }
    }
    IRControlFlowGraph cfg = cfgs.get(bestNode);
    IOUtils.debug().pln("CFG for position: " + cfg).flush();
    return cfg;
  }

  /** Find the CFG for function call <code>Statement</code>. 
   * @throws RunProcessorException */
  private IRControlFlowGraph getCFGForStatement(IRStatement stmt) 
      throws RunProcessorException {
    Node bestNode = findFuncDeclareNode(stmt);
    IRControlFlowGraph cfg = cfgs.get(bestNode);
    return cfg;
  }
  
  /** Get the function declare <code>Node</code> for the function call statement. 
   * @throws RunProcessorException */
  private Node findFuncDeclareNode (IRStatement stmt) throws RunProcessorException {
    String name = ((Statement) stmt).getOperand(0).toString();
    
    File file = stmt.getLocation().getFile();
    CSymbolTable symbolTable = symbolTables.get(file);

    IRVarInfo info = symbolTable.lookup(name);
    if(info == null)    return null; // For undeclared function.
    Location funcDeclareLoc = info.getDeclarationNode().getLocation();
    
    String funcFile = funcDeclareLoc.file;
    int lineNum = funcDeclareLoc.line;
    Node bestNode = null;    
    for (Node node : cfgs.keySet()) {
      Location loc = node.getLocation();
      if (funcFile.equals(loc.file)) {
        int diff = lineNum - loc.line;
        if (diff == 0) {
          bestNode = node;
          break;
        }
      }
    }
    
    if(bestNode == null) {
      // FIXME: continue find in the parent scope or stays at root scope initially?
      System.err.println("Cannot find the function declaration node for " + stmt);
    }
    return bestNode;
  }
  
  /** Collect a list <code>Statement</code> from function body. */
  private List<IRStatement> collectStmtFromFunction(IRStatement stmt) 
      throws RunProcessorException {
    List<IRStatement> path = Lists.newArrayList();
    IRControlFlowGraph cfg = getCFGForStatement(stmt);
    if(cfg == null) {
      System.err.println("Cannot find cfg for statement: " + stmt);
    } else {
      IRBasicBlock entry = cfg.getEntry();
      IRBasicBlock exit = cfg.getExit();
      buildPathToBlock(cfg, entry, exit, path);
    }
    return path;
  }

  /** Create the assign <code>Statements</code> from arguments to parameters. 
   * @throws RunProcessorException */
  private List<IRStatement> assignArgToParam(IRStatement stmt) 
      throws RunProcessorException {
    return assignArgToParam(null, stmt); 
  }
  
  /** Create the assign <code>Statements</code> from arguments to parameters. 
   * @throws RunProcessorException */
  private List<IRStatement> assignArgToParam(IRStatement repStmt, IRStatement rmvStmt) 
      throws RunProcessorException {
    if(!rmvStmt.getType().equals(StatementType.CALL)) {
      throw new RunProcessorException("Invalid statement type: " + rmvStmt);
    }
      
    Node defNode = findFuncDeclareNode(rmvStmt);    
    List<IRStatement> assignments = Lists.newArrayList();
    
    if(defNode == null)     return assignments;
    
    // Pick the new scope for the function declaration    
    File file = new File(defNode.getLocation().file);
    CSymbolTable symbolTable = symbolTables.get(file);  
    Scope paramScope = symbolTable.getScope(defNode);
    
    Node paramDeclare = null;
    
    for(Object o : defNode.getNode(2)) {
      if(o != null) {
        if("FunctionDeclarator".equals(((Node) o).getName())) {
          o = ((Node) o).get(1);
        }
      }
      if(o != null) {
        if("ParameterTypeList".equals(((Node) o).getName())) {
          paramDeclare = ((Node) o).getNode(0);
          break;
        }
      }
    }
    
    if(paramDeclare == null)    return assignments;
    
    // Pick all arguments
    List<IRExpression> args = Lists.newArrayList(rmvStmt.getOperands());
    args = args.subList(1, args.size());
    
    if(repStmt != null) {
      switch(repStmt.getType()) {
      case ASSIGN: {
        Node argNode = ((Statement) repStmt).getOperand(1).getSourceNode().getNode(1); 
        for(int i=0; i<args.size(); i++) {
          Node arg_call = args.get(i).getSourceNode();
          Node arg_assign = argNode.getNode(i);
          if(!arg_call.equals(arg_assign)) {
            if(!arg_assign.getString(0).startsWith(TEMP_VAR_PREFIX)) {
              throw new RunProcessorException("Invalid argument: " + arg_assign);
            }
            args.set(i, CExpression.create(arg_assign, symbolTable.getScope(arg_assign)));
          }      
        }
        break;
      }
      case CALL: {
        List<IRExpression> args_call = Lists.newArrayList(((Statement) repStmt).getOperands());
        args_call = args_call.subList(1, args_call.size());
        for(int i=0; i<args.size(); i++) {
          IRExpression arg = args.get(i);
          IRExpression arg_call = args_call.get(i);
          if(!arg_call.equals(arg)) {
            if(!arg_call.getSourceNode().getString(0).startsWith(TEMP_VAR_PREFIX)) {
              throw new RunProcessorException("Invalid argument: " + arg_call);
            }
            args.set(i, arg_call);
          }      
        }
        break;
      }
      default :
        throw new RunProcessorException("Invalid stmt type: " + repStmt);
      }
      /* Go through all arguments to replace the function call argument with corresponding 
       * temporal variable within stmt_assign. */

    }
    
    if(paramDeclare.size() != args.size()) {
      throw new RunProcessorException("#arg does not match with #param.");
    }
    // Generate assign statement one by one
    for(int i=0; i < paramDeclare.size(); i++) {
      Node paramNode = paramDeclare.getNode(i);
      paramNode = paramNode.getNode(1);
      // Pointer parameter declaration
      if("PointerDeclarator".equals(paramNode.getName()))
        paramNode = paramNode.getNode(1);
      
      assert("SimpleDeclarator".equals(paramNode.getName()));
      IRExpressionImpl param = CExpression.create(paramNode, paramScope);
      IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
      Statement assign = Statement.assign(paramNode, param, arg);
      assignments.add(assign);
    }    
    return assignments; 
  }

  /** Replace the last return statement as assign statement. 
   * @throws RunProcessorException */
  private IRStatement replaceReturnStmt(IRStatement returnStmt, IRStatement assignStmt) 
      throws RunProcessorException {
    if(!returnStmt.getType().equals(StatementType.RETURN)) {
      throw new RunProcessorException("No return statement in call statement: " + assignStmt);
    }
    IRExpressionImpl lExpr = (IRExpressionImpl) ((Statement) assignStmt).getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) ((Statement) returnStmt).getOperand(0);
    IRStatement assignResult = Statement.assign(assignStmt.getSourceNode(), lExpr, rExpr);
    return assignResult;
  }
  
  /**
   * Collect <code>list</code> of all the relevant <code>Statement</code>
   * including assign arguments to parameters, statements in function body
   * and return statement.
   * @throws RunProcessorException 
   */
  private List<IRStatement> getStmtForAssignCall(IRStatement lhsStmt, IRStatement rhsStmt) 
      throws RunProcessorException {
      List<IRStatement> func_path = assignArgToParam(lhsStmt, rhsStmt);
      func_path.addAll(collectStmtFromFunction(rhsStmt));
      
      //  Pick the last statement from func_path - return statement.
      if(!func_path.isEmpty()) {
        IRStatement returnStmt = func_path.remove(func_path.size()-1);
        func_path.add(replaceReturnStmt(returnStmt, lhsStmt));
      }
      return func_path;
  }
  
  /**
   * Collect <code>List</code> of all relevant <code>Statement</code>
   * including assign statements to assign arguments to parameters, 
   * and the statements collected from the function body. 
   * @throws RunProcessorException 
   */
  private List<IRStatement> getStmtForCall(IRStatement stmt) throws RunProcessorException {
    if(!stmt.getType().equals(StatementType.CALL)) {
      throw new RunProcessorException("Invalid statement type: " + stmt);
    }
    List<IRStatement> func_path = assignArgToParam(stmt);
    func_path.addAll(collectStmtFromFunction(stmt));
    return func_path;
  }
    
  /**
   * Replace all the function call node with a temporary var node, and return the 
   * function call node list to keep the insertion order of the "pairs", otherwise, 
   * "pairs" will be arbitrary order.
   * @throws RunProcessorException 
   * @param node
   * @param symbolTable
   * @param scope
   * @param pairs
   * @return
   * @throws RunProcessorException
   */
  
  private LinkedHashMap<Node, Node> replaceFuncCallwithVar(Node node, CSymbolTable symbolTable, Scope scope) 
      throws RunProcessorException {
    Node resNode = node; 
    LinkedHashMap<Node, Node> funcNodeReplaceMap = Maps.newLinkedHashMap();
    // replace operands of node if we can find the replace candidate operands from "funcNodeReplaceMap"
    if(!node.isEmpty()) {
      // Collect operands of node
      boolean updated = false;
      List<Object> argList = Lists.newArrayList();
      for(int i=0; i<node.size(); i++) {
        Object arg = node.get(i);
        Object substituteArg = arg;
        if(arg instanceof Node) {
          Node argNode = (Node) arg;
          // update "argList" if we can find new pair by step into the operands of argx
          funcNodeReplaceMap.putAll(replaceFuncCallwithVar(argNode, symbolTable, scope));
          if(funcNodeReplaceMap.containsKey(argNode)) { // substitute arg
            substituteArg = funcNodeReplaceMap.get(argNode);
            updated = true;
          }
        }
        argList.add(substituteArg);
      }
      if(updated) { // compose a substituted node
        resNode = createNodeWithArgList(node.getName(), argList);
        resNode.setLocation(node.getLocation());
        resNode.setProperty(xtc.Constants.SCOPE, scope.getQualifiedName());
      }
    } 
    
    // build pairs by replace function call to temp_var if such function call
    // node hasn't been replaced before
    if(!funcNodeReplaceMap.containsKey(resNode) && "FunctionCall".equals(resNode.getName())) {
      String resFuncName = resNode.getNode(0).getString(0);
      if(!ReservedFunctions.contains(resFuncName)) {
        if(symbolTable.lookup(resFuncName) == null)
          throw new RunProcessorException("Undeclared function: " + resFuncName);
        // Create temporary variable node for function call node.
        String varName = TEMP_VAR_PREFIX + (TEMP_VAR_POSTFIX++);
        GNode varNode = GNode.create("PrimaryIdentifier", varName);
        varNode.setLocation(node.getLocation());
        varNode.setProperty(xtc.Constants.SCOPE, scope.getQualifiedName());
        varNode.setProperty(xtc.Constants.TYPE, NumberT.INT);
        if(node.equals(resNode)) {
          funcNodeReplaceMap.put(node, (Node)varNode); // f(a) : TEMP_VAR_x
        } else {
          funcNodeReplaceMap.put(node, resNode); // g(f(a)) : g(TEMP_VAR_x1)
          funcNodeReplaceMap.put(resNode, (Node)varNode); // g(TEMP_VAR_x1) : TEMP_VAR_x2
        }
        IRVarInfo varInfo = new VarInfo(scope, varName, IRIntegerType.getInstance(), varNode);

        Scope oldScope = symbolTable.getCurrentScope();
        symbolTable.setScope(scope);
        symbolTable.define(varName, varInfo);
        symbolTable.setScope(oldScope);
      } else {
        if(!node.equals(resNode))  funcNodeReplaceMap.put(node, resNode);
      }
    } else {
      if(!node.equals(resNode))  funcNodeReplaceMap.put(node, resNode);
    }
    return funcNodeReplaceMap;
  }
  
  /**
   * Collect auxiliary list of <code>IRStatement</code>s of 
   * <code>Statement</code> stmt if it has function call node nested inside.
   */
  private List<IRStatement> pickFuncCallFromStmt(IRStatement stmt, CSymbolTable symbolTable) 
      throws RunProcessorException {  
    List<IRStatement> assignStmts = Lists.newArrayList();
    if(stmt.equals(null)) 
      return assignStmts;
    ImmutableList<IRExpression> argExprs = stmt.getOperands();
    List<IRExpression> argExprsRep = Lists.newArrayList();
    LinkedHashMap<Node, Node> pairs = Maps.newLinkedHashMap();
    
    for(IRExpression argExpr : argExprs) {
      Node argNode = argExpr.getSourceNode();
      Scope scope = argExpr.getScope();
      Map<Node, Node> argPairs = replaceFuncCallwithVar(argNode, symbolTable, scope);
      pairs.putAll(argPairs);
      if(argPairs.isEmpty())
        argExprsRep.add(argExpr);
      else {
        while(argPairs.get(argNode) != null)
          argNode = argPairs.get(argNode);
        argExprsRep.add(CExpression.create(argNode, scope));
      }
    }

    for(Entry<Node, Node> pair : pairs.entrySet()) {
      Node keyNode = pair.getKey();
      Node valNode = pair.getValue();
      /* For f(a) = TEMP_VAR_x, add assign statement TEMP_VAR_x := f(a) */
      if(!("FunctionCall".equals(keyNode.getName()) && 
          "PrimaryIdentifier".equals(valNode.getName())))   continue;
      Scope scope = symbolTable.getScope(valNode);
      CExpression keyExpr = CExpression.create(keyNode, scope);
      CExpression valExpr = CExpression.create(valNode, scope);
      
      Node assignNode = substituteNode(stmt.getSourceNode(), valNode, keyNode);
      IRStatement assignStmt = Statement.assign(assignNode, valExpr, keyExpr);
      assignStmts.add(assignStmt);
    }
    if(!pairs.isEmpty()) {
      IRStatement replaceStmt = null;
      Node replaceNode = substituteNode(stmt.getSourceNode(), argExprsRep);
      switch(stmt.getType()) {
      case ASSIGN:
        replaceStmt = Statement.assign(replaceNode, 
            (IRExpressionImpl) argExprsRep.get(0), (IRExpressionImpl) argExprsRep.get(1));
        break;
      case ASSERT:
        replaceStmt = Statement.assertStmt(replaceNode, argExprsRep.get(0)); break;
      case ASSUME:
      case AWAIT:
        replaceStmt = Statement.assumeStmt(replaceNode, argExprsRep.get(0)); break;
      case RETURN:
        replaceStmt = Statement.returnStmt(replaceNode, argExprsRep.get(0)); break;
      case CALL:
        replaceStmt = Statement.functionCall(replaceNode, 
            argExprsRep.get(0), argExprsRep.subList(1, argExprsRep.size())); break;
      default:
        throw new RunProcessorException("Invalid stmt type: " + stmt);
      }
      assignStmts.add(replaceStmt);
    }
    return assignStmts;
  }
 
  /**
   * Substitute the rhs of each element in pathRep with the related element of 
   * pathRmv. The element in pathRep is in form as "TEMP_VAR_0 := addOne(x)". 
   * addOne(x) is created in <code>IRStatement stmt, CSymbolTable symbolTable
   * </code>. Those info is incorrect.
   * 
   * However, pathRmv's element has the corresponding statement - addOne(x) directly 
   * picked from cfg, whose info is correct. Here, we substitute the "addOne(x)" 
   * in pathRep to the "addOne(x)" in pathRmv.
   */
  private List<IRStatement> substitutePath(List<IRStatement> pathRep, List<IRStatement> pathRmv) 
      throws RunProcessorException {
    assert(pathRep.size() == pathRmv.size()) :
      "RunProcessor::substitutePath - invalid size.";
    List<IRStatement> pathRes = Lists.newArrayList();
    int lastIndex = pathRep.size()-1;
    for(int i=0; i<lastIndex; i++) {
      IRStatement stmtRep = pathRep.get(i);
      IRStatement stmtRmv = pathRmv.get(i);
      pathRes.addAll(getStmtForAssignCall(stmtRep, stmtRmv));
    }
    pathRes.add(pathRep.get(lastIndex));
    return pathRes;
  }
  
  /**
   * Check path based on <code>CSymbolTable</code> symbolTable, replace 
   * function call within any <code>Statement</code> and process single 
   * function call <code>Statement</code>.
   */
  private void checkPath(List<IRStatement> path, CSymbolTable symbolTable) 
      throws RunProcessorException {
    IOUtils.debug().pln("Checking path...");
    for(int i=path.size()-1; i>=0; i--) {     
      int oldPostfix = this.TEMP_VAR_POSTFIX;
      IRStatement stmt = path.get(i);
      List<IRStatement> stmtRep = pickFuncCallFromStmt(stmt, symbolTable);
      if(!stmtRep.isEmpty()) {
        List<IRStatement> stmtRmv = Lists.newArrayList();
        for(int j = TEMP_VAR_POSTFIX-oldPostfix; j>=0; j--) {
          int k = i - (TEMP_VAR_POSTFIX - oldPostfix);
          assert(k>=0);
          stmtRmv.add(path.remove(k));
        }
        List<IRStatement> resPath = substitutePath(stmtRep, stmtRmv);
        path.addAll(i-(TEMP_VAR_POSTFIX-oldPostfix), resPath);
        i = i - (TEMP_VAR_POSTFIX-oldPostfix) + resPath.size();
      } else if(stmt.getType().equals(StatementType.CALL)) {
        if(findFuncDeclareNode(stmt) != null) { 
          path.remove(i); // Remove CALL statement
          List<IRStatement> resPath = getStmtForCall(stmt);
          path.addAll(i, resPath);
          i = i + resPath.size();
        } // Else, for undeclared function, do nothing.
      }
    }
  }
  
  /**
   * Add tmpPath into path, before do that, check the tmpPath by call 
   * <code>checkPath(...)</code>, and clear the tmpPath.
   */
  private void addTmpPathToPath(List<IRStatement> path, List<IRStatement> tmpPath, 
      CSymbolTable symbolTable) throws RunProcessorException {
    checkPath(tmpPath, symbolTable);
    path.addAll(tmpPath);
    tmpPath.clear();
  }
  
  /** Remove way points before callPoint from wayPoints, return them. 
   * @throws RunProcessorException */
  private List<Position> waypointsBeforeCall(List<Position> wayPoints) 
      throws RunProcessorException {
    List<Position> resWaypoints = Lists.newArrayList();
    while(!wayPoints.isEmpty()) {
      Position waypoint = wayPoints.get(0);
      if(!waypoint.hasFunctions()) {
        Position pos = wayPoints.remove(0);
        resWaypoints.add(pos);
      }
      else
        break;
    }
    return resWaypoints;
  }
  
  /**
   * Parse the invariant to a
   * @param position
   * @param symbolTable
   * @param invariant
   * @return assume statement
   * @throws RunProcessorException
   */
  private List<IRStatement> processInvariant(IRControlFlowGraph cfg,
      IRBasicBlock block, Position position, 
      CSymbolTable symbolTable) throws RunProcessorException {
    List<IRStatement> stmts = Lists.newArrayList();
    try {
      CSpecParser specParser = new CSpecParser(new StringReader(position.getInvariant()),
          position.getFile().getPath());
      Result specResults = specParser.pCSpecExpression(0);
      Node spec = (Node) specParser.value(specResults);
      
      CExpression argExpr = CExpression.create(spec,symbolTable.getCurrentScope());
      IOUtils.debug().pln(argExpr.toString()).flush();
      
      /** FIXME: CVC4 has incremental support problem, multiple queries are not supported
       * well. If this assertion statement is added, will have invalid memory access inside
       * CVC4*/
      stmts.add(Statement.assertStmt(spec, argExpr));
      
      List<IRStatement> loopPath = Lists.newArrayList();
      
      // Pick all statements from the loop body
      buildPathToPosition(cfg, block, position, loopPath);
      
      // Process havoc statements
      { 
        assert(position.getLoops().size() == 1); // only one loop is specified for the invariant

        List<IRStatement> havocStmts = Lists.newArrayList();
        for(IRStatement stmt : loopPath) {
          if(stmt.getType() == StatementType.ASSIGN) {
            IRExpressionImpl lval = (IRExpressionImpl) ((Statement) stmt).getOperand(0);
            if(stmt == loopPath.get(loopPath.size()-1)) {// last statement
              if(!lval.toString().startsWith(TEST_VAR_PREFIX))
                throw new RunProcessorException("Invalid last statement in the loop.");
              havocStmts.add(stmt);
            } else {
              havocStmts.add(Statement.havoc(lval.getSourceNode(), lval));
            }
          }           
        }
        stmts.addAll(havocStmts);        
      }
      
      stmts.add(Statement.assumeStmt(spec, argExpr));
      stmts.addAll(loopPath);
      stmts.add(Statement.assertStmt(spec, argExpr));
      
    } catch (IOException e) {
      throw new RunProcessorException("Specification parse failure", e);
    } catch (ParseException e) {
      throw new RunProcessorException("Specification parse failure", e);
    }
    return stmts;    
  }
  
  private List<Position> loopPointsUnroll(IRControlFlowGraph cfg, List<Position> wayPoints) 
      throws RunProcessorException {
    List<Position> resWaypoints = Lists.newArrayList();
    for(Position pos : wayPoints) {
      if(pos.hasLoop()) {
        // Clear default iteration times in loop block if users specify iteration times in ctrl file
        cfg.bestBlockForPosition(pos).clearIterTimes();
       
        for(LoopPoint loopPos : pos.getLoops()) { 
          // Ignore loop iteration times when have loop invariant
          if(loopPos.getInvariant() != null) {
//            if(pos.getInvariant() != null)
//              throw new RunProcessorException("Multiple invariants for one loop.");
            pos.setInvariant(loopPos.getInvariant());
            resWaypoints.add(pos);
            continue;
          }
          int iterTimes = loopPos.getIterTimes();
          while(iterTimes>0) {
            resWaypoints.add(pos);
            resWaypoints.addAll(loopPointsUnroll(cfg, loopPos.getWayPoint()));
            iterTimes--;
          }
          
          LoopPoint lastLoopPos = pos.getLoops().get(pos.getLoops().size()-1);
          // if last loop point doesn't contains wayPoint, add iteration times to hit the entry
          // block of the loop and exit
          if(lastLoopPos.getWayPoint().isEmpty()) 
            resWaypoints.add(pos);
        }
      } else {
        resWaypoints.add(pos);
      }
    }
    return resWaypoints;
  }
  
  private List<IRStatement> processRun(IRLocation start, IRLocation end, List<Position> waypoints) 
          throws RunProcessorException {   
    File file = start.getFile();
    CSymbolTable symbolTable = symbolTables.get(file);   
    IRControlFlowGraph cfg = getCFGForLocation(start);
    Scope oldScope = symbolTable.getCurrentScope();
    symbolTable.enterScope(cfg);

    // Start position    
    IRBasicBlock block = cfg.splitAt(start, true);
    List<IRStatement> path = Lists.newArrayList();
    List<IRStatement> tmpPath = Lists.newArrayList();
    
    IOUtils.debug().pln("<startPosition> " + start.toString()).flush();
    if(start instanceof Position)
      processPosition((Position)start, symbolTable, tmpPath);
    addTmpPathToPath(path, tmpPath, symbolTable);
    
    List<Position> wayPoints = loopPointsUnroll(cfg, waypoints);
    
    while(!wayPoints.isEmpty()) {
      // Way points before call position 
      List<Position> tmpWaypoints = waypointsBeforeCall(wayPoints);
      for(Position pos : tmpWaypoints) {
        if (block == null)      break;
        IOUtils.debug().pln("<wayPoint> " + pos.toString()).flush();
        block = buildPathToPosition(cfg, block, pos, tmpPath);
        Scope currScope = symbolTable.getCurrentScope();
        if(block.getScope() != null)   symbolTable.setScope(block.getScope());
        if(pos.getInvariant() != null)
          tmpPath.addAll(processInvariant(cfg, block, pos, symbolTable));
        processPosition(pos, symbolTable, tmpPath);
        symbolTable.setScope(currScope);
        addTmpPathToPath(path, tmpPath, symbolTable);
      }
      
      if(wayPoints.isEmpty())   break;
      
      Position callPos = wayPoints.remove(0);  // call position
      IOUtils.debug().pln("<callPoint> " + callPos.toString()).flush();
  
      // The blocks from last way point to the call position (not include call position)
      IRBasicBlock target = cfg.splitAt(callPos, true); // Split before callPos
      block = buildPathToBlock(cfg, block, target, tmpPath);
      addTmpPathToPath(path, tmpPath, symbolTable);
     
      /* Call position, all stmt in tmpPath are related to the expression in callPos.line. */
      target = cfg.splitAt(callPos, false);
      block = buildPathToBlock(cfg, block, target, tmpPath);      
      IRStatement targetStmt = (Statement) tmpPath.get(tmpPath.size()-1);       
      List<IRStatement> stmtRep = pickFuncCallFromStmt(targetStmt, symbolTable);
      List<IRStatement> stmtRmv = Lists.newArrayList(tmpPath);
      tmpPath.clear();
    
      if(!targetStmt.getType().equals(StatementType.CALL) && stmtRep.isEmpty()) {
        throw new RunProcessorException("Invalid call position: " + callPos);
      }
      
      /* Add targetStmt into stmtRep; while stmtRmv has the same statement. */
      if(stmtRep.isEmpty())     stmtRep.add(targetStmt);
      
      /* Add all the side-effect statements to tmpPath first. For now, the 
       * reason of stmtRep.size > stmtRmv.size is string as an argument of 
       * the function; */
      while(stmtRep.size() < stmtRmv.size()) {
        tmpPath.add(stmtRmv.remove(0));
      }
      
      List<CallPoint> functions = Lists.newArrayList(callPos.getFunctions());
      for(int i=0; i<stmtRep.size(); i++) {
        Statement rep = (Statement) stmtRep.get(i); // TEMP_VAR_0 := addOne(x);
        Statement rmv = (Statement) stmtRmv.get(i); // addOne(x);
        if(i==stmtRep.size()-1 && !rep.getType().equals(StatementType.CALL))
          tmpPath.add(rep);
        else {
          if(functions.isEmpty())
            tmpPath.addAll(collectStmtFromFunction(rmv));
          else {
            String funcName_a = functions.get(0).getFuncName();
            String funcName_b = rmv.getSourceNode().getNode(0).getString(0);         
            tmpPath.addAll(assignArgToParam(rep, rmv));
            if(funcName_a.equals(funcName_b)) { // function mentioned in control file
              CallPoint func = functions.remove(0);
              IRControlFlowGraph funcCfg = getCFGForStatement(rmv);
              IRLocation funcStart = funcCfg.getEntry().getStartLocation();
              IRLocation funcEnd = funcCfg.getExit().getEndLocation();
              tmpPath.addAll(processRun(funcStart, funcEnd, func.getWayPoint()));  
            } else {
              tmpPath.addAll(collectStmtFromFunction(rmv));
            }
          }
          if(rep.getType().equals(StatementType.ASSIGN)) {
            IRStatement returnStmt = tmpPath.remove(tmpPath.size()-1);
            tmpPath.add(replaceReturnStmt(returnStmt, rep));
          }
        }
        path.addAll(tmpPath);
        tmpPath.clear();
      }
      // assert functions.isEmpty() : "RunProcessor::processRun - too many call positions.";
    }
    
    // End position
    if (block == null) {
      throw new RunProcessorException("Function ended before end of run.");
    }
    if (end == null) {
      IRBasicBlock endBlock = buildPathToBlock(cfg, block, cfg.getExit(), tmpPath);
      IOUtils.debug().pln("<endPosition> Null").flush();
      Scope currScope = symbolTable.getCurrentScope();
      if(endBlock.getScope() != null) symbolTable.setScope(endBlock.getScope());
      addTmpPathToPath(path, tmpPath, symbolTable);
      symbolTable.setScope(currScope);
    } else {
      IRBasicBlock endBlock = buildPathToPosition(cfg, block, end, tmpPath);
      IOUtils.debug().pln("<endPosition> " + end.toString()).flush();
      Scope currScope = symbolTable.getCurrentScope();
      if(endBlock.getScope() != null) symbolTable.setScope(endBlock.getScope());
      processPosition((Position)end, symbolTable, tmpPath);
      addTmpPathToPath(path, tmpPath, symbolTable);
      symbolTable.setScope(currScope);
    }
    
    symbolTable.setScope(oldScope);
    
    return path;
  }
  
  /**
   * Substitute the child nodes in srcNode as nodes in order
   * @param srcNode
   * @param nodes
   * @return substituted node
   */
  private Node substituteNode(Node srcNode, Node ... nodes) {
    String srcNodeName = srcNode.getName();
    List<Object> argList = Lists.newArrayList();
    List<Node> candidateList = Lists.newArrayList(nodes);
    for(int i = 0; i < srcNode.size(); i++) {
      Object o = srcNode.get(i);
      if(o instanceof GNode)
        argList.add(candidateList.remove(0));
      else  
        argList.add(srcNode.get(i));
    }
    Node newNode = createNodeWithArgList(srcNodeName, argList);
    newNode.setLocation(srcNode.getLocation());
    return newNode;
  }
  
  /**
   * Substitute the child nodes in srcNode as source nodes of exprs
   * @param srcNode
   * @param exprs
   * @return substituted node
   */
  private Node substituteNode(Node srcNode, List<IRExpression> exprs) {
    String srcNodeName = srcNode.getName();
    List<Object> argList = Lists.newArrayList();
    List<Node> candidateList = Lists.newArrayList();
    for(IRExpression expr : exprs)
      candidateList.add(expr.getSourceNode());
    for(int i = 0; i < srcNode.size(); i++) {
      Object o = srcNode.get(i);
      if(o instanceof GNode)
        argList.add(candidateList.remove(0));
      else  
        argList.add(o);
    }
    Node newNode = createNodeWithArgList(srcNodeName, argList);
    newNode.setLocation(srcNode.getLocation());
    return newNode;
  }
  /**
   * Put argList to operands, since if GNode.create(name, argList), 
   * then new node only has one operand that is the argList. Here, 
   * we want to new node has every arg of argList as operand, 
   * thus the size is desired function, whose argument is Pair
   * @param argList
   * @return a new node
   */
  
  private Node createNodeWithArgList(String name, List<Object> argList) {
    Pair<Object> operands = null;
    for(Object o : argList) {
      Pair<Object> pair = new Pair<Object>(o);
      if(operands == null)  operands = pair;
      else  operands = operands.append(pair);
    }
    GNode newNode = GNode.createFromPair(name, operands);
    return newNode;
  }
  
  public void enableFeasibilityChecking() {
    pathEncoder.setFeasibilityChecking(true);
  }

}