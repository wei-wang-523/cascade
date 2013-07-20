package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.Iterator;
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
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;
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
//import edu.nyu.cascade.ir.expr.DynamicPathEncoding;
import edu.nyu.cascade.ir.expr.SimplePathEncoding;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.VarInfo;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.c.CSpecParser;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */
final class PathSeqEncoder {
  private PathEncoding pathEncoding;  // the encoding to use for the path
  private Expression path;  // the expression representing the encoded path 
  private boolean runIsValid, runIsFeasible, checkFeasibility;

  PathSeqEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathSeqEncoder create(PathEncoding encoding) {
    return new PathSeqEncoder(encoding);
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
class RunSeqProcessor implements RunProcessor {
  
  public RunSeqProcessor(Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs, CAnalyzer cAnalyzer,
      CExpressionEncoder exprEncoder)
      throws RunProcessorException {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.cAnalyzer = cAnalyzer;
//    this.pathEncoder = PathSeqEncoder.create(DynamicPathEncoding.create(exprEncoder));
    this.pathEncoder = PathSeqEncoder.create(SimplePathEncoding.create(exprEncoder));
    this.TEMP_VAR_POSTFIX = 0;
  }
  
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final CAnalyzer cAnalyzer;
  private final PathSeqEncoder pathEncoder;
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
  public boolean process(Run run) throws RunProcessorException {
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

  /** Incorporate the command for the given position into the given path. */
  List<IRStatement> processPosition(Position position, CSymbolTable symbolTable) 
      throws RunProcessorException {
    Preconditions.checkArgument(position != null);
    List<IRStatement> path = Lists.newArrayList();
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
    
    if(path.isEmpty())  return null;
    
    return path;
  }

  /**
   * Find a path in the CFG to the given position and add the statements along
   * the path to the List path. If more than one path
   * to the position exists in the CFG, one will be chosen arbitrarily. Raises
   * PathBuilderException if no path to the position can be found.
   * 
   * The behavior if position is not within a basic block depends
   * on the property position.matchAfter: if true, the
   * path will terminate at the nearest subsequent block; if false,
   * it will terminate after the nearest preceding block.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   */
  
  private Pair<? extends IRBasicBlock, ? extends IRBasicBlock> getTargetBlock(
      IRControlFlowGraph cfg, IRBasicBlock block, IRLocation pos) 
          throws RunProcessorException {
    Pair<? extends IRBasicBlock, ? extends IRBasicBlock> target;
    if(pos instanceof Position) {
      target = cfg.splitAt(pos, InsertionType.BEFORE.equals(
          ((Position)pos).getInsertionType()));
    } else {
      throw new RunProcessorException("Bad position: " + pos);
    }      

    if( target==null ) {
      throw new RunProcessorException("Bad position: " + pos);
    }
    IOUtils.debug().pln("Searching for path:").incr().pln(
        "Source: " + block + "\nTarget: " + target).decr().flush();
    return target;
  }

  /**
   * Find a path in the CFG to the given start block and target block, and add
   * the statements along the path to the list path. 
   * If more than one path to the position exists in the CFG, one will be chosen
   * arbitrarily. Raises PathBuilderException if no path can be 
   * found.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   */
  
  private List<IRStatement> buildPathToBlock(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target) 
          throws RunProcessorException {
    List<IRStatement> path = Lists.newArrayList();
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
    if(start.equals(target) && 
        (start.getType().equals(IRBasicBlock.Type.LOOP) || 
            (start.getType()).equals(IRBasicBlock.Type.SWITCH))) {
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
    if((start.equals(target) && 
        (start.getType().equals(IRBasicBlock.Type.LOOP) || 
            (start.getType()).equals(IRBasicBlock.Type.SWITCH)))) {
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
        path.addAll(buildPathToBlock(cfg, u, u));
        iterTimes--;
      }
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    
    path.addAll(target.getStatements());
    IOUtils.debug().decr().flush();

    return path;
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

  /** Find the CFG for function call Statement. */
  private IRControlFlowGraph getCFGForStatement(IRStatement stmt) 
      throws RunProcessorException {
    Node bestNode = findFuncDeclareNode(stmt);
    IRControlFlowGraph cfg = cfgs.get(bestNode);
    return cfg;
  }
  
  /** Get the function declare Node for the function call statement. */
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
      IOUtils.debug().pln("Cannot find the function declaration node for " + stmt);
    }
    return bestNode;
  }
  
  private Node findFuncDeclareNode (CSymbolTable symbolTable, String funcName) 
      throws RunProcessorException {
    IRVarInfo info = symbolTable.lookup(funcName);
    if(info == null)    return null; /* For undeclared function. */
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
      /* FIXME: continue find in the parent scope or stays at root scope initially? */
      IOUtils.debug().pln("Cannot find the function declaration node for " + funcName);
    }
    return bestNode;
  }
  
  /** 
   * Collect a list Statement from function body, func is the function
   * section in the control file, might with loop position and way points
   * nested inside.
   */
  private List<IRStatement> collectStmtFromFunction(IRStatement stmt) 
      throws RunProcessorException {
    return collectStmtFromFunction(stmt, null);
  }
  
  private List<IRStatement> collectStmtFromFunction(IRStatement stmt, CallPoint func) 
      throws RunProcessorException {
    List<IRStatement> path = Lists.newArrayList();
    IRControlFlowGraph funcCfg = getCFGForStatement(stmt);
    if(funcCfg == null) {
      System.err.println("Cannot find cfg for statement: " + stmt);
    } else {     
      IRLocation funcStart = funcCfg.getEntry().getStartLocation();
      IRLocation funcEnd = funcCfg.getExit().getEndLocation();
      List<Position> waypoints = null;
      if(func != null) waypoints = func.getWayPoint();
      path.addAll(processRun(funcStart, funcEnd, waypoints));
    }
    return path;
  }
  
  /** 
   * Create the assign statements from arguments to parameters. 
   * E.g. repStmt: TEMP_VAR_1 := addOne(x, TEMP_VAR_0), rmvStmt: addOne(x,returnOne());
   * repStmt is a flattened version of function call stmt, rmvStmt is not.
   * It's the reason why both are required arguments.
   */
  private List<IRStatement> assignArgToParam(IRStatement stmt) 
      throws RunProcessorException {
    return assignArgToParam(null, stmt); 
  }
  
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
          if(arg_assign.getName().equals("CastExpression"))  arg_assign = arg_assign.getNode(1);
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
  
  /**
   * Function inlining for call statement
   * 1) assign statements to assign arguments to parameters, 
   * 2) statements collected from the function body.
   * @throws RunProcessorException 
   */
  private List<IRStatement> getStmtForCall(IRStatement stmt) throws RunProcessorException {
    return getStmtForCall(stmt, null);
  }
  
  private List<IRStatement> getStmtForCall(IRStatement stmt, CallPoint func) throws RunProcessorException {
    if(!stmt.getType().equals(StatementType.CALL)) {
      throw new RunProcessorException("Invalid statement type: " + stmt);
    }
    List<IRStatement> func_path = assignArgToParam(stmt);
    if(func != null)    func_path.addAll(collectStmtFromFunction(stmt, func));
    else                func_path.addAll(collectStmtFromFunction(stmt));
    return func_path;
  }
    
  /**
   * Replace all the function call node with a temporary var node, and return the 
   * function call node list to keep the insertion order of the "pairs", otherwise, 
   * "pairs" will be arbitrary order.
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
        if(node.hasProperty(xtc.Constants.TYPE))
          varNode.setProperty(xtc.Constants.TYPE, node.getProperty(xtc.Constants.TYPE));
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
  
  /** Flatten function call statement if it has function call nested inside. */
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
  
  private CallPoint findCallPointForStmt(IRStatement stmt, List<CallPoint> callPoints) {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    int count = 0;
    for(int i = 0; i < callPoints.size(); i++) {
      CallPoint call = callPoints.get(i);
      String name1 = call.getFuncName();
      String name2 = ((Statement) stmt).getOperand(0).toString();
      if(name1.equals(name2)) {
        if(call.getFuncId().intValue() == ++count) return call;
      }
    }
    return null;
  }
  
  private boolean hasFunctionCall(IRStatement stmt) throws RunProcessorException {
    File file = stmt.getLocation().getFile();
    CSymbolTable symbolTable = symbolTables.get(file);
    return hasFunctionCall(symbolTable, stmt.getSourceNode());
  }
  
  private boolean hasFunctionCall(CSymbolTable symbolTable, Node srcNode) 
      throws RunProcessorException {
    if(srcNode.getName().equals("FunctionCall")) {
      String funcName = srcNode.getNode(0).getString(0);
      /* Do not touch the reserved functions */
      if(ReservedFunctions.contains(funcName))  return false;
      Node funcNode = findFuncDeclareNode(symbolTable, funcName);
      return (funcNode != null);
    }
    for(int i=0; i<srcNode.size(); i++) {
      Object arg = srcNode.get(i);
      if(arg instanceof Node)
        if(hasFunctionCall(symbolTable, (Node) arg))
          return true;
    }
    return false;
  }
  
  /** Replace the last return statement as assign statement. */
  private IRStatement replaceReturnStmt(IRStatement returnStmt, IRStatement assignStmt) {
    Preconditions.checkArgument(returnStmt.getType().equals(StatementType.RETURN));
    IRExpressionImpl lExpr = (IRExpressionImpl) ((Statement) assignStmt).getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) ((Statement) returnStmt).getOperand(0);
    Node assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }
  
  /**
   * Function inlining for call statement
   * 1) assign statements to assign arguments to parameters, 
   * 2) statements collected from the function body.
   * 3) return statement
   */
  private List<IRStatement> getStmtForAssignCallStmt(IRStatement lhsStmt, IRStatement rhsStmt, CallPoint func) 
      throws RunProcessorException {
    List<IRStatement> paramPassStmts = assignArgToParam(lhsStmt, rhsStmt);
    List<IRStatement> funcStmts = collectStmtFromFunction(rhsStmt, func);
    funcStmts.addAll(0, paramPassStmts);
    
    /* replace all the return statements. */
    IRStatement lastStmt = funcStmts.get(funcStmts.size()-1);
    if(lastStmt.getType().equals(StatementType.RETURN)) {
      IRStatement assignResult = replaceReturnStmt(lastStmt, lhsStmt);
      funcStmts.set(funcStmts.size()-1, assignResult);
    }
    return funcStmts;
  }
  
  private List<IRStatement> getStmtForAllAssignCallStmt(List<IRStatement> pathRep, List<IRStatement> pathRmv) 
      throws RunProcessorException {
    return getStmtForAllAssignCallStmt(pathRep, pathRmv, null);
  }
  
  private List<IRStatement> getStmtForAllAssignCallStmt(List<IRStatement> pathRep, List<IRStatement> pathRmv, 
      Iterable<CallPoint> funcs) throws RunProcessorException {
    Preconditions.checkArgument(pathRep.size() == pathRmv.size());
    
    List<CallPoint> funcs_copy = null;
    if(funcs != null)   funcs_copy = Lists.newArrayList(funcs);
    
    List<IRStatement> path = null;
    int lastIndex = pathRep.size()-1;
    for(int i=0; i<lastIndex; i++) {
      IRStatement stmtRep = pathRep.get(i);
      IRStatement stmtRmv = pathRmv.get(i);
      CallPoint func = null;
      if(funcs_copy != null) {
        Node funcNode = stmtRmv.getSourceNode();
        assert(funcNode.getName().equals("FunctionCall") 
            && funcNode.getNode(0).getName().equals("PrimaryIdentifier"));
        String funcName = funcNode.getNode(0).getString(0);
        Iterator<CallPoint> itr = funcs_copy.iterator();
        while(itr.hasNext()) {
          CallPoint callPos = itr.next();
          if(callPos.getFuncName().equals(funcName)) {
            func = callPos;
            itr.remove();
            break;
          }
        }
      }
      List<IRStatement> tmpPath = getStmtForAssignCallStmt(stmtRep, stmtRmv, func);
      if(path == null)     path = tmpPath;
      else                 path.addAll(tmpPath);
    }
    
    if(path == null)   throw new RunProcessorException("Invalid path.");
    path.add(pathRep.get(lastIndex));
    return path;
  }
 
  /**
   * If callPos is not null, it means we are process the function call statement with 
   * specification of the symbolic run in the control file; and the path is the 
   * statements flatten from that single function call statement.
   */
  private List<IRStatement> functionInline(CSymbolTable symbolTable, List<IRStatement> path, 
      List<Position> callPos) throws RunProcessorException {
    Preconditions.checkArgument(path != null);
    IOUtils.debug().pln("Checking path...");
    List<IRStatement> resPath = Lists.newArrayList();
    
    Iterator<Position> callPosItr = null; 
    Position candidatePosition = null;
    if(callPos != null) {
      callPosItr = Lists.reverse(callPos).iterator();
      if(callPosItr.hasNext())    candidatePosition = callPosItr.next();
    }
    
    while(path != null && !path.isEmpty()) {
      
      int lastIndex = path.size()-1;
      IRStatement last_stmt = path.get(lastIndex);
            
      /* function call statement f(x) with declared function */
      if(last_stmt.getType().equals(StatementType.CALL) && 
          findFuncDeclareNode(last_stmt) != null) {
        
        IRStatement funcCallStmt = last_stmt;
        int splitIndex = lastIndex;
        
        Position callPosition = null;
        if(candidatePosition != null) {
          if(candidatePosition.getLine() == last_stmt.getLocation().getLine()) {
            callPosition = candidatePosition;
            if(callPosItr.hasNext()) candidatePosition = callPosItr.next();
          }
        }
        
        List<IRStatement> stmtRep = pickFuncCallFromStmt(last_stmt, symbolTable);
        /* special case function with function as argument f(g(x), 1) */
        if(stmtRep != null && !stmtRep.isEmpty()) { 
          splitIndex = lastIndex - stmtRep.size() + 1;
          funcCallStmt = stmtRep.get(stmtRep.size()-1);
        }
        path = path.subList(0, splitIndex);
        
        List<IRStatement> callPath = null;
        if(callPosition != null) {
          CallPoint call = findCallPointForStmt(funcCallStmt, callPosition.getFunctions());
          callPath = getStmtForCall(funcCallStmt, call);
        } else {
          callPath = getStmtForCall(funcCallStmt);
        }
        resPath.addAll(0, callPath);
      }
      
      /* assign statement with function call as rhs y = f(x) */
      else if(hasFunctionCall(last_stmt)) {
        List<IRStatement> stmtRep = pickFuncCallFromStmt(last_stmt, symbolTable);
        int splitIndex = lastIndex - stmtRep.size() + 1;     
        List<IRStatement> funcPath = path.subList(splitIndex, path.size());
        path = path.subList(0, splitIndex);  
        List<IRStatement> callPath = null;
        
        Position callPosition = null;
        if(candidatePosition != null) {
          if(candidatePosition.getLine() == last_stmt.getLocation().getLine()) {
            callPosition = candidatePosition;
            if(callPosItr.hasNext()) candidatePosition = callPosItr.next();
          }
        }
        
        if(callPosition != null) {
          callPath = getStmtForAllAssignCallStmt(stmtRep, funcPath, callPosition.getFunctions());
        } else {
          callPath = getStmtForAllAssignCallStmt(stmtRep, funcPath);
        }
        resPath.addAll(0, callPath);
      } 
      
      /* other statements keep unchanged */
      else {
        int currIndex = lastIndex;
        while(currIndex >= 0) {
          IRStatement stmt = path.get(currIndex);
          if(stmt.getType().equals(StatementType.CALL) && 
              findFuncDeclareNode(stmt) != null)
            break;
          else if(hasFunctionCall(stmt))
            break;
          else
            currIndex--;
        }

        int splitIndex = currIndex + 1;
        List<IRStatement> tmpPath = path.subList(splitIndex, path.size());
        path = path.subList(0, splitIndex);
        resPath.addAll(0, tmpPath);
      }
    }
    return resPath;
  }
  
  /** Parse the invariant of loop. */
  private List<IRStatement> processInvariant(IRControlFlowGraph cfg, Position position, 
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
      
      // Pick all statements from the loop body
      List<Position> wayPoints = position.getLoops().iterator().next().getWayPoint();
      
      List<IRStatement> loopPath = processRun(position, position, wayPoints);
      
      // Process havoc statements
      { 
        /* only one loop is specified for the invariant */
        assert(position.getLoops().size() == 1); 

        List<IRStatement> havocStmts = Lists.newArrayList();
        /* First statement is conditional guard variable assignment statement*/
        for(IRStatement stmt : loopPath.subList(1, loopPath.size())) {
          if(stmt.getType() == StatementType.ASSIGN) {
            IRExpressionImpl lval = (IRExpressionImpl) ((Statement) stmt).getOperand(0);
            havocStmts.add(Statement.havoc(lval.getSourceNode(), lval));
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
    Preconditions.checkArgument(wayPoints != null);
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
    
    List<IRStatement> path = Lists.newArrayList();
    List<IRStatement> startPath = null, endPath = null;
    IRBasicBlock block = null;
    
    // Start position  
    {    
      IOUtils.debug().pln("<startPosition> " + start.toString()).flush();
      if(start instanceof Position) {
        startPath = processPosition((Position)start, symbolTable);
      }    
      Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = cfg.splitAt(start, true);
      block = pair.snd();
    }
    
    List<Position> unrollWayPoints = null;
    if(waypoints != null) { 
      unrollWayPoints = loopPointsUnroll(cfg, waypoints);
      
      for(Position pos : unrollWayPoints) {
        if (block == null)      break;
        IOUtils.debug().pln("<wayPoint> " + pos.toString()).flush();
        
        Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = 
            getTargetBlock(cfg, block, pos);
        IRBasicBlock target = pair.fst();
        List<IRStatement> wayPath = buildPathToBlock(cfg, block, target);
        block = pair.snd();
        
        Scope currScope = symbolTable.getCurrentScope();
        if(block.getScope() != null)   symbolTable.setScope(block.getScope());
        if(pos.getInvariant() != null) {
          List<IRStatement> invarantPath = processInvariant(cfg, pos, symbolTable);
          block = cfg.splitAt(pos, false).snd();
          wayPath.addAll(invarantPath);
        }
        
        List<IRStatement> posPath = processPosition(pos, symbolTable);
//        if(InsertionType.BEFORE.equals(((Position)pos).getInsertionType())) {
//          wayPath.addAll(0, posPath);
//        } else {
        if(posPath != null) wayPath.addAll(posPath);
//        }
        symbolTable.setScope(currScope);
        
        path.addAll(wayPath);
      }
    }
    
    // End position
    if (block == null)
      throw new RunProcessorException("Function ended before end of run.");
    
    { 
      IRBasicBlock endBlock;
      
      if (end == null) {
        endBlock = cfg.getExit();
        IOUtils.debug().pln("<endPosition> Null").flush();
      } else {
        Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = 
            getTargetBlock(cfg, block, end);
        endBlock = pair.snd();
        IOUtils.debug().pln("<endPosition> " + end.toString()).flush();
        endPath = processPosition((Position) end, symbolTable);
      }
      List<IRStatement> tmpPath = buildPathToBlock(cfg, block, endBlock);
      Scope currScope = symbolTable.getCurrentScope();      
      if(endBlock.getScope() != null) symbolTable.setScope(endBlock.getScope());
      
      path.addAll(tmpPath);
      symbolTable.setScope(currScope);
    }
    
    if(startPath != null) path.addAll(0, startPath);
    if(endPath != null) path.addAll(endPath);
     
    if(unrollWayPoints != null) {
      Builder<Position> builder = new ImmutableList.Builder<Position>();
      for(Position waypoint : unrollWayPoints) {
        if(waypoint.hasFunctions())
          builder.add(waypoint);
      }
      path = functionInline(symbolTable, path, builder.build());
    }
    
    symbolTable.setScope(oldScope);
    
    return path;
  }
  
  /**
   * Substitute the child nodes in srcNode as nodes in order
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
   * Put argList to operands, since if use GNode.create(name, argList), 
   * then newly created node has only one operand - argList. Here, 
   * we want to new node has multiple operands, each operand is an arg of argList, 
   * thus we use GNode.create(name, operands), where operands is with type
   * Pair<? extends Object>.
   */  
  private Node createNodeWithArgList(String name, List<Object> argList) {
    xtc.util.Pair<Object> operands = null;
    for(Object o : argList) {
      xtc.util.Pair<Object> pair = new xtc.util.Pair<Object>(o);
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