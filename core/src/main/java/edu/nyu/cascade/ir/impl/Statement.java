package edu.nyu.cascade.ir.impl;

import static edu.nyu.cascade.ir.IRStatement.StatementType.DECLARE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ALLOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSERT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSIGN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSUME;
import static edu.nyu.cascade.ir.IRStatement.StatementType.AWAIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALL;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CAST;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CRITICAL_SECTION;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FREE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.HAVOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.NON_CRITICAL_SECTION;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RECEIVE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RELEASE_SEMAPHORE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.REQUEST_SEMAPHORE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RETURN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.SEND;
import static edu.nyu.cascade.ir.IRStatement.StatementType.SKIP;
import static edu.nyu.cascade.ir.IRStatement.StatementType.LIFT_BEGIN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.LIFT_END;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FUNC_ENT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FUNC_EXIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ENUM;

import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

public class Statement implements IRStatement {
  
  public static Statement declare(Node sourceNode, IRExpressionImpl varExpr) {
    return new Statement(sourceNode, DECLARE, varExpr);
  }
  
  public static Statement declareEnum(Node sourceNode, List<? extends IRExpressionImpl> varExprs) {
  	return new Statement(sourceNode, ENUM, varExprs);
  }
	
  public static Statement alloc(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, ALLOC, ptrExpr, sizeExpr);
  }
  
  public static Statement assertStmt(Node sourceNode, IRExpression expr) {
    return new Statement(sourceNode, ASSERT, expr);
  }

  public static Statement assign(Node sourceNode, IRExpressionImpl varExpr,
      IRExpressionImpl valExpr) {
    return new Statement(sourceNode, ASSIGN, varExpr, valExpr);
  }

  public static Statement assumeStmt(Node sourceNode, IRExpression expression) {
    return new Statement(sourceNode, ASSUME, expression);
  }
  
  public static Statement await(Node sourceNode, IRExpressionImpl expr) {
    return new Statement(sourceNode, AWAIT, expr);
  }

  public static Statement create(Node sourceNode) {
    return new Statement(sourceNode);
  }

  public static Statement critical(Node sourceNode) {
    return new Statement(sourceNode, CRITICAL_SECTION);
  }
  
  public static Statement cast(Node sourceNode, IRExpression typeExpr, IRExpression argExpr) {
    return new Statement(sourceNode, CAST, typeExpr, argExpr);
  }
  
  public static Statement functionCall(Node sourceNode, IRExpression funExpr,
      List<? extends IRExpression> args) {
    List<IRExpression> operands;
    if(args == null){
      operands = ImmutableList.<IRExpression> builder().add(funExpr).build();
    } else {
      operands = ImmutableList.<IRExpression> builder().add(funExpr).addAll(args).build();
    }
        
    return new Statement(sourceNode, CALL, operands);
  }
  
  public static Statement free(Node sourceNode, IRExpressionImpl ptrExpr) {
    return new Statement(sourceNode, FREE, ptrExpr);
  }
  
  public static Statement havoc(Node sourceNode, IRExpression varExpr) {
    return new Statement(sourceNode, HAVOC, varExpr);
  }
  
  public static Statement nonCritical(Node sourceNode) {
    return new Statement(sourceNode, NON_CRITICAL_SECTION);
  }
  
  public static Statement receives(GNode node, IRExpression channel,
      IRExpression value) {
    return new Statement(node, RECEIVE, channel, value);
  }

  public static Statement release(Node node, IRExpression arg) {
    return new Statement(node, RELEASE_SEMAPHORE, arg);
  }

  public static Statement request(Node node, IRExpression arg) {
    return new Statement(node, REQUEST_SEMAPHORE, arg);
  }
  
  public static Statement returnStmt(Node sourceNode, IRExpression val) {
    return new Statement(sourceNode, RETURN, val);
  }
  
  public static Statement returnStmt(Node sourceNode) {
    return new Statement(sourceNode, RETURN);
  }
  
  public static Statement scopeEnt(Node sourceNode) {
  	return new Statement(sourceNode, FUNC_ENT);
  }
  
  public static Statement scopeExit(String scopeName) {
  	Statement stmt = new Statement(null, FUNC_EXIT);
  	stmt.setProperty(Identifiers.SCOPE, scopeName);
  	return stmt;
  }

  public static Statement sends(GNode node, IRExpression channel,
      IRExpression value) {
    return new Statement(node, SEND, channel, value);
  }
  
  public static Statement skip(Node sourceNode) {
    return new Statement(sourceNode, SKIP);
  }
  
  /**
   * The statement to mark the begin of statements
   * with duplicated scopes
   * 
   * @param loc
   * @return
   */
  public static Statement LiftBegin() {
  	return new Statement(null, LIFT_BEGIN);
  }
  
  /**
   * The statement to mark the end of statements
   * with duplicated scopes
   * 
   * @param loc
   * @return
   */
  public static Statement LiftEnd() {
  	return new Statement(null, LIFT_END);
  }
  
  private Node sourceNode;

  private StatementType type;

  private ImmutableList<IRExpression> operands;

  private final IRLocation location;
  
  private final Set<String> preLabels, postLabels;
  
  private final Map<String, Object> properties;
  
  protected Statement(Node sourceNode) {
    this(sourceNode, null);
  }
  
  protected Statement(IRLocation loc, StatementType type) {
    this.type = type;
    this.location = loc;
    this.preLabels = Collections.emptySet();
    this.postLabels = Collections.emptySet();
    this.properties = Maps.newHashMap();
  }
  
  protected Statement(Node sourceNode, StatementType type,
      IRExpression... operands) {
    this.sourceNode = sourceNode;
    this.type = type;
    this.operands = ImmutableList.copyOf(Arrays.asList(operands));
    this.location = IRLocations.ofNode(sourceNode);
    this.preLabels = Sets.newHashSet();
    this.postLabels = Sets.newHashSet();
    this.properties = Maps.newHashMap();
  }
  
  protected Statement(Node sourceNode, StatementType type,
      List<? extends IRExpression> operands) {
    this.sourceNode = sourceNode;
    this.type = type;
    this.operands = ImmutableList.copyOf(operands);
    this.location = IRLocations.ofNode(sourceNode);
    this.preLabels = Sets.newHashSet();
    this.postLabels = Sets.newHashSet();
    this.properties = Maps.newHashMap();
  }
  
  @Override
  public boolean hasLocation() {
  	return location != null;
  }
  
  @Override
  public void setProperty(String name, Object o) {
  	properties.put(name, o);
  }
  
  @Override
  public Object getProperty(String name) {
  	Preconditions.checkArgument(hasProperty(name));
  	return properties.get(name);
  }
  
  @Override
  public boolean hasProperty(String name) {
  	return properties.containsKey(name);
  }
  
  @Override
  public void addPostLabel(String label) { 
    postLabels.add(label);
  }
  
  @Override
  public void addPostLabels(Iterable<String> labels) { 
    Iterables.addAll(postLabels,labels);
  }

  @Override
  public void addPreLabel(String label) { 
    preLabels.add(label);
  }

  @Override
  public void addPreLabels(Iterable<String> labels) { 
    Iterables.addAll(preLabels,labels);
  }
  
  @Override
  public IRLocation getLocation() {
    return location;
  }

  @Override
  public StateExpressionClosure getOperand(ExpressionEncoder encoder,int i)  {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperand(i).toExpression(encoder);
  }

  @Override
  public IRExpression getOperand(int i) {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperands().get(i);
  }

  @Override
  public ImmutableList<IRExpression> getOperands() {
    return ImmutableList.copyOf(operands);
  }

  @Override
  public ImmutableList<StateExpressionClosure> getOperands(final ExpressionEncoder encoder) {
    ImmutableList.Builder<StateExpressionClosure> listBuilder = ImmutableList.builder();
    for( IRExpression e : operands ) {
      listBuilder.add( e.toExpression(encoder) );
    }
    return listBuilder.build();
  }

  @Override
  public StateExpression getPostCondition(PathEncoding factory, StateExpression prefix) {
    switch (getType()) {
    case DECLARE:
    	return factory.declare(prefix, getOperand(0));
    case ENUM:
    	return factory.declareEnum(prefix, getOperands().toArray(new IRExpression[operands.size()]));
    case ASSIGN: 
      return factory.assign(prefix, getOperand(0), getOperand(1));
//    case ASSERT:
//      return factory.check(prefix, getOperand(0));
    case ASSUME:
    case AWAIT:
      return factory.assume(prefix, getOperand(0));
    case ALLOC:
        return factory.alloc(prefix, getOperand(0), getOperand(1));
    case FREE:
      return factory.free(prefix, getOperand(0));
    case HAVOC:
      return factory.havoc(prefix, getOperand(0));

      /* CALL statement is used to analyze scope-sensitive partition memory
       * model. It is useful to indicate the exact scope of caller node;
       * and particularly useful in the function call without parameter.
       * 
       * Sample code:
       *   if(...) {
       *      ... // last statement before test()
       *   }
       *   test();
       */
    case CALL:
    	return factory.call(prefix, getOperand(0).toString(), 
    			getOperands().subList(1, operands.size()).toArray(new IRExpression[operands.size()-1]));
    case LIFT_BEGIN:
    	CScopeAnalyzer.liftStatementsBegin();
    	break;
    case LIFT_END:
    	CScopeAnalyzer.liftStatementsEnd();
    	break;
    case FUNC_ENT:
    	String scopeName = CType.getScopeName(sourceNode);
    	CScopeAnalyzer.pushScope(scopeName);
    	break;
    case FUNC_EXIT:
    	CScopeAnalyzer.popScope();
    	break;
    case CRITICAL_SECTION:
    case NON_CRITICAL_SECTION:
    case CAST:
    case SKIP:
    default:
      IOUtils.debug().pln(
          "Statement.getPostCondition: Ignoring statement type: "
              + getType());
    }
    return factory.noop(prefix);
  }
  
  @Override
  public ImmutableSet<String> getPostLabels() {
    return ImmutableSet.copyOf(postLabels);
  }

  @Override
  public StateExpressionClosure getPreCondition(ExpressionEncoder  encoder) {
    switch (getType()) {
    case ASSERT: {
      return getOperand(0).toBoolean(encoder);
    }
    default:
      return null;
    }
  }

  @Override
  public ImmutableSet<String> getPreLabels() {
    return ImmutableSet.copyOf(preLabels);
  }
  
  @Override
  public Node getSourceNode() {
    return sourceNode;
  }

  @Override
  public StatementType getType() {
    return type;
  }

  @Override
  public String toString() {
    if (getType() == null) {
      return sourceNode.getName();
    }
    switch (getType()) {
    case DECLARE:
    	return "declare " + getOperand(0);
    case ALLOC:
      return getOperand(0) + " := malloc(" + getOperand(1) + ")";
    case ASSERT:
      return "assert " + getOperand(0);
    case ASSIGN:
      return getOperand(0) + " := " + getOperand(1);

    case ASSUME:
      return "assume " + getOperand(0);
    case AWAIT:
      return "await " + getOperand(0);

    case CALL:
      Iterator<IRExpression> opIter = getOperands().iterator();
      assert (opIter.hasNext()); // function expression
      IRExpression funExpr = opIter.next();
      String result = funExpr.toString() + "(";
      while (opIter.hasNext()) {
        IRExpression arg = opIter.next();
        result += arg.toString();
        if (opIter.hasNext()) {
          result += ",";
        }
      }
      result += ")";
      return result;

    case CRITICAL_SECTION:
      return "critical";

    case FREE: 
      return "free " + getOperand(0);
      
    case HAVOC:
      return "havoc " + getOperand(0);
      
    case NON_CRITICAL_SECTION:
      return "noncritical";
    
    case RELEASE_SEMAPHORE:
      return "release " + getOperand(0);
      
    case REQUEST_SEMAPHORE:
      return "request " + getOperand(0);

    case RETURN:
    	if(operands.isEmpty())
    		return "return ";
    	else
    		return "return " + getOperand(0);
    case CAST:
      return "cast (" + getOperand(0) + ")" + getOperand(1);
      
    case SKIP:
      return "skip";
    	
    case LIFT_BEGIN:
    	return "lift begin";
   
    case LIFT_END:
    	return "lift end";
    
    case FUNC_ENT:
    	return "enter (" + CType.getScopeName(sourceNode) + ")";
    
    case FUNC_EXIT:
    	return "exit (" + getProperty(Identifiers.SCOPE) + ")";
    
    case ENUM:	
    	return new StringBuilder().append("enum ")
    	.append(getOperands()).toString();
    	
    default:
      return sourceNode.getName();
    }
  }
}
