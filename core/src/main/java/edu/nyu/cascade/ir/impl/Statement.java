package edu.nyu.cascade.ir.impl;

import static edu.nyu.cascade.ir.IRStatement.StatementType.DECLARE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.INIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.MALLOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALLOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ALLOCA;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSERT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSIGN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSUME;
import static edu.nyu.cascade.ir.IRStatement.StatementType.AWAIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALL;
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
import static edu.nyu.cascade.ir.IRStatement.StatementType.FUNC_ENT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FUNC_EXIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.DECLARE_VAR_ARRAY;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.Identifiers;

public class Statement implements IRStatement {

	public static Statement declare(Node sourceNode, IRExpressionImpl varExpr) {
    return new Statement(sourceNode, DECLARE, varExpr);
  }
	
	public static Statement declareVarArray(Node sourceNode, IRExpressionImpl varExpr, IRExpression sizeExpr) {
		return new Statement(sourceNode, DECLARE_VAR_ARRAY, varExpr, sizeExpr);
	}
	
  public static Statement malloc(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, MALLOC, ptrExpr, sizeExpr);
  }
  
  public static Statement calloc(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl nitemExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, CALLOC, ptrExpr, nitemExpr, sizeExpr);
  }
  
  public static Statement alloca(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, ALLOCA, ptrExpr, sizeExpr);
  }
  
  public static Statement assertStmt(Node sourceNode, IRExpression expr) {
    return new Statement(sourceNode, ASSERT, expr);
  }

  public static Statement assign(Node sourceNode, IRExpressionImpl varExpr,
      IRExpressionImpl valExpr) {
    return new Statement(sourceNode, ASSIGN, varExpr, valExpr);
  }
  
  public static Statement initialize(Node sourceNode, IRExpressionImpl varExpr, IRExpressionImpl valExpr) {
    return new Statement(sourceNode, INIT, varExpr, valExpr);
  }

  public static Statement assumeStmt(Node sourceNode, IRExpression expression, boolean guard) {
    Statement stmt = new Statement(sourceNode, ASSUME, expression);
    stmt.setProperty(Identifiers.GUARD, guard);
    return stmt;
  }
  
  public static Statement await(Node sourceNode, IRExpressionImpl expr) {
    return new Statement(sourceNode, AWAIT, expr);
  }

  public static Statement critical(Node sourceNode) {
    return new Statement(sourceNode, CRITICAL_SECTION);
  }
  
  public static Statement functionCall(Node sourceNode, IRExpression funExpr,
      IRExpression retExpr, List<? extends IRExpression> args) {
    ImmutableList.Builder<IRExpression> builder = ImmutableList.builder();
    builder.add(funExpr);
    if(retExpr != null) builder.add(retExpr);
    if(args != null)	builder.addAll(args);
    return new Statement(sourceNode, CALL, builder.build());
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
  
  public static Statement scopeEnt(Node sourceNode, String scopeName) {
  	Statement stmt = new Statement(sourceNode, FUNC_ENT);
  	stmt.setProperty(Identifiers.SCOPE, scopeName);
  	return stmt;
  }
  
  public static Statement scopeExit(Node sourceNode, String scopeName) {
  	Statement stmt = new Statement(sourceNode, FUNC_EXIT);
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
  
  private Node sourceNode;

  private StatementType type;

  private ImmutableList<IRExpression> operands;

  private final IRLocation location;
  
  private final Set<String> preLabels, postLabels;
  
  private final Map<String, Object> properties;
  
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
  
  protected Statement(Node sourceNode, StatementType type,
      IRExpression... operands) {
    this(sourceNode, type, Lists.newArrayList(operands));
  }
  
  @Override
  public IRStatement clone() {
  	Statement copy = new Statement(sourceNode, type, operands);
  	copy.properties.putAll(properties);
  	copy.preLabels.addAll(preLabels);
  	copy.postLabels.addAll(postLabels);
  	return copy;
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
  public IRExpression getOperand(int i) {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperands().get(i);
  }

  @Override
  public ImmutableList<IRExpression> getOperands() {
    return ImmutableList.copyOf(operands);
  }
  
  @Override
  public ImmutableSet<String> getPostLabels() {
    return ImmutableSet.copyOf(postLabels);
  }
  
  @Override
  public boolean hasPreLabel(String label) {
  	return preLabels.contains(label);
  }
  
  @Override
  public boolean hasPostLabel(String label) {
  	return postLabels.contains(label);
  }

  @Override
  public Expression getPreCondition(StateExpression pre, ExpressionEncoder encoder) {
    switch (getType()) {
    case ASSERT: {
      return getOperand(0).toBoolean(pre, encoder);
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
    case DECLARE_VAR_ARRAY:
    	return "declare " + getOperand(0) + "[" + getOperand(1) + "]"; 
    case MALLOC:
      return getOperand(0) + " := malloc(" + getOperand(1) + ")";
    case CALLOC:
      return getOperand(0) + " := calloc(" + getOperand(1) + ", " +  getOperand(2) + ")";
    case ALLOCA:
      return getOperand(0) + " := alloca(" + getOperand(1) + ")";    
    case ASSERT:
      return "assert " + getOperand(0);
    case INIT: 
    	return getOperand(0) + " := " + getOperand(1);
    case ASSIGN:
    	return getOperand(0) + " := " + getOperand(1);
    case ASSUME:
      return "assume " + getOperand(0);
    case AWAIT:
      return "await " + getOperand(0);

    case CALL:
    	StringBuilder sb = new StringBuilder();
      Iterator<IRExpression> opIter = getOperands().iterator();
      assert (opIter.hasNext()); // function expression
      IRExpression funExpr = opIter.next();
      xtc.type.Type resultType = CType.getType(sourceNode);
      if(!resultType.resolve().isVoid()) {
      	IRExpression retExpr = opIter.next();
      	sb.append(retExpr + " := ");
      }
      
      sb.append(funExpr + "(");
      while (opIter.hasNext()) {
        IRExpression arg = opIter.next();
        sb.append(arg.toString());
        if (opIter.hasNext()) {
          sb.append(",");
        }
      }
      sb.append(")");
      return sb.toString();

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
      
    case SKIP:
      return "skip";
    
    case FUNC_ENT:
    	return "enter " + getProperty(Identifiers.SCOPE);
    
    case FUNC_EXIT:
    	return "exit " + getProperty(Identifiers.SCOPE);
    	
    default:
      return sourceNode.getName();
    }
  }
}
