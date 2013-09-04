package edu.nyu.cascade.ir.impl;

import static edu.nyu.cascade.ir.IRStatement.StatementType.ALLOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSERT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSIGN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.ASSUME;
import static edu.nyu.cascade.ir.IRStatement.StatementType.AWAIT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.DECLARE_ARRAY;
import static edu.nyu.cascade.ir.IRStatement.StatementType.DECLARE_STRUCT;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CALL;
import static edu.nyu.cascade.ir.IRStatement.StatementType.CRITICAL_SECTION;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FIELD_ASSIGN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.FREE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.HAVOC;
import static edu.nyu.cascade.ir.IRStatement.StatementType.NON_CRITICAL_SECTION;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RECEIVE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RELEASE_SEMAPHORE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.REQUEST_SEMAPHORE;
import static edu.nyu.cascade.ir.IRStatement.StatementType.RETURN;
import static edu.nyu.cascade.ir.IRStatement.StatementType.SEND;
import static edu.nyu.cascade.ir.IRStatement.StatementType.SKIP;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathEncoding;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.UnionFind;

public class Statement implements IRStatement {
  
  public static Statement alloc(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, ALLOC, ptrExpr, sizeExpr);
  }
  
  public static Statement declareArray(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, DECLARE_ARRAY, ptrExpr, sizeExpr);
  }
  
  public static Statement declareStruct(Node sourceNode, IRExpressionImpl ptrExpr, IRExpressionImpl sizeExpr) {
    return new Statement(sourceNode, DECLARE_STRUCT, ptrExpr, sizeExpr);
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
  
  public static Statement fieldAssign(Node sourceNode, IRExpressionImpl varExpr, 
      IRExpression fieldName,
      IRExpressionImpl valExpr) {
    return new Statement(sourceNode, FIELD_ASSIGN, varExpr, fieldName, valExpr);
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
  
  protected Statement(Node sourceNode) {
    this(sourceNode, null);
  }

  protected Statement(Node sourceNode, StatementType type,
      IRExpression... operands) {
    // ArrayList<IExpression> arrayList) {
    this.sourceNode = sourceNode;
    this.type = type;
    this.operands = ImmutableList.copyOf(Arrays.asList(operands));
    this.location = IRLocations.ofNode(sourceNode);
    this.preLabels = Sets.newHashSet();
    this.postLabels = Sets.newHashSet();
  }
  
  protected Statement(Node sourceNode, StatementType type,
      List<? extends IRExpression> operands) {
    this.sourceNode = sourceNode;
    this.type = type;
    this.operands = ImmutableList.copyOf(operands);
    this.location = IRLocations.ofNode(sourceNode);
    this.preLabels = Sets.newHashSet();
    this.postLabels = Sets.newHashSet();
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

/*  @Override
  public <Expr> Expr getBooleanOperand(ExpressionEncoder<Expr> interp,int i) throws ExpressionFactoryException {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperand(i).toBoolean(interp);
  }
*/
  @Override
  public IRLocation getLocation() {
    return location;
  }

  @Override
  public  ExpressionClosure getOperand(ExpressionEncoder encoder,int i)  {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperand(i).toExpression(encoder);
  }

  public IRExpression getOperand(int i) {
    Preconditions.checkArgument(i >= 0 && i < getOperands().size());
    return getOperands().get(i);
  }

  @Override
  public ImmutableList<IRExpression> getOperands() {
    return ImmutableList.copyOf(operands);
  }

  @Override
  public ImmutableList<ExpressionClosure> getOperands(final ExpressionEncoder encoder) {
    ImmutableList.Builder<ExpressionClosure> listBuilder = ImmutableList.builder();
    for( IRExpression e : operands ) {
      listBuilder.add( e.toExpression(encoder) );
    }
    return listBuilder.build();
    
/*    return Collections.unmodifiableList(Lists.transform(operands,
        new Function<Expression, Expr>() {
          @Override
          public Expr apply(Expression e) {
            return factory.createExpr(e.getSourceNode());
          }
        }));
*/  
  }

  @Override
  public Expression getPostCondition(PathEncoding factory, Expression prefix) {
//    Preconditions.checkArgument( factory.getPathType().equals( prefix.getType() ));
    switch (getType()) {
    case ASSIGN: 
      return factory.assign(prefix, getOperand(0), getOperand(1));
    case FIELD_ASSIGN: {
      if(Preferences.isSet(Preferences.OPTION_THEORY) 
          && Preferences.getString(Preferences.OPTION_THEORY).endsWith("Reach"))
        return factory.fieldAssign(prefix, getOperand(0), getOperand(1).toString(), getOperand(2));
      else
        return factory.noop(prefix);
    }
    case ASSERT:
    	return factory.check(prefix, getOperand(0));
    case ASSUME:
    case AWAIT:
      return factory.assume(prefix, getOperand(0));
    case ALLOC:
        return factory.alloc(prefix, getOperand(0), getOperand(1));      
    case DECLARE_ARRAY:
        return factory.declareArray(prefix, getOperand(0), getOperand(1));
    case DECLARE_STRUCT:
      return factory.declareStruct(prefix, getOperand(0), getOperand(1));
    case FREE:
      return factory.free(prefix, getOperand(0));
    case HAVOC:
      return factory.havoc(prefix, getOperand(0));
    case CRITICAL_SECTION:
    case NON_CRITICAL_SECTION:
    case SKIP:
      return factory.noop(prefix);
      
    default:
      IOUtils.debug().pln( getType() == CALL ? 
          "Statement.getPostCondition: Igonring statement type: " 
              + getType() + ", with undeclared function " 
              + getOperand(0).toString()    :
          "Statement.getPostCondition: Ignoring statement type: "
              + getType());
      return factory.noop(prefix);
    }
  }
  
  @Override
  public ImmutableSet<String> getPostLabels() {
    return ImmutableSet.copyOf(postLabels);
  }

  @Override
  public ExpressionClosure getPreCondition(ExpressionEncoder  encoder) {
    switch (getType()) {
    case ASSERT:
      return getOperand(0).toBoolean(encoder);
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
    case ALLOC:
      return getOperand(0) + " := malloc(" + getOperand(1) + ")";     
    case DECLARE_ARRAY:
      return getOperand(0) + " := array[" + getOperand(1) + "]";
    case DECLARE_STRUCT:
      return getOperand(0) + " := struct[" + getOperand(1) + "]";
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
      
    case FIELD_ASSIGN:
      if(Preferences.isSet(Preferences.OPTION_THEORY) 
          && Preferences.getString(Preferences.OPTION_THEORY).endsWith("Reach")) {
        if(getOperands().size() == 2)
          return "f(" + getOperand(0) + ") := " + getOperand(1);
        else
          return "f(" + getOperand(0) + "->" + getOperand(1) + ") := " + getOperand(2);
      } else 
        return "skip";

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
      return "return " + getOperand(0);

    case SKIP:
      return "skip";

    default:
      return sourceNode.getName();
    }
  }

  /**
   * TODO: to support the equality relation between pointers 
   * assumption/assertion in the annotation
   */
  @Override
  public Map<String, String> preProcessAlias(PathEncoding factory, Map<String, String> aliasMap) {
    switch (getType()) {
    case ASSIGN: {
      Node lhs = getOperand(0).getSourceNode();
      Node rhs = getOperand(1).getSourceNode();
      
      xtc.type.Type lType = (xtc.type.Type) lhs.getProperty(xtc.Constants.TYPE);
      xtc.type.Type rType = (xtc.type.Type) rhs.getProperty(xtc.Constants.TYPE);

      if(CType.unwrapped(lType).isPointer() && CType.unwrapped(rType).isPointer()) {
        if("AddressExpression".equals(rhs.getName())) {
          rType = (xtc.type.Type) rhs.getGeneric(0).getProperty(xtc.Constants.TYPE);
        }
        
        String lRefName = CType.getReferenceName(lType);
        String rRefName = CType.getReferenceName(rType);
        
        aliasMap = UnionFind.union(aliasMap, lRefName, rRefName);
      }
      return aliasMap;
    }
    default:
      return aliasMap;
    }
  }
}
