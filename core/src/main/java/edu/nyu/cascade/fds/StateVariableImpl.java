package edu.nyu.cascade.fds;

import java.util.HashMap;
import java.util.Iterator;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class StateVariableImpl extends StateExpressionImpl implements StateVariable {
  protected static final char PRIME_CHAR = '\'';

  private static final HashMap<VariableExpression, StateVariableImpl> varMap = 
    new HashMap<VariableExpression, StateVariableImpl>();

  public static StateVariableImpl create(
      ExpressionManager exprManager, String name, Type t, boolean fresh) {
    return create(exprManager,name,t,fresh,false);
  }
  
  public static StateVariableImpl create(
      ExpressionManager exprManager, String name, Type t, boolean fresh, boolean constant) {
    VariableExpression varExpr = exprManager.variable(name, t, fresh);
    return valueOf(varExpr, fresh, constant);
  }

  /* NOTE: fresh is passed in here solely to be used in an assertion. */
  private static StateVariableImpl valueOf(
      VariableExpression varExpr, boolean fresh, boolean constant) {
    if( varExpr instanceof StateVariableImpl ) {
      return (StateVariableImpl) varExpr;
    }
    
    StateVariableImpl var = lookup(varExpr);
    /* If the var is fresh than the lookup should have failed. */
    assert( !fresh || var==null );
    /* If the lookup succeeded that var.isConstant should agree with constant */
    assert( var==null || var.isConstant() == constant );
    if (var == null) {
      var = new StateVariableImpl(varExpr,constant);
      varMap.put(varExpr, var);
    } 
    return var;
  }
  
  public static StateVariableImpl constant(
      ExpressionManager exprManager, String name, Type t, boolean fresh) {
    return create(exprManager,name,t,fresh,true);
  }
  

  public static StateVariableImpl freshVariable(ExpressionManager exprMgr,
      String name, Type type) {
    return create(exprMgr,name,type,true);
  }

  public static StateVariableImpl lookup(VariableExpression var) {
    return (StateVariableImpl)varMap.get(var);
  }
  
  public static StateVariableImpl valueOf(VariableExpression varExpr) {
    return valueOf(varExpr,false,false);
  }

  private final VariableExpression var;
  
  private int primeLevel;

  private StateVariableImpl primedVersion;
  private StateVariableImpl unprimedVersion;
  private final boolean constant;
    
  private StateVariableImpl(VariableExpression var, boolean constant) {
    super(var);
    this.var = var;
    this.primeLevel = 0;
    this.constant = constant;
  }
  
  @Override
  public boolean equals(Object o) {
    if (o instanceof StateVariableImpl) {
      StateVariableImpl x = (StateVariableImpl) o;
      return primeLevel == x.primeLevel && var.equals(x.var);
    } else {
      return false;
    }
  }

  @Override
  public String getName() {
    return var.getName();
  }

  @Override
  public int hashCode() {
    return var.hashCode();
  }

  @Override
  public boolean isConstant() {
    return constant;
  }
  
  @Override
  public boolean isPrimed() {
    return primeLevel > 0;
  }

  @Override
  public boolean isVariable() {
    return true;
  }

  @Override
  public StatePropertyImpl preserved() {
    /*
     * When variable is boolean, use iff() instead of eq().
     * FIXME: It is not a good idea to put boolean-check here.
     * Need improvement.
     */
    if(var.getClass().getName().equals("edu.nyu.cascade.z3.BooleanVariable")) {
      return StatePropertyImpl.valueOf(getExpressionManager().iff(prime().asBooleanExpression(), var.asBooleanExpression()));
    } else {
      return StatePropertyImpl.valueOf(prime().eq(var));
    }
//    return StateProperty.create(prime().eq(var));
  }

  @Override
  public StateVariableImpl prime() {
//    IOUtils.debug().indent().pln(">> PRIMING VAR: " + this);
    if( constant ) {
      return this;
    }
    
    if(primedVersion == null) {
      primedVersion = create(getExpressionManager(),getName() + PRIME_CHAR, getType(), true, constant);
      primedVersion.primeLevel = primeLevel + 1;
      primedVersion.unprimedVersion = this;

//      IOUtils.debug().indent().pln("<< got: " + primedVersion);
    } else {
//      IOUtils.debug().indent().pln("<< already had primed " + this).indent().pln("   got: " + primedVersion);
    }

    return primedVersion;
  }

  @Override
  public Expression subst(Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs) {

    for(Iterator<? extends Expression> i = oldExprs.iterator(), j = newExprs.iterator(); i.hasNext(); ) {
      Expression old = i.next();
      Expression neww = j.next();
      if(old.equals(this))
        return (Expression)neww;
    }

    return this;
  }

  @Override
  public String toString() {
    return var.toString();
  }
  
  @Override
  public StateVariableImpl unprime() {
    Preconditions.checkArgument(unprimedVersion != null);
    return unprimedVersion;
  }
}
