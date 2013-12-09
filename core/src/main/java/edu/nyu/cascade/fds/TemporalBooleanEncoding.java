package edu.nyu.cascade.fds;

import java.util.List;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.AbstractTypeEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;

public class TemporalBooleanEncoding extends
    AbstractTypeEncoding<StateProperty> implements
    BooleanEncoding<StateProperty> {
  
  private final StateProperty.Factory propFactory;
  private final BooleanEncoding<? extends Expression> baseEncoding;
  
  @Inject
  public TemporalBooleanEncoding(
      @Assisted BooleanEncoding<? extends Expression> booleanEncoding,
      @Assisted StateProperty.Factory propFactory) {
    super(booleanEncoding.getExpressionManager(), booleanEncoding
        .getExpressionManager().booleanType());

    Preconditions.checkArgument(booleanEncoding.getType().equals(
        booleanEncoding.getExpressionManager().booleanType()));

    this.propFactory = propFactory;
    this.baseEncoding = booleanEncoding;
  }

  @Override
  public StateProperty and(Iterable<? extends StateProperty> conjuncts) {
    return propFactory.valueOf( and_(baseEncoding,conjuncts));
  }
  
  private <T extends Expression> T and_(BooleanEncoding<T> be,
      Iterable<? extends StateProperty> conjuncts) {
    List<T> conjExprs = Lists.newArrayList();
    for (StateProperty p : conjuncts) {
      conjExprs.add(be.ofExpression(p.toExpression()));
    }
    return be.and(conjExprs);
  }
  
  @Override
  public StateProperty and(StateProperty lhs, StateProperty rhs) {
    return propFactory.valueOf( and_(baseEncoding,lhs,rhs) );
  }

  private <T extends Expression> T and_(BooleanEncoding<T> be,
      StateProperty lhs, StateProperty rhs) {
    return be.and(be.ofExpression(lhs.toExpression()),be.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public StateProperty ff() {
    return propFactory.valueOf(baseEncoding.ff());
  }
  
  @Override
  public StateProperty iff(StateProperty lhs, StateProperty rhs) {
    return propFactory.valueOf( iff_(baseEncoding,lhs,rhs) );
  }

  private <T extends Expression> T iff_(BooleanEncoding<T> be,
      StateProperty lhs, StateProperty rhs) {
    return be.iff(be.ofExpression(lhs.toExpression()),be.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public StateProperty implies(StateProperty lhs, StateProperty rhs) {
    return propFactory.valueOf( implies_(baseEncoding,lhs,rhs) );
  }

  private <T extends Expression> T implies_(BooleanEncoding<T> be,
      StateProperty lhs, StateProperty rhs) {
    return be.implies(be.ofExpression(lhs.toExpression()),be.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public StateProperty not(StateProperty arg) {
    return propFactory.valueOf( not_(baseEncoding,arg) );
  }

  private <T extends Expression> T not_(BooleanEncoding<T> be,
      StateProperty arg) {
    return be.not(be.ofExpression(arg.toExpression()));
  }
  @Override
  public StateProperty ofBooleanExpression(BooleanExpression b) {
    return propFactory.valueOf(b);
  }

  @Override
  public StateProperty or(Iterable<? extends StateProperty> disjuncts) {
    return propFactory.valueOf(or_(baseEncoding,disjuncts));
  }

  private <T extends Expression> T or_(BooleanEncoding<T> be,
      Iterable<? extends StateProperty> disjuncts) {
    List<T> disjExprs = Lists.newArrayList();
    for (StateProperty p : disjuncts) {
      disjExprs.add(be.ofExpression(p.toExpression()));
    }
    return be.or(disjExprs);
  }
  
  @Override
  public StateProperty or(StateProperty lhs, StateProperty rhs) {
    return propFactory.valueOf( or_(baseEncoding,lhs,rhs) );
  }

  private <T extends Expression> T or_(BooleanEncoding<T> be,
      StateProperty lhs, StateProperty rhs) {
    return be.or(be.ofExpression(lhs.toExpression()),be.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public StateProperty tt() {
    return propFactory.valueOf(baseEncoding.tt());
  }

  @Override
  public StateProperty xor(StateProperty lhs, StateProperty rhs) {
    return propFactory.valueOf( xor_(baseEncoding,lhs,rhs) );
  }

  private <T extends Expression> T xor_(BooleanEncoding<T> be,
      StateProperty lhs, StateProperty rhs) {
    return be.xor(be.ofExpression(lhs.toExpression()),be.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public BooleanExpression toBoolean(StateProperty b) {
    return b.asBooleanExpression();
  }

  @Override
  public StateProperty forall(Iterable<? extends VariableExpression> vars,
      StateProperty expr) {
    return propFactory.valueOf(forall_(baseEncoding,vars,expr));
  }
  
  private <T extends Expression> T forall_(BooleanEncoding<T> be,
      Iterable<? extends VariableExpression> vars,
          StateProperty expr) {
    return be.forall(vars,be.ofExpression(expr.toExpression()));
  }
  
  @Override
  public StateProperty exists(Iterable<? extends VariableExpression> vars,
      StateProperty expr) {
    return propFactory.valueOf(exists_(baseEncoding,vars,expr));
  }
  
  private <T extends Expression> T exists_(BooleanEncoding<T> be,
      Iterable<? extends VariableExpression> vars,
          StateProperty expr) {
    return be.exists(vars,be.ofExpression(expr.toExpression()));
  }

  @Override
  public StateProperty ofExpression(Expression x) {
    Preconditions.checkArgument(x.isBoolean());
    return propFactory.valueOf(baseEncoding.ofExpression(x));
  }

  @Override
  public StateProperty unknown() {
    return propFactory.valueOf(baseEncoding.unknown());
  }
}
