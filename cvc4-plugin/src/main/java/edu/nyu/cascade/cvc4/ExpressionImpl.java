package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.APPLY;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_INDEX;
import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.IF_THEN_ELSE;
import static edu.nyu.cascade.prover.Expression.Kind.SUBST;
import static edu.nyu.cascade.prover.Expression.Kind.TUPLE_INDEX;
import static edu.nyu.cascade.prover.Expression.Kind.VARIABLE;
import static edu.nyu.cascade.prover.Expression.Kind.NULL_EXPR;

import xtc.tree.GNode;

import java.util.List;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BoundVarType;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

/**
 * Base class encapsulating the cvc4 expressions.
 * 
 * @author dejan, wei
 */
public class ExpressionImpl implements Expression {
  
  static interface ArrayStoreAllConstructionStrategy {
    Expr apply(ExprManager em, edu.nyu.acsys.CVC4.Type type, Expr expr);
  }
  
  static interface BinaryConstructionStrategy {
    Expr apply(ExprManager em, Expr left, Expr right);
  }

  static interface BinderConstructionStrategy {
    Expr apply(ExprManager em, List<Expr> vars, Expr body);
  }
  
  static interface BinderGuardConstructionStrategy {
    Expr apply(ExprManager em, List<Expr> vars, Expr guard, Expr body);
  }
  
  static interface BinderTriggersConstructionStrategy {
    Expr apply(ExprManager em, List<Expr> vars, Expr body, List<Expr> triggers)
        throws Exception;
  }
  
  static interface BinderTriggersWithRewriteRuleConstructionStrategy {
    Expr apply(ExprManager em, Expr head, Expr body, List<Expr> triggers)
        throws Exception;
  }

  static interface NaryConstructionStrategy {
    Expr apply(ExprManager em, List<Expr> args);
  }
  
  static interface NarySubstitutionStrategy {
    Expr apply(ExprManager em, List<Expr> args);
  }

  static interface NullaryConstructionStrategy {
    Expr apply(ExprManager em);
  }

  static interface TernaryConstructionStrategy {
    Expr apply(ExprManager em, Expr arg1, Expr arg2, Expr arg3);
  }

  static interface UnaryConstructionStrategy {
    Expr apply(ExprManager em, Expr arg);
  }

  static interface VariableConstructionStrategy {
    Expr apply(ExprManager em, String name, edu.nyu.acsys.CVC4.Type type);
  }
  
  static ExpressionImpl mkNullExpr(ExpressionManagerImpl exprManager) {
    ExpressionImpl result = new ExpressionImpl(exprManager, NULL_EXPR,
        new NullaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em) {
            return em.mkConst(edu.nyu.acsys.CVC4.Kind.NULL_EXPR);
          }
        });
    return result;
  }

  static ExpressionImpl mkArrayIndex(
      ExpressionManagerImpl exprManager, Expression array,
      Expression index) {
    Preconditions.checkArgument(array.isArray());
    ExpressionImpl result = new ExpressionImpl(exprManager, ARRAY_INDEX,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.SELECT, left, right);
          }
        }, array, index);
    result.setType(array.asArray().getElementType());
    return result;
  }

/*  static ExpressionImpl mkFunApply(
      ExpressionManagerImpl exprManager, Expression fun,
      Expression arg1, Expression arg2) {
    Preconditions.checkArgument(fun.getType().getArity() == 2);
    return mkFunApply(exprManager, fun, ImmutableList.of(arg1, arg2));
  }*/

  static ExpressionImpl mkFunApply(
      ExpressionManagerImpl exprManager, Expression fun,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(fun.isFunction());
    int numArgs = Iterables.size(args);
    Preconditions.checkArgument(fun.getType().asFunction().getArity() == numArgs);
    List<Expression> args1 = Lists.newArrayListWithCapacity(numArgs + 1);
    args1.add(fun);
    Iterables.addAll(args1, args);
    ExpressionImpl result = new ExpressionImpl(exprManager, APPLY,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> children) {
            vectorExpr opkids = new vectorExpr();
            for(Expr child : children)  opkids.add(child);
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.APPLY_UF, opkids);
          }
        }, args1);
    result.setType(fun.asFunctionExpression().getRange());
    return result;
  }

  static ExpressionImpl mkFunApply(
      ExpressionManagerImpl exprManager, Expression fun,
      Expression firstArg,
      Expression... restArgs) {
    return mkFunApply(exprManager, fun, Lists.asList(firstArg, restArgs));
  }

  static ExpressionImpl mkIte(
      ExpressionManagerImpl exprManager, Expression cond,
      Expression thenPart, Expression elsePart) {
    Preconditions.checkArgument(cond.isBoolean());
    Preconditions.checkArgument(thenPart.getType().equals(elsePart.getType()));
    
    ExpressionImpl e = new ExpressionImpl(exprManager, IF_THEN_ELSE,
        new TernaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr arg1, Expr arg2, Expr arg3) {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.ITE, arg1, arg2, arg3);
          }
        }, cond, thenPart, elsePart);
    e.setType(thenPart.getType());
    return e;
  }

  static ExpressionImpl mkSubst(
      ExpressionManagerImpl exprManager, Expression e,
      Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs) {
    Preconditions.checkArgument(Iterables.size(oldExprs) == Iterables
        .size(newExprs));
    
    /* Don't bother to SUBST a constant */
    if( CONSTANT.equals(e.getKind()) || VARIABLE.equals(e.getKind())) {
      return exprManager.importExpression(e);
    }
    
    List<Expression> subs = Lists.newArrayList();
    subs.add(e);
    Iterables.addAll(subs, oldExprs);
    Iterables.addAll(subs, newExprs);
    ExpressionImpl result = new ExpressionImpl(exprManager, SUBST,
        new NarySubstitutionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args)
              throws Exception {
            assert (args.size() > 0);
            Expr e = args.get(0);
            int n = args.size() / 2;
            assert (args.size() == 2 * n + 1);
            vectorExpr oldExprs = new vectorExpr(n);
            for(int i = 1; i < n+1; i++)   
              oldExprs.add(args.get(i));
            vectorExpr newExprs = new vectorExpr(n);
            for(int i = n+1; i < args.size(); i++)  
              newExprs.add(args.get(i));
            return e.substitute(oldExprs, newExprs);
          }
        }, subs);
    result.setType(e.getType());
    return result;
  }

  static ExpressionImpl mkTupleIndex(ExpressionManagerImpl exprManager,
      Expression tuple, final int index) {
    ExpressionImpl result = new ExpressionImpl(exprManager, TUPLE_INDEX,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr tuple) {
            // FIXME: tuple update is not supported by CVC4 yet
            throw new UnsupportedOperationException("Unsupported cvc4 operation");
            /*return em.tupleSelectExpr(tuple, index);*/
          }
        }, tuple);
    result.setType(tuple.getType().asTuple().getElementTypes().get(index));
    return result;
  }

/*  static ExpressionImpl mkTypeExpr(TypeImpl t) {
    ExpressionManagerImpl exprManager = t.getExpressionManager();
    return new ExpressionImpl(exprManager, TYPE, t
        .getCVC4Type().mkGroundTerm(), 
        new TypeKindImpl(exprManager, t));
  }*/

  static ExpressionImpl mkTypeStub(
      ExpressionManagerImpl exprManager, final String name) {
    ExpressionImpl result = new ExpressionImpl(
        exprManager, Kind.TYPE_STUB, new NullaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em) {
            return em.mkConst(name);
          }
        });
    InductiveTypeImpl t = InductiveTypeImpl.stub(exprManager, name);
    result.setType(t);
    return result;
  }
  
  /**
   * The expression manager we are using.
   */
  private final ExpressionManagerImpl exprManager;

  /**
   * The cvc4 expression we are using
   */
  private Expr cvc4_expr;

  /** The vector of children to return on request (read only) */
  private ImmutableList<? extends ExpressionImpl> children;

  /**
   * A field to remember constant status at construction.
   */
  private boolean constant;

  private boolean isVariable;

  private TypeImpl type;
  
  private GNode sourceNode;
  
  /** The name of a variable expression. <code>null</code> if the expression
   * is not a variable. */
  protected String name = null;

  private final Kind kind;
  /* Copy constructor. */
  protected ExpressionImpl(ExpressionImpl e) {
    this.kind = e.getKind();
    exprManager = e.getExpressionManager();
    setCvc4Expression(e.getCvc4Expression());
    if (!e.getChildren().isEmpty()) {
      initChildren(e.getChildren());
    } else {
      children = ImmutableList.of();
    }
    setConstant(e.isConstant());
    setIsVariable(e.isVariable());
    setType(e.getType());
    setNode(e.getNode());
  }
  
  /*
   * protected void setChildren(List<? extends Expression> children) {
   * this.children = ImmutableList.copyOf(children); }
   */

  /* NOTE: This constructor does not set cvc4_expr! The sub-class will
   * be responsible for making sure it gets set!
   */
  protected ExpressionImpl(final ExpressionManagerImpl exprManager, Expression expr) {
    this.exprManager = exprManager;
    this.kind = expr.getKind();
    children = ImmutableList.copyOf(Lists.transform(expr.getChildren(),
        new Function<Expression, ExpressionImpl>() {
          @Override
          public ExpressionImpl apply(Expression from) {
            return exprManager.importExpression(from);
          }
        }));
    setConstant(expr.isConstant());
    setIsVariable(expr.isVariable());
    setType(expr.getType());
    setNode(expr.getNode());
  }

  private ExpressionImpl(ExpressionManagerImpl em, Kind kind) {
    this.exprManager = em;
    this.kind = kind;
  }
  
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      ArrayStoreAllConstructionStrategy strategy, Type arrayType,
      Expression expr) {
    this(em, kind, arrayType);
    init(expr);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprManager != null);
    assert (exprs.size() == 1);

    // Get the body cvc4 expressions
    Expr body_expr = exprs.get(0); 

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    edu.nyu.acsys.CVC4.ArrayType atype = new edu.nyu.acsys.CVC4.ArrayType(type.getCVC4Type());
    setCvc4Expression(strategy.apply(cvc4_em, atype, body_expr));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right) {
    this(em, kind);
    init(left, right);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprManager != null);
    assert (exprs.size() == 2);

    // Get the left and right cvc4 expressions
    Expr left_expr = exprs.get(0); // ((Expression) left).getCvc4Expression();
    Expr right_expr = exprs.get(1); // ((Expression) right).getCvc4Expression();

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, left_expr, right_expr));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      BinderConstructionStrategy strategy,
      Iterable<? extends Expression> vars, Expression body) {
    this(em, kind);
    init(body);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprs.size() == 1);

    Expr cvc4_body = exprs.get(0);

    // New list for the cvc4 variables
    List<Expr> cvc4_vars = ImmutableList.copyOf(getExpressionManager()
        .toCvc4Exprs(vars));

    /*
     * List<Expr> cvc4_triggers = ImmutableList.copyOf(ExpressionManager
     * .toCvc4Exprs(triggers));
     */
    // Call the construct method for quantification
    ExprManager cvc4_em = getExpressionManager()
        .getTheoremProver()
        .getCvc4ExprManager();
    setCvc4Expression(strategy.apply(cvc4_em, cvc4_vars, cvc4_body));
  }
  
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      BinderGuardConstructionStrategy strategy,
      Iterable<? extends Expression> vars, Expression guard, 
      Expression body) {
    this(em, kind);
    init(guard, body);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprs.size() == 2);

    Expr cvc4_guard = exprs.get(0);
    Expr cvc4_body = exprs.get(1);

    // New list for the cvc4 variables
    List<Expr> cvc4_vars = ImmutableList.copyOf(getExpressionManager()
        .toCvc4Exprs(vars));

    /*
     * List<Expr> cvc4_triggers = ImmutableList.copyOf(ExpressionManager
     * .toCvc4Exprs(triggers));
     */
    // Call the construct method for quantification
    ExprManager cvc4_em = getExpressionManager()
        .getTheoremProver()
        .getCvc4ExprManager();
    setCvc4Expression(strategy.apply(cvc4_em, cvc4_vars, cvc4_guard, cvc4_body));
  }
  
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      BinderTriggersConstructionStrategy strategy,
      Iterable<? extends Expression> vars, Expression body, Iterable<? extends Expression> triggers) {
    this(em, kind);
    init(body);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprs.size() == 1);

    Expr cvc4_body = exprs.get(0);

    // New list for the cvc4 variables
    List<Expr> cvc4_vars = ImmutableList.copyOf(getExpressionManager()
        .toCvc4Exprs(vars));

    List<Expr> cvc4_triggers = ImmutableList.copyOf(getExpressionManager()
        .toCvc4Exprs(triggers));
    
    // Call the construct method for quantification
    ExprManager cvc4_em = getExpressionManager()
        .getTheoremProver()
        .getCvc4ExprManager();
    setCvc4Expression(strategy.apply(cvc4_em, cvc4_vars, cvc4_body, cvc4_triggers));
  }
  
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      BinderTriggersWithRewriteRuleConstructionStrategy strategy,
      Expression head, Expression body, Iterable<? extends Expression> triggers) {
    this(em, kind);
    init(head, body);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprs.size() == 2);

    Expr cvc4_head = exprs.get(0);
    Expr cvc4_body = exprs.get(1);

    // New list for the cvc4 triggers
    List<Expr> cvc4_triggers = ImmutableList.copyOf(getExpressionManager()
        .toCvc4Exprs(triggers));
    
    // Call the construct method for quantification
    ExprManager cvc4_em = getExpressionManager()
        .getTheoremProver()
        .getCvc4ExprManager();
    setCvc4Expression(strategy.apply(cvc4_em, cvc4_head, cvc4_body, cvc4_triggers));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind, Expr e, Type type) {
    this(em, kind, type);
    setCvc4Expression(e);
  }

  /**
   * Constructs the expression by just setting the expression manager. The
   * inheriting class is responsible for setting up the other properties of the
   * expression, specially the cvc4_expr and the children list. Use with care.
   * 
   * @param em
   *          the expression manager.
   */
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind, Type type) {
    this(em, kind);
    setType(type);
    init();
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      NaryConstructionStrategy strategy, Expression first,
      Expression... rest) {
    this(em, kind, strategy, Lists.asList(first, rest));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      NaryConstructionStrategy strategy, Expression first,
      Expression second, Expression... rest) {
    this(em, kind, strategy, Lists.asList(first, second, rest));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      NaryConstructionStrategy strategy,
      Iterable<? extends Expression> subExpressions) {
    this(em, kind);
//    checkArgument(!Iterables.isEmpty(subExpressions));
    init(subExpressions);
    List<Expr> exprs = convertChildrenToExpr();

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, exprs));
  }
  
  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      NarySubstitutionStrategy strategy, Iterable<? extends Expression> expressions) {
    this(em, kind);
    // FIXME: the initialization actually compose the incorrect children of the new expression
    // Fortunately, Cascade don't use these children for now. So, it's safe for now only.
    // Following is the right version of convert children, which cause invalid memory access.
    init(expressions);
    List<Expr> exprs = convertChildrenToExpr();

//  Expression expr;
//  if(cvc4_expr.getType().isBoolean()) {
//    expr = exprManager.toBooleanExpression(cvc4_expr);
//  } else
//    expr = exprManager.toExpression(cvc4_expr);
//  initChildren(expr.getChildren());
    
    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, exprs));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      NullaryConstructionStrategy strategy) {
    this(em, kind);
    init();

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      TernaryConstructionStrategy strategy, Expression arg1,
      Expression arg2, Expression arg3) {
    this(em, kind);
    init(arg1, arg2, arg3);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprManager != null);
    assert (exprs.size() == 3);

    // Get the left and right cvc4 expressions
    Expr expr1 = exprs.get(0);
    Expr expr2 = exprs.get(1);
    Expr expr3 = exprs.get(2);

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, expr1, expr2, expr3));
  }

  protected ExpressionImpl(ExpressionManagerImpl em, Kind kind,
      UnaryConstructionStrategy strategy, Expression subExpression) {
    this(em, kind);
    init(subExpression);
    List<Expr> exprs = convertChildrenToExpr();

    assert (exprManager != null);
    assert (exprs.size() == 1);

    // Get the subexpression
    Expr expr = exprs.get(0);

    // Get the cvc4 expression manager
    ExprManager cvc4_em = exprManager.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, expr));
  }

  /*
   * TODO: Should probably move uniquify out of this package entirely. It has to
   * be up to clients to make sure their identifiers don't collide. Otherwise,
   * augment current variable creation functions with "fresh" variants.
   */
  protected ExpressionImpl(ExpressionManagerImpl em,
      VariableConstructionStrategy strategy, String name, Type itype,
      boolean uniquify) {
    this(em, Kind.VARIABLE, itype);
    assert( type != null );

    String actualName = uniquify ? Identifiers.uniquify(name) : name;

    this.name = actualName;
    setConstant(false);
    setIsVariable(true);

    // Get the cvc4 expression manager
    ExprManager cvc4_em = em.getTheoremProver().getCvc4ExprManager();

    // Create the new expression
    setCvc4Expression(strategy.apply(cvc4_em, actualName, type.getCVC4Type()));
  }

  @Override
  public BitVectorExpressionImpl asBitVector() {
    Preconditions.checkState( isBitVector() );
    return getExpressionManager().asBitVector(this);
  }

  @Override
  public BooleanExpressionImpl asBooleanExpression() {
    Preconditions.checkState( isBoolean() );
    return getExpressionManager().asBooleanExpression((ExpressionImpl) this);
  }

  @Override
  public IntegerExpressionImpl asIntegerExpression() {
    Preconditions.checkState( isInteger() );
    return getExpressionManager().asIntegerExpression(this);
  }

  @Override
  public IntegerVariableImpl asIntegerVariable() {
    Preconditions.checkState( isInteger() && isVariable() );
      return getExpressionManager().asIntegerVariable(this);
  }

  @Override
  public RationalExpressionImpl asRationalExpression() {
    Preconditions.checkState( isRational() );
      return getExpressionManager().asRationalExpression(this);
  }

  @Override
  public RationalVariableImpl asRationalVariable() {
    Preconditions.checkState( isRational() && isVariable() );
      return getExpressionManager().asRationalVariable(this);
  }

  @Override
  public FunctionExpression asFunctionExpression() {
    Preconditions.checkState( isFunction() );
      return getExpressionManager().asFunctionExpression(this);
  }

  @Override
  public VariableExpressionImpl asVariable() {
    Preconditions.checkState(isVariable());
    return getExpressionManager().asVariable(this);
  }

  private ImmutableList<Expr> convertChildrenToExpr() {
    // ImmutableList.copyOf(ExpressionManager.toCvc4Expr(children));
    ImmutableList.Builder<Expr> listBuilder = ImmutableList.builder();
    for (ExpressionImpl child : children) {
      listBuilder.add(child.getCvc4Expression());
    }
    return listBuilder.build();
  }

  @Override
  public BooleanExpressionImpl eq(Expression e) {
    return getExpressionManager().eq(this, e);
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof Expression) {
      return getCvc4Expression().equals(
          (getExpressionManager().importExpression((Expression) obj))
              .getCvc4Expression());
      
    }
    return super.equals(obj);
  }

  @Override
  public int getArity() {
    return children.size();
  }

  @Override
  public Expression getChild(int i) {
    Preconditions.checkArgument(i >= 0 && i < getArity());
    return getChildren().get(i);
  }

  @Override
  public ImmutableList<? extends ExpressionImpl> getChildren() {
    return children;
  }

  /**
   * Returns the cvc4 expression we are using
   * 
   * @return the expression
   */
  public Expr getCvc4Expression() {
    // FIXME: User could mutate Expr and cause it to get out of sync
    // with kind, children, etc.
    return cvc4_expr;
  }

  /**
   * Returns the expression manager.
   */
  @Override
  public ExpressionManagerImpl getExpressionManager() {
    return exprManager;
  }

/*  private void initChildren(IExpression first, IExpression... rest) {
    initChildren(Lists.asList(first, rest));
  }
*/
  /*
   * public Expression simplify() { ExprManager em =
   * exprManager.getTheoremProver().getValidityChecker(); try { Expr cvc4_expr =
   * em.simplify(getCvc4Expression()); return new
   * Expression(exprManager,cvc4_expr); } catch (Exception e) { throw new
   * TheoremProverException(e); } }
   */

  @Override
  public Kind getKind() {
    return kind;
  }

  protected String getName() { return name; }

  @Override
  public Type getType() {
    return type;
  }
  
  @Override
  public FunctionType getFuncDecl() {
    // FIXME: FuncDecl is only for Z3 expression
    return null;
  }
  
  @Override
  public GNode getNode() {
    return sourceNode;
  }
  
  @Override
  public Expression setNode(GNode node) {
    this.sourceNode = node;
    return this;
  }
  
  @Override
  public int hashCode() {
    return getCvc4Expression().hashCode();
  }

  private void init() {
    cvc4_expr = null;
    children = ImmutableList.of();
    setConstant(false);
    setIsVariable(false);
  }

  private void init(Expression first, Expression... rest) {
    init(Lists.asList(first, rest));
  }

  private void init(Iterable<? extends Expression> subExpressions) {
    initChildren(subExpressions);
    // setExpressionManagerFromChildren();
    setConstantFromChildren();
  }

  protected void initChildren(Iterable<? extends Expression> subExpressions) {
    /*
     * TODO: Is there a reason we won't take an empty Iterable here? See
     * BooleanExpression for an example of why this is annoying
     * [chris 1/7/10] I'm guessing no. I think the old reason was, we needed one
     * of the children to provide the ExpressionManager, but now we're passing in
     * the ExpressionManager in the constructors.
     */
//    checkArgument(!Iterables.isEmpty(subExpressions));
    children = ImmutableList.copyOf(getExpressionManager().importExpressions(
        subExpressions));
  }

  /*
   * protected void setExpressionManagerFromChildren() {
   * Preconditions.checkState( children.size() > 0 );
   * 
   * // element 0 is guaranteed to exist, from the assertion above, // and to
   * have a CVC4 ExpressionManager, from toExpression. Expression firstExpr =
   * children.get(0); final IExpressionManager em =
   * firstExpr.getExpressionManager();
   * 
   * boolean emsMatch = Iterables.all(children, new Predicate<Expression>() {
   * public boolean apply(Expression expr) { return
   * expr.getExpressionManager() == em; }});
   * 
   * if (!emsMatch || !(em instanceof ExpressionManager)) { throw new
   * TheoremProverException("Expression manager mismatch."); }
   * 
   * exprManager = (ExpressionManager) em; }
   */

  @Override
  public final boolean isConstant() {
    return constant;
  }

  @Override
  public final boolean isVariable() {
    return isVariable;
  }

/*  private Kind kindOfCvc4Expr(Expr e) {
    if (e.isMinus()) {
      return MINUS;
    } else if (e.isMult()) {
      return MULT;
    } else if (e.isPlus()) {
      return PLUS;
    } else if (e.isPow()) {
      return POW;
    } else if (e.isUminus()) {
      return UNARY_MINUS;
    } else if (e.isVar()) {
      return VARIABLE;
    } else
      throw new IllegalArgumentException("Unsupported kind (this is a bug).");
  }
*/
  
  public FunctionExpression lambda(BoundVariableListExpressionImpl vars) {
    return ((TypeImpl) getType()).lambda(vars, this);
  }
  
  @Override
  public FunctionExpression lambda(VariableExpression var) {
    return getType().lambda(var, this);
  }
  
  @Override
  public FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars) {
    return getType().lambda(vars, this);
  }

  @Override
  public BooleanExpression neq(Expression e) {
    return getExpressionManager().neq(this, e);
  }

  protected void setConstant(boolean constant) {
    this.constant = constant;
  }

  protected void setConstantFromChildren() {
    setConstant(Iterables.all(children, new Predicate<ExpressionImpl>() {
      public boolean apply(ExpressionImpl expr) {
        return expr.isConstant();
      }
    }));
  }

  protected void setCvc4Expression(Expr cvc4_expr) {
    this.cvc4_expr = cvc4_expr;
  }

  protected void setIsVariable(boolean b) {
    this.isVariable = b;
  }

  protected void setName(String name) { this.name = name; }

  protected void setType(Type type) {
    this.type = getExpressionManager().importType(type);
  }

  @Override
  public Expression subst(Expression oldExpr, Expression newExpr) {
    List<Expression> oldExprs = Lists.newArrayList();
    oldExprs.add(oldExpr);
    List<Expression> newExprs = Lists.newArrayList();
    newExprs.add(newExpr);
    return subst(oldExprs,newExprs);
  }

  @Override
  public Expression subst(Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs) {
    return mkSubst(getExpressionManager(), this, oldExprs, newExprs);
  }

  @Override
  public String toString() {
    return getCvc4Expression().toString();
  }

  @Override
  public boolean isBoolean() {
    return getType().equals( getExpressionManager().booleanType() );
  }

  @Override
  public ArrayExpression asArray() {
    Preconditions.checkArgument(isArray());
    return ArrayExpressionImpl.valueOf(this);
  }

/*  @SuppressWarnings("unchecked")
  @Override
  public ArrayExpression asArray(Type indexType) {
    Preconditions.checkArgument(isArray(indexType));
    return (ArrayExpression) this;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <I extends Type, E extends Type> ArrayExpression asArray(
      I indexType, E elementType) {
    Preconditions.checkArgument(isArray(indexType,elementType));
    return (ArrayExpression) this;
  }*/

  @Override
  public boolean isArray() {
    return getType() instanceof ArrayType;
  }

/*  @Override
  public <I extends Type> boolean isArray(I indexType) {
    return isArray() && ((ArrayType)getType()).getIndexType().equals(indexType);
  }

  @Override
  public boolean isArray(Expression indexType,
      Expression elementType) {
    return isArray(indexType) && ((ArrayType)getType()).getElementType().equals(elementType);
  }
*/
  @Override
  public boolean isBitVector() {
    return getType() instanceof BitVectorType;
  }

  @Override
  public boolean isInteger() {
    return getType() instanceof IntegerType;
  }

  @Override
  public boolean isRational() {
    return getType() instanceof RationalType;
  }

  @Override
  public boolean isFunction() {
    return getType() instanceof FunctionType;
  }

  @Override
  public InductiveExpression asInductive() {
    Preconditions.checkState(isInductive());
    return getExpressionManager().asInductiveExpression(this);
  }

  @Override
  public TupleExpression asTuple() {
    Preconditions.checkState(isTuple());
    return getExpressionManager().asTuple(this);
  }

  @Override
  public boolean isTuple() {
    return getType() instanceof TupleType;
  }

  @Override
  public boolean isInductive() {
    return getType() instanceof InductiveType;
  }
  
  public boolean isBoundVariableList() {
    return getType() instanceof BoundVarType;
  }
  
  public BoundVariableListExpressionImpl asBoundVariableList() {
    Preconditions.checkState(isBoundVariableList());
    return getExpressionManager().asBoundVariableList(this);
  }
}
