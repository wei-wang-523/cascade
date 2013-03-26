package edu.nyu.cascade.z3;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.ConcurrentMap;

import com.google.common.base.Function;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.UninterpretedSort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public class InductiveTypeImpl extends TypeImpl implements InductiveType {
  
  private static ConcurrentMap<ExpressionManagerImpl, ConcurrentMap<String, ConstructorImpl>> constructorCache = new MapMaker()
      .makeComputingMap(new Function<ExpressionManagerImpl, ConcurrentMap<String, ConstructorImpl>>() {
        @Override
        public ConcurrentMap<String, ConstructorImpl> apply(
            ExpressionManagerImpl from) {
          return new MapMaker().makeMap();
        }
      });
  
  
  static class Builder {
    private final List<String> typeNames; 
    private final List<List<ConstructorImpl>> constructorLists;
    private final List<List<String>> constructorNameLists;
    private final List<List<List<String>>> selectorNameListLists;
    private final List<List<List<Sort>>> selectorTypeListLists;
    private final List<List<List<Sort>>> selectorUninterTypeListLists;
    private final List<List<List<Integer>>> selectorTypeRefListLists;
    private String currentName;
    private List<ConstructorImpl> currentConstructors;
    private List<String> currentConstructorNames;
    private List<List<String>> currentSelectorNameLists;
    private List<List<Sort>> currentSelectorTypeLists;
    private List<List<Sort>> currentSelectorUninterTypeLists;
    private List<List<Integer>> currentSelectorTypeRefLists;
    private final ExpressionManagerImpl exprManager;
    
    public Builder(ExpressionManagerImpl exprManager) {
      this.exprManager = exprManager;
      typeNames = Lists.newArrayList();
      constructorLists= Lists.newArrayList();
      constructorNameLists = Lists.newArrayList();
      selectorNameListLists = Lists.newArrayList();
      selectorTypeListLists = Lists.newArrayList();
      selectorUninterTypeListLists = Lists.newArrayList();
      selectorTypeRefListLists = Lists.newArrayList();
      currentName = null;
      currentConstructors = Lists.newArrayList();
      currentConstructorNames = Lists.newArrayList();
      currentSelectorNameLists = Lists.newArrayList();
      currentSelectorTypeLists = Lists.newArrayList();
      currentSelectorUninterTypeLists = Lists.newArrayList();
      currentSelectorTypeRefLists = Lists.newArrayList();
    }
    
    public Builder addConstructor(Constructor iConstructor) {
      ConstructorImpl c = ConstructorImpl.valueOf(iConstructor);
      currentConstructors.add(c);
      currentConstructorNames.add(c.getName());
      List<SelectorImpl> selectors = c.getSelectors();
      List<String> selectorNames = Lists.newArrayListWithExpectedSize(selectors.size());
      List<Sort> selectorTypes = 
        Lists.newArrayListWithExpectedSize(selectors.size());
      List<Sort> selectorUninters = 
          Lists.newArrayListWithExpectedSize(selectors.size());
      List<Integer> selectorTypeRefs = 
          Lists.newArrayListWithExpectedSize(selectors.size());
      for( SelectorImpl  selector : selectors ) {
        selectorNames.add( selector.getName() );
        Type type = selector.getType();
        Sort sort = exprManager.toZ3Type(type);
        selectorTypes.add(sort);
        if(sort == null) {
          Sort uninterpretedSort = ((InductiveTypeImpl) type).getZ3UnresolvedDatatype();
          selectorUninters.add(uninterpretedSort);
        } else {
          selectorUninters.add(null);
        }
        selectorTypeRefs.add(selector.typeRef);
      }
      currentSelectorNameLists.add(selectorNames);
      currentSelectorTypeLists.add(selectorTypes);
      currentSelectorUninterTypeLists.add(selectorUninters);
      currentSelectorTypeRefLists.add(selectorTypeRefs);
      return this;
    }
    
    public ImmutableList<InductiveTypeImpl> build(ExpressionManagerImpl exprManager) { 
      flushState();
      
      if (IOUtils.debugEnabled() || IOUtils.tpFileEnabled()) {
        StringBuilder sb = new StringBuilder();
        sb.append("() ("); // Type parameter
        int i = 0;
        for (String typeName : typeNames) {
          if (i > 0) {
            sb.append("\n                       ");
          }
          sb.append(" (" + typeName);
          int j = 0;
          for (String constructorName : constructorNameLists.get(i)) {
            int selectorSize = selectorNameListLists.get(i).get(j).size();
            sb.append(" (" + constructorName);
            
            if (selectorSize > 0) {
              int k = 0;
              for (String selectorName : selectorNameListLists.get(i).get(j)) {
                sb.append(" (" + selectorName + " ");
                Sort sType = selectorTypeListLists.get(i).get(j).get(k);
                try {
                  if(sType != null) sb.append(sType);
                  else {
                    Sort uninterSort = selectorUninterTypeListLists.get(i).get(j).get(k);
                    sb.append(uninterSort.toString());
                  }
                } catch (Exception e) {
                  throw new TheoremProverException(e);
                }
                sb.append(")");
                k++;
              }
            }
            sb.append(")");
            j++;
          }
          sb.append(")");
          i++;
        }
        sb.append(")");
        if(IOUtils.debugEnabled())
          TheoremProverImpl.debugCommand("(declare-datatypes " + sb.toString() + ")");
        if(IOUtils.tpFileEnabled())
          TheoremProverImpl.z3FileCommand("(declare-datatypes " + sb.toString() + ")");
      }
      
      Sort[] sorts = null;
      com.microsoft.z3.Constructor[][] clists = null;
      String[] typeNameArray = null;
      
      try {
        assert typeNames.size() == constructorNameLists.size()
            : "expected names and constructors vectors to be of equal length";
        assert typeNames.size() == selectorNameListLists.size()
            : "expected names and selectors vectors to be of equal length";
        assert typeNames.size() == selectorTypeListLists.size()
            : "expected names and types vectors to be of equal length";
        assert typeNames.size() == selectorTypeRefListLists.size()
            : "expected names and type refs vectors to be of equal length";
        
        Context ctx = exprManager.getTheoremProver().getZ3Context();
        
        clists = new com.microsoft.z3.Constructor[typeNames.size()][];
        typeNameArray = new String[typeNames.size()];
        
        for(int i = 0; i < typeNames.size(); i++) {
          assert constructorNameLists.get(i).size() == selectorNameListLists.get(i).size()
              : "expected sub-vectors in constructors and selectors vectors to match in size";
          assert constructorNameLists.get(i).size() == selectorTypeListLists.get(i).size() 
              : "expected sub-vectors in constructors and types vectors to match in size";
          assert constructorNameLists.get(i).size() == selectorTypeRefListLists.get(i).size() 
              : "expected sub-vectors in constructors and types ref vectors to match in size";
          
          int cons_size = constructorNameLists.get(i).size();
          com.microsoft.z3.Constructor[] constructors = new com.microsoft.z3.Constructor[cons_size];
          for(int j = 0; j < constructorNameLists.get(i).size(); j++) {
            String cons_name = constructorNameLists.get(i).get(j);
            int arity = selectorNameListLists.get(i).get(j).size();
            String[] selectorNames = new String[arity];
            Sort[] selectorTypes = new Sort[arity];
            int[] selectorTypeRefs = new int[arity];
            for(int k = 0; k < selectorNameListLists.get(i).get(j).size(); k++) {
              selectorNames[k] = selectorNameListLists.get(i).get(j).get(k);
              selectorTypes[k] = selectorTypeListLists.get(i).get(j).get(k);
              selectorTypeRefs[k] = selectorTypeRefListLists.get(i).get(j).get(k);
            }
            com.microsoft.z3.Constructor cons = ctx.MkConstructor(cons_name, "is-" + cons_name, 
                selectorNames, selectorTypes, selectorTypeRefs);
            constructors[j] = cons;
          }
          clists[i] = constructors;
          typeNameArray[i] = typeNames.get(i);
        }
        
        sorts = ctx.MkDatatypeSorts(typeNameArray, clists);
      } catch (Exception e) {
        throw new TheoremProverException(e);
      }
      
      assert( sorts.length == constructorLists.size() );
      
      ImmutableList.Builder<InductiveTypeImpl> listBuilder = new ImmutableList.Builder<InductiveTypeImpl>(); 

      for(int i = 0; i< sorts.length; i++) {
        Sort z3type = sorts[i];
        List<ConstructorImpl> constructors = constructorLists.get(i);
        InductiveTypeImpl t = new InductiveTypeImpl(exprManager, z3type, typeNames
            .get(i), constructors);
        int j = 0;
        for( ConstructorImpl c : constructors ) {
          c.setType(t);
          c.setZ3Constructor(clists[i][j]);
          j++;
        }
        listBuilder.add(t);
      }
      ImmutableList<InductiveTypeImpl> types = listBuilder.build();
      
      /* Fill in stub types with actual types in selectors */
      for (List<ConstructorImpl> constructors : constructorLists) {
        for (ConstructorImpl constr : constructors) {
          for (SelectorImpl sel : constr.getSelectors()) {
            if(sel.getType().isInductive()) {            
              SelectorImpl sel0 = (SelectorImpl) sel;
              final InductiveType selType = (InductiveType) sel.getType();
              try {
                InductiveTypeImpl t = Iterables.find(types,
                    new Predicate<InductiveTypeImpl>() {
                  @Override
                  public boolean apply(InductiveTypeImpl t) {
                    return t.getName().equals(selType.getName());
                  }
                });
              sel0.setType(t);
              } catch (NoSuchElementException e) {
                throw new TheoremProverException("Stub type not found: "
                    + selType.toString());
              }
            }
          }
        }
      }
      
      return types;
    }
    
    private void flushState() {
      typeNames.add(currentName);
      constructorLists.add(currentConstructors);
      constructorNameLists.add(currentConstructorNames);
      selectorNameListLists.add(currentSelectorNameLists);
      selectorTypeListLists.add(currentSelectorTypeLists);
      selectorUninterTypeListLists.add(currentSelectorUninterTypeLists);
      selectorTypeRefListLists.add(currentSelectorTypeRefLists);
    }

    public Builder newType(String name) {
      if( currentName != null ) {
        flushState();
      }
      currentName = name;
      currentConstructors = Lists.newArrayList();
      currentConstructorNames = Lists.newArrayList();
      currentSelectorNameLists = Lists.newArrayList();
      currentSelectorTypeLists = Lists.newArrayList();
      currentSelectorUninterTypeLists = Lists.newArrayList();
      currentSelectorTypeRefLists = Lists.newArrayList();
      return this;
    }
  }
  
  static class ConstructorImpl implements Constructor {
    static ConstructorImpl valueOf(Constructor constructor) {
      if( constructor instanceof ConstructorImpl ) {
        return (ConstructorImpl) constructor;
      } else {
        throw new UnsupportedOperationException();
//        return new Constructor(constructor.getName(),constructor.getSelectors());
      }
    }
    
    private final ExpressionManagerImpl exprManager;
    private final String name;
    private ImmutableList<SelectorImpl> selectors;
    private InductiveTypeImpl type;
    private com.microsoft.z3.Constructor z3Constructor;
    
    ConstructorImpl(ExpressionManagerImpl exprManager, String name, Selector...selectors) {
      this(exprManager, name,ImmutableList.of(selectors));
    }
    
    ConstructorImpl(ExpressionManagerImpl exprManager, String name, List<? extends Selector> selectors) {
      this.exprManager = exprManager;
      this.name = name;
      ImmutableList.Builder<SelectorImpl> listBuilder = new ImmutableList.Builder<SelectorImpl>();
      for( Selector iSelector : selectors ) {
        SelectorImpl selector = SelectorImpl.valueOf(iSelector);
        selector.setConstructor(this);
        listBuilder.add(selector);
      }
      this.selectors = listBuilder.build();
    }

    @Override
    public InductiveExpression apply(Expression... args) {
      return InductiveExpressionImpl.create(this, args);
    }

    @Override
    public InductiveExpression apply(Iterable<? extends Expression> args) {
      return InductiveExpressionImpl.create(this, args);
    }

    @Override
    public int getArity() {
      return getSelectors().size();
    }
    
    @Override
    public ExpressionManagerImpl getExpressionManager() {
      return exprManager;
    }
    
    @Override
    public String getName() {
      return name;
    }

    @Override
    public ImmutableList<SelectorImpl> getSelectors() {
      return selectors;
    }

    @Override
    public InductiveType getType() {
      return type;
    }

    public void setType(InductiveTypeImpl type) {
      this.type = type;
    }
    
    public com.microsoft.z3.Constructor getZ3Constructor() {
      return this.z3Constructor;
    }
    
    public void setZ3Constructor(com.microsoft.z3.Constructor z3Constructor) {
      this.z3Constructor = z3Constructor;
    }

    @Override
    public String toString() {
      return getName() + getSelectors();
    }
  }
  
  static class SelectorImpl implements Selector {
    
    static SelectorImpl valueOf(Selector selector) {
      if( selector instanceof SelectorImpl ) {
        return (SelectorImpl) selector;
      } else {
        throw new UnsupportedOperationException();
//        return new Selector<T>(selector.getName(),selector.getTypeDescriptor());
      }
    }

    private final ExpressionManagerImpl exprManager;
    private Type type;
    private int typeRef;
    private final String name;
    private Constructor constructor;

    SelectorImpl(ExpressionManagerImpl exprManager, String name, Type type, Integer ref) {
//      Preconditions.checkArgument(type.isKind());
      this.exprManager = exprManager;
      this.name = name;
      this.type = type;
      if(ref == null) this.typeRef = -1;
      else this.typeRef = ref;
    }

    @Override
    public Expression apply(Expression x) {
      try {
        com.microsoft.z3.Constructor cons = ((ConstructorImpl) constructor).getZ3Constructor();
        FuncDecl[] fieldAccess = cons.AccessorDecls();
        int index = constructor.getSelectors().indexOf(this);
        final FuncDecl func = fieldAccess[index];
        Expression result = new ExpressionImpl(exprManager,
            new ExpressionImpl.FuncApplyConstructionStrategy() {
              @Override
              public Expr apply(Context ctx, FuncDecl func, Expr[] exprs) {
                  try {
                    return ctx.MkApp(func, exprs);
                  } catch (Z3Exception e) {
                    throw new TheoremProverException(e);
                  }
              }
            }, FunctionDeclarator.create(exprManager, func), x);
        return result;
      } catch (Z3Exception e) {
        throw new TheoremProverException(e);
      }
    }

    @Override
    public Constructor getConstructor() {
      return constructor;
    }

    @Override
    public ExpressionManagerImpl getExpressionManager() {
      return exprManager;
    }
    
    @Override
    public String getName() {
      return name;
    }

    @Override
    public Type getType() {
      return this.type;
    }
    
    @Override
    public int getTypeRef() {
      return this.typeRef;
    }

    public void setConstructor(Constructor constructor) {
      this.constructor = constructor;
    }

    public void setType(Type t) {
      this.type = t;
    }

    @Override
    public String toString() {
      Type type = (Type) getType();
      /* Need to make sure we don't infinitely recurse on inductive types */
      if (type instanceof InductiveType /*&& !typeExpr.getType().isKind()
          || !typeExpr.getType().asKind().isStub()*/) {
        return getName() + ":" + ((InductiveType)type).getName() + "[...]";
      } else {
        return getName() + ":" + type;
      }
    }
  }
  
  static ConstructorImpl constructor(ExpressionManagerImpl exprManager, String name, Selector... selectors) {
    ConstructorImpl constr = new ConstructorImpl(exprManager, name, selectors);
    constructorCache.get(exprManager).put(name, constr);
    return constr;
  }
  
  static ConstructorImpl lookupConstructor(ExpressionManagerImpl exprManager, String name) {
    return constructorCache.get(exprManager).get(name);
  }
  
/*
  public static <T extends IType> ISelector<T> selector(String name, T type) {
    return new Selector<T>(name,type);
  }
*/

  static InductiveTypeImpl create(ExpressionManagerImpl expressionManager,
      String name, Constructor... constructors) {
    return create(expressionManager, name, ImmutableList.of(constructors));
  }
  
  @SuppressWarnings("unchecked")
  public static InductiveTypeImpl create(ExpressionManagerImpl expressionManager,
      String name, List<? extends Constructor> constructors) {
    List<InductiveTypeImpl> types = recursiveTypes(expressionManager, ImmutableList
        .of(name), constructors);
    assert( types.size() == 1 );
    return types.get(0);
    
/*    Context ctx = expressionManager
        .getTheoremProver()
        .getValidityChecker();

    List<String> constructorNames = Lists
        .newArrayListWithExpectedSize(constructors.size());
    List<List<String>> selectorLists = Lists
        .newArrayListWithExpectedSize(constructors.size());
    List<List<ExprMut>> selectorTypeLists = Lists
        .newArrayListWithExpectedSize(constructors.size());

    for (IConstructor constr : constructors) {
      constructorNames.add(constr.getName());
      List<? extends ISelector<?>> selectors = constr.getSelectors();
      List<String> selectorNames = Lists.newArrayListWithExpectedSize(selectors.size());
      List<ExprMut> selectorTypes = 
        Lists.newArrayListWithExpectedSize(selectors.size());
      for( ISelector<?>  selector : selectors ) {
        selectorNames.add( selector.getName() );
        selectorTypes.add( ExpressionManager.toZ3Expr( selector.getTypeDescriptor() ));
      }
      selectorLists.add(selectorNames);
      selectorTypeLists.add(selectorTypes);
    }
    TypeMut type = ctx.dataType(name, constructorNames, selectorLists,
        selectorTypeLists);
    
    return new InductiveType(expressionManager, type, name, constructors);
*/
    }

  static ImmutableList<InductiveTypeImpl> recursiveTypes(
      ExpressionManagerImpl expressionManager, List<String> names,
      List<? extends Constructor>... constructorLists) {
    checkArgument(names.size() == constructorLists.length, "Inconsistent list sizes");

    Builder builder = new Builder(expressionManager);
    int i = 0;
    for (String name : names) {
      builder.newType(name);
      for (Constructor constructor : constructorLists[i]) {
        builder.addConstructor(constructor);
      }
      i++;
    }
    return builder.build(expressionManager);
  }
  
  /*
   * Create a set of mutually recursive datatypes. NOTE: This method will throw
   * an exception if one of the datatype names is not globally unique (i.e.,
   * every datatype name must be unique).
   * 
   * @param expressionManager an ExpressionManager
   * 
   * @param names the suggested names of the datatypes
   * 
   * @param constructorLists lists of constructors associated with each
   * datatype. The number of lists must be exactly <code>names.size()</code>.
   * 
   * @throws IllegalArgumentException if the number of construtor list arguments
   * is not <code>names.size()</code>
   */
  
  static SelectorImpl selector(ExpressionManagerImpl exprManager, String name, Type type, int ref) {
    return new SelectorImpl(exprManager, name, type, ref);
  }
  
  static SelectorImpl selector(ExpressionManagerImpl exprManager, String name, Type type) {
    return new SelectorImpl(exprManager, name, type, null);
  }

  /*  
  public static InductiveType create(ExpressionManager expressionManager, String name, List<String> constructors,
      List<List<String>> selectorLists,
      List<List<IExpression>>> selectorTypeLists) throws Exception {
    if( constructors.size() != selectorLists.size() || selectorLists.size() != selectorTypeLists.size() ) {
      throw new IllegalArgumentException("Inconsistent arguments");
    }
    Context ctx = expressionManager.getTheoremProver().getValidityChecker();
    TypeMut type = ctx.dataType(name,constructors,selectorLists,selectorTypeLists);
    return new InductiveType(expressionManager,type,name,constructors,selectorLists,selectorTypeLists);
  }
*/
/*  
  public static InductiveType create(ExpressionManager expressionManager,
      String name, String constructor, List<String> selectors,
      List<IExpression>> selectorTypes) throws Exception {
    return create(expressionManager, name,
        Collections.singletonList(constructor),
        Collections.singletonList(selectors),
        Collections.singletonList(selectorTypes));
  }
*/  
/*
  public static Map<String,InductiveType> recursiveTypes(ExpressionManager expressionManager, List<String> names,
           List<List<String>> constructorLists, List<List<List<String>>> selectorListLists,
           List<List<List<IExpression>>>> selectorTypeListLists) throws Exception {
    if (names.size() != constructorLists.size()
        || constructorLists.size() != selectorListLists.size()
        || selectorListLists.size() != selectorTypeListLists.size()) {
      throw new IllegalArgumentException("Inconsistent arguments");
    }

    Context ctx = expressionManager.getTheoremProver().getValidityChecker();
    @SuppressWarnings("unchecked")
    List<TypeMut> cvc_types = ctx.dataType(names, constructorLists, selectorListLists, selectorTypeListLists);
    assert( cvc_types.size() == names.size() );
    
    
    Iterator<TypeMut> typeIter = cvc_types.iterator();
    Iterator<String> nameIter = names.iterator();
    Iterator<List<String>> constrIter = constructors.iterator();
    Iterator<List<List<String>>> selIter = selectors.iterator();
    
    int i=0;
    Map<String,InductiveType> typeMap = Maps.newHashMapWithExpectedSize(names.size());
    for( TypeMut type : cvc_types ) {
      InductiveType t = new InductiveType(expressionManager, type,
          names.get(i), constructorLists.get(i), selectorListLists.get(i),
          selectorTypeListLists.get(i));
      typeMap.put(names.get(i), t);
      i++;
    }
    
    return Collections.unmodifiableMap(typeMap);
  }
 */ 
  static InductiveTypeImpl stub(ExpressionManagerImpl exprManager, String name) {
    return new InductiveTypeImpl(exprManager,name);
  }
  
  private final String name;
  private final ImmutableList<Constructor> constructors;
//  private final boolean stub;

  private InductiveTypeImpl(ExpressionManagerImpl expressionManager, Sort z3Type,
      String name, List<? extends Constructor> constructors) {
    super(expressionManager);
    setZ3Type(z3Type);
    this.name = name;
    this.constructors = ImmutableList.copyOf(constructors);
    expressionManager.addToInductiveTypeCache(this);
  }
  
  /** Private constructor for stubs only. */
  private InductiveTypeImpl(ExpressionManagerImpl expressionManager,String name) {
    super(expressionManager);
    this.name = name;
    this.constructors = ImmutableList.of();
    UninterpretedSort type;
    try {
      type = expressionManager.getTheoremProver().getZ3Context().MkUninterpretedSort(name);
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
    setZ3UnresolvedDatatype(type);
    // We don't addToCache here because this is only a stub
  }
  
  @Override
  public InductiveExpression construct(Constructor constructor,
      Expression... args) {
    return InductiveExpressionImpl.create(constructor, args);
  }

  @Override
  public InductiveExpression construct(Constructor constructor,
      Iterable<? extends Expression> args) {
    return InductiveExpressionImpl.create(constructor,args);
  }

  @Override
  public ImmutableList<Constructor> getConstructors() {
    return constructors;
  }

/*  @Override
  public boolean isStub() {
    return stub;
  }
*/
/*  @Override
  public List<String> getSelectors(String constr) {
    return selectors.get(constr);
  }
  */

  @Override
  public DomainType getDomainType() {
    return DomainType.DATATYPE;
  }

  public String getName() {
    return name;
  }

  @Override
  public Expression select(Selector s,
      Expression x) {
    return s.apply(x);
  }

  @Override
  public BooleanExpression test(Constructor c, Expression x) {
    try {
      ExpressionManagerImpl exprManager = getExpressionManager();
      com.microsoft.z3.Constructor cons = ((ConstructorImpl) c).getZ3Constructor();
      final FuncDecl func = cons.TesterDecl();
      Expression result = new ExpressionImpl(exprManager, 
          new ExpressionImpl.FuncApplyConstructionStrategy() {
            @Override
            public Expr apply(Context ctx, FuncDecl func, Expr[] exprs) {
                try {
                  return ctx.MkApp(func, exprs);
                } catch (Z3Exception e) {
                  throw new TheoremProverException(e);
                }
            }
          }, FunctionDeclarator.create(exprManager, func), x);
      return result.asBooleanExpression();
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public String toString() {
    return getName() + getConstructors();
  }

  @Override
  public InductiveVariableImpl variable(final String name, boolean fresh) {
    return InductiveVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public ExpressionImpl importExpression(
      Expression expression) {
    throw new UnsupportedOperationException();
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    return variable(name, fresh);
  }
}
