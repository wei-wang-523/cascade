package edu.nyu.cascade.cvc4;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Arrays;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Datatype;
import edu.nyu.acsys.CVC4.DatatypeConstructor;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.acsys.CVC4.DatatypeUnresolvedType;
import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.vectorDatatype;
import edu.nyu.acsys.CVC4.vectorDatatypeType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.CacheException;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public class InductiveTypeImpl extends TypeImpl implements InductiveType {
  
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, ConstructorImpl>> constructorCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, ConstructorImpl>>(){
            public ConcurrentMap<String, ConstructorImpl> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  
  static class Builder {
    private final List<String> typeNames; 
    private final List<List<ConstructorImpl>> constructorLists;
    private final List<List<String>> constructorNameLists;
    private final List<List<List<String>>> selectorNameListLists;
    private final List<List<List<edu.nyu.acsys.CVC4.Type>>> selectorTypeListLists;
    private final List<List<List<DatatypeUnresolvedType>>> selectorUnresolvedTypeListLists;
    private String currentName;
    private List<ConstructorImpl> currentConstructors;
    private List<String> currentConstructorNames;
    private List<List<String>> currentSelectorNameLists;
    private List<List<edu.nyu.acsys.CVC4.Type>> currentSelectorTypeLists;
    private List<List<DatatypeUnresolvedType>> currentSelectorUnresolvedTypeLists;
    private final ExpressionManagerImpl exprManager;
    
    public Builder(ExpressionManagerImpl exprManager) {
      this.exprManager = exprManager;
      typeNames = Lists.newArrayList();
      constructorLists= Lists.newArrayList();
      constructorNameLists = Lists.newArrayList();
      selectorNameListLists = Lists.newArrayList();
      selectorTypeListLists = Lists.newArrayList();
      selectorUnresolvedTypeListLists = Lists.newArrayList();
      currentName = null;
      currentConstructors = Lists.newArrayList();
      currentConstructorNames = Lists.newArrayList();
      currentSelectorNameLists = Lists.newArrayList();
      currentSelectorTypeLists = Lists.newArrayList();
      currentSelectorUnresolvedTypeLists = Lists.newArrayList();
    }
    
    public Builder addConstructor(Constructor iConstructor) {
      ConstructorImpl c = ConstructorImpl.valueOf(iConstructor);
      currentConstructors.add(c);
      currentConstructorNames.add(c.getName());
      List<SelectorImpl> selectors = c.getSelectors();
      List<String> selectorNames = Lists.newArrayListWithExpectedSize(selectors.size());
      List<edu.nyu.acsys.CVC4.Type> selectorTypes = 
        Lists.newArrayListWithExpectedSize(selectors.size());
      List<DatatypeUnresolvedType> selectorUnresolvedTypes = 
          Lists.newArrayListWithExpectedSize(selectors.size());
      for( SelectorImpl  selector : selectors ) {
        selectorNames.add( selector.getName() );
        Type type = selector.getType();
        if(exprManager.toCvc4Type(type) != null) {
          selectorTypes.add( exprManager.toCvc4Type(type) );
          selectorUnresolvedTypes.add(null);
        } else {        
          selectorUnresolvedTypes.add( exprManager.toCvc4UnresolvedType(type) );
          selectorTypes.add(null);
        }
      }
      currentSelectorNameLists.add(selectorNames);
      currentSelectorTypeLists.add(selectorTypes);
      currentSelectorUnresolvedTypeLists.add(selectorUnresolvedTypes);
      return this;
    }
    
    public ImmutableList<InductiveTypeImpl> build(ExpressionManagerImpl exprManager) { 
      flushState();
      ExprManager em = exprManager.getTheoremProver().getCvc4ExprManager();
      
      if (IOUtils.debugEnabled() || IOUtils.tpFileEnabled()) {
        StringBuilder sb = new StringBuilder();
        sb.append("DATATYPE\n  ");
        int i = 0;
        for (String typeName : typeNames) {
          if (i > 0) {
            sb.append(",\n  ");
          }
          sb.append(typeName + " =\n    ");
          int j = 0;
          for (String constructorName : constructorNameLists.get(i)) {
            if (j > 0) {
              sb.append("\n  | ");
            }
            sb.append(constructorName);
            if (selectorNameListLists.get(i).get(j).size() > 0) {
              sb.append(" (");
              int k = 0;
              for (String selectorName : selectorNameListLists.get(i).get(j)) {
                if (k > 0) {
                  sb.append(", ");
                }
                sb.append(selectorName + " : ");
                edu.nyu.acsys.CVC4.Type sType = selectorTypeListLists.get(i).get(j).get(k);
                edu.nyu.acsys.CVC4.DatatypeUnresolvedType usType = 
                    selectorUnresolvedTypeListLists.get(i).get(j).get(k);
                try {
                  if(sType != null)     sb.append(sType);
                  else                  sb.append(usType.getName());
                } catch (Exception e) {
                  throw new TheoremProverException(e);
                }
                k++;
              }
              sb.append(")");
            }
            j++;
          }
          i++;
        }
        sb.append("\nEND;");
        if(IOUtils.debugEnabled())
          TheoremProverImpl.debugCommand(sb.toString());
        if(IOUtils.tpFileEnabled())
          TheoremProverImpl.tpFileCommand(sb.toString());
      }    
      
      vectorDatatypeType cvcTypes = new vectorDatatypeType();
      
      try {
        assert typeNames.size() == constructorNameLists.size()
            : "expected names and constructors vectors to be of equal length";
        assert typeNames.size() == selectorNameListLists.size()
            : "expected names and selectors vectors to be of equal length";
        assert typeNames.size() == selectorTypeListLists.size()
            : "expected names and types vectors to be of equal length";
        assert typeNames.size() == selectorUnresolvedTypeListLists.size()
            : "expected names and unresolved types vectors to be of equal length";
        
        vectorDatatype dv = new vectorDatatype();
        
        for(int i = 0; i < typeNames.size(); i++) {
          Datatype dt = new Datatype(typeNames.get(i));
          assert constructorNameLists.get(i).size() == selectorNameListLists.get(i).size()
              : "expected sub-vectors in constructors and selectors vectors to match in size";
          assert constructorNameLists.get(i).size() == selectorTypeListLists.get(i).size() 
              : "expected sub-vectors in constructors and types vectors to match in size";
          assert constructorNameLists.get(i).size() == selectorUnresolvedTypeListLists.get(i).size() 
              : "expected sub-vectors in constructors and unresolved types vectors to match in size";
          
          for(int j = 0; j < constructorNameLists.get(i).size(); j++) {
            DatatypeConstructor cons = new DatatypeConstructor(constructorNameLists.get(i).get(j));
            
            for(int k = 0; k < selectorNameListLists.get(i).get(j).size(); k++) {
              String name = selectorNameListLists.get(i).get(j).get(k);
              if(selectorTypeListLists.get(i).get(j).get(k) != null)
                cons.addArg(name, selectorTypeListLists.get(i).get(j).get(k));
              else
                cons.addArg(name, selectorUnresolvedTypeListLists.get(i).get(j).get(k));
            }
            dt.addConstructor(cons);
          }
          dv.add(dt);
        }
        cvcTypes = em.mkMutualDatatypeTypes(dv);
      } catch (Exception e) {
        throw new TheoremProverException(e);
      }
      assert( cvcTypes.size() == constructorLists.size() );
      
      ImmutableList.Builder<InductiveTypeImpl> listBuilder = new ImmutableList.Builder<InductiveTypeImpl>(); 

      for(int i = 0; i< cvcTypes.size(); i++) {
        DatatypeType cvcType = cvcTypes.get(i);
        List<ConstructorImpl> constructors = constructorLists.get(i);
        InductiveTypeImpl t = new InductiveTypeImpl(exprManager, cvcType, typeNames
            .get(i), constructors);
        for( ConstructorImpl c : constructors ) {
          c.setType(t);
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
      selectorUnresolvedTypeListLists.add(currentSelectorUnresolvedTypeLists);
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
      currentSelectorUnresolvedTypeLists = Lists.newArrayList();
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
    
    ConstructorImpl(ExpressionManagerImpl exprManager, String name, Selector...selectors) {
      this(exprManager, name, ImmutableList.copyOf(Arrays.asList(selectors)));
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
    private final String name;
    private Constructor constructor;

    SelectorImpl(ExpressionManagerImpl exprManager, String name, Type type) {
//      Preconditions.checkArgument(type.isKind());
      this.exprManager = exprManager;
      this.name = name;
      this.type = type;
    }

    @Override
    public Expression apply(Expression x) {
      return SelectExpressionImpl.create(getExpressionManager(),this, x);
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

    @Override
    public int getTypeRef() {
      // TODO Auto-generated method stub
      return 0;
    }
  }
  
  static ConstructorImpl constructor(ExpressionManagerImpl exprManager, String name, Selector... selectors) {
    ConstructorImpl constr = new ConstructorImpl(exprManager, name, selectors);
    try {
      constructorCache.get(exprManager).put(name, constr);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
    return constr;
  }
  
  static ConstructorImpl lookupConstructor(ExpressionManagerImpl exprManager, String name) {
    try {
      return constructorCache.get(exprManager).get(name);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
/*
  public static <T extends IType> ISelector<T> selector(String name, T type) {
    return new Selector<T>(name,type);
  }
*/

  static InductiveTypeImpl create(ExpressionManagerImpl expressionManager,
      String name, Constructor... constructors) {
    return create(expressionManager, name, ImmutableList.copyOf(Arrays.asList(constructors)));
  }

  
  @SuppressWarnings("unchecked")
  public static InductiveTypeImpl create(ExpressionManagerImpl expressionManager,
      String name, List<? extends Constructor> constructors) {
    List<InductiveTypeImpl> types = recursiveTypes(expressionManager, ImmutableList
        .of(name), constructors);
    assert( types.size() == 1 );
    return types.get(0);
    
/*    ExprManager em = expressionManager
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
        selectorTypes.add( ExpressionManager.toCvc4Expr( selector.getTypeDescriptor() ));
      }
      selectorLists.add(selectorNames);
      selectorTypeLists.add(selectorTypes);
    }
    TypeMut type = em.dataType(name, constructorNames, selectorLists,
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
  
  static SelectorImpl selector(ExpressionManagerImpl exprManager, String name, Type type) {
    return new SelectorImpl(exprManager, name,type);
  }

  /*  
  public static InductiveType create(ExpressionManager expressionManager, String name, List<String> constructors,
      List<List<String>> selectorLists,
      List<List<IExpression>>> selectorTypeLists) throws Exception {
    if( constructors.size() != selectorLists.size() || selectorLists.size() != selectorTypeLists.size() ) {
      throw new IllegalArgumentException("Inconsistent arguments");
    }
    ExprManager em = expressionManager.getTheoremProver().getValidityChecker();
    TypeMut type = em.dataType(name,constructors,selectorLists,selectorTypeLists);
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

    ExprManager em = expressionManager.getTheoremProver().getValidityChecker();
    @SuppressWarnings("unchecked")
    List<TypeMut> cvc_types = em.dataType(names, constructorLists, selectorListLists, selectorTypeListLists);
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

  private InductiveTypeImpl(ExpressionManagerImpl expressionManager, edu.nyu.acsys.CVC4.Type cvcType,
      String name, List<? extends Constructor> constructors) {
    super(expressionManager);
    setCVC4Type(cvcType);
    this.name = name;
    this.constructors = ImmutableList.copyOf(constructors);
    expressionManager.addToInductiveTypeCache(this);
  }
  
  /** Private constructor for stubs only. */
  private InductiveTypeImpl(ExpressionManagerImpl expressionManager,String name) {
    super(expressionManager);
    this.name = name;
    this.constructors = ImmutableList.of();
    DatatypeUnresolvedType type = new DatatypeUnresolvedType(name);
    setCVC4UnresolvedDatatype(type);
    // We don't addToCache here because this is only a stub
  }
  
/*  
  private InductiveType(ExpressionManager expressionManager, TypeMut type, String name, List<String> constructors,
      List<List<String>> selectorLists,
      List<List<IExpression>>> selectorTypeLists) throws Exception {
    super(expressionManager);
    setCVC4Type(type);
    
    this.name = name;
    this.constructors = Lists.newArrayList(constructors);
    this.selectors = Maps.newHashMap();
    this.selectorTypes = Maps.newHashMap();

     Map constructors -> selectors 
    int i=0;
    for( String constructor : constructors ) {
      List<String> selectorList = selectorLists.get(i);
      selectors.put(constructor, selectorList);

      List<IExpression>> selectorTypeList = selectorTypeLists.get(i);
      if( selectorList.size() != selectorTypeList.size() ) {
        throw new IllegalArgumentException("Inconsistent arguments");
      }

       Map selectors -> types 
      int j=0;
      for( String selector : selectorList ) {
        selectorTypes.put(selector, selectorTypeList.get(j));
        j++;
      }
      i++;
    }
  }
*/
  
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
    return SelectExpressionImpl.create(getExpressionManager(),s,x);
  }

  @Override
  public BooleanExpression test(Constructor c, Expression x) {
    return TestExpressionImpl.create(getExpressionManager(), c, x);
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
  public InductiveBoundVariableImpl boundVariable(final String name, boolean fresh) {
    return InductiveBoundVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public ExpressionImpl importExpression(
      Expression expression) {
    throw new UnsupportedOperationException();
  }
}
