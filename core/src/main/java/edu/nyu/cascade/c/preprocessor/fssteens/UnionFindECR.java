package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import xtc.type.PointerT;
import xtc.type.StructOrUnionT;
import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.fssteens.Offset.Kind;
import edu.nyu.cascade.c.preprocessor.fssteens.ValueType.ValueTypeKind;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

public class UnionFindECR {
  UnionFind<IRVar> uf;
  
  private UnionFindECR () {
    uf = UnionFind.create();
  }

  static UnionFindECR create() {
    return new UnionFindECR();
  }
  
  /**
   * Add <code>var</code> into union find
   * @param var
   */
  void add(VarImpl var) {
    uf.add(var, var.getECR());
  }
  
  /**
   * Add <code>vars</code> into union find
   * @param vars
   */
  void addAll(Iterable<VarImpl> vars) {
  	for(VarImpl var : vars) {
  		uf.add(var, var.getECR());
  	}
  }
  
  /**
   * Set type <code>e</code> as <code>type</code>
   * @param e
   * @param type
   */
  void setType(ECR e, ValueType type) { 
    ECR root = (ECR) e.findRoot();
    root.setType(type);
    
    Collection<ECR> joins = Lists.newArrayList(root.getJoins());
    for(ECR join : joins) 	
    	join(root, join);
    
    root.clearJoin();
    
    Collection<Pair<Size, ECR>> cjoins = Lists.newArrayList(root.getCjoins());
    for(Pair<Size, ECR> cjoin : cjoins)
    	cjoin(cjoin.fst(), root, cjoin.snd());
    
    root.clearCjoin();
  }
  
  /**
   * Get the type of the ECR @param e
   */
  ValueType getType(ECR e) {
    ECR root = (ECR) e.findRoot();
    return root.getType();
  }
  
  void join(Pair<ECR, Offset> pair1, Pair<ECR, Offset> pair2) {
  	if(pair1.equals(pair2)) return;
  	
  	Offset o1 = pair1.snd();
  	Offset o2 = pair2.snd();
  	
  	if(Offset.Kind.ZERO.equals(o1.getKind())) {
  		o1.addCollapses(o2.getCollapse());
  		o1.addMakeUnknowns(o2.getMakeUnknown());
  		o1.addMakeUnknown(o2);
  	} else if(Offset.Kind.ZERO.equals(o2.getKind())) {
  		makeUnknown(o2);
  	}
  	
  	join(pair1.fst(), pair2.fst());
  }
  
  void join(ECR e1, ECR e2) {
  	if(e1.equals(e2)) return;
  	
  	if(ValueTypeKind.BOTTOM.equals(getType(e1).getKind())) {
  		e1.addJoin(e2);
  		return;
  	}
  	
  	ValueType t1 = getType(e1);
  	ValueType t2 = getType(e2);
  	
  	ECR e = union(e1, e2);
  	ValueType repType = getType(e);
  	
  	ValueType type = t1.equals(t2) ? t1 : unify(t1, t2);
  	
  	if(!type.hasAddress()) {
  		type.setAddress(repType.getAddress());
  	}
  	
  	setType(e, type);
  	
  	e.addAllCjoin(Sets.newHashSet(e1.getCjoins()));
  	e.addAllCjoin(Sets.newHashSet(e2.getCjoins()));
  	e.addAllJoin(Sets.newHashSet(e1.getJoins()));
  	e.addAllJoin(Sets.newHashSet(e2.getJoins()));
  }
  
  void join(Function func1, Function func2) {
  	if(func1.isLambda() && func2.isLambda()) {
  		Collection<ECR> args1 = func1.getArgs();
  		Collection<ECR> args2 = func2.getArgs();
  		
  		assert(args1.size() == args2.size());
  		Iterator<ECR> argItr1 = args1.iterator();
  		Iterator<ECR> argItr2 = args2.iterator();
  		
  		while(argItr1.hasNext() && argItr2.hasNext()) {
  			join(argItr1.next(), argItr2.next());
  		}
  		
  		Collection<ECR> rets1 = func1.getRets();
  		Collection<ECR> rets2 = func2.getRets();
  		
  		assert(rets1.size() == rets2.size());
  		Iterator<ECR> resItr1 = rets1.iterator();
  		Iterator<ECR> resItr2 = rets2.iterator();
  		
  		while(resItr1.hasNext() && resItr2.hasNext()) {
  			join(resItr1.next(), resItr2.next());
  		}
  	}
  }
  
  void ensureSimObj(ECR e, Size rangeSize) {
  	ValueType type = getType(e);
  	ECR addr = type.getAddress();
  	
  	switch(type.getKind()) {
		case BOTTOM: {
	  	Pair<Pair<ECR, Offset>, Function> pair = createBottomLocFunc(e);
	  	Type addrXtcType = addr.getXtcType().resolve();
	  	String scopeName = addr.getType().getScopeName();
	  	
	  	Type xtcType = null;
	  	if(addrXtcType.isPointer()) {
	  		xtcType = addrXtcType.toPointer().getType();
	  	} else if(addrXtcType.isArray()) {
	  		xtcType = CType.getArrayCellType(addrXtcType);
	  	} else if(addrXtcType.isStruct() || addrXtcType.isUnion()) {
	  		xtcType = addrXtcType;
	  	} else {
	  		IOUtils.err().println("WARNING: get pointer-to type of " + addrXtcType);
	  	}
	  	
	  	ValueType simType = ValueType.simple(
	  			pair.fst(), 
	  			pair.snd(), 
	  			rangeSize, 
	  			Parent.getEmpty(), 
	  			xtcType, 
	  			scopeName);
	  	simType.setAddress(addr);
	  	setType(e, simType);	  	
			return;
		}
		case BLANK: {
			BlankType blankType = type.asBlank();
			
			Pair<Pair<ECR, Offset>, Function> pair = createBottomLocFunc(e);
	  	Type xtcType = type.getXtcType();
	  	String scopeName = type.getScopeName();
	  	
	  	ValueType simType = ValueType.simple(
	  			pair.fst(), 
	  			pair.snd(), 
	  			blankType.getSize(), 
	  			blankType.getParent(), 
	  			xtcType, 
	  			scopeName);
	  	simType.setAddress(addr);
	  	setType(e, simType);
	  	
	  	if(!(Size.isLessThan(rangeSize, blankType.getSize()))) expand(e);
			return;
		}
		case SIMPLE: {
			SimpleType simType = type.asSimple();
			Size simSize = simType.getSize();
			if(!(Size.isLessThan(rangeSize, simSize))) expand(e);
			return;
		}
		case STRUCT: {
			StructType strType = type.asStruct();
			Size strSize = strType.getSize();
			promote(e, strSize);
			return;
		}
		default:
			return;
  	}
  }
  
  void cjoin(long rangeSize, ECR e1, ECR e2) {
  	cjoin(Size.create(rangeSize), e1, e2);
  }
  
  void cjoin(Size rangeSize, ECR e1, ECR e2) {
  	if(e1.equals(e2)) return;
  	
		e1.addCjoin(rangeSize, e2);
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		
		switch(t1.getKind()) {
		case BOTTOM:	return;
		case BLANK: {
			Size size1 = t1.getSize();
			if(!Size.isLessThan(rangeSize, size1)) {
				expand(e1); 
			} else {				
				switch(t2.getKind()) {
				case BOTTOM: {
					ValueType freshType = ValueType.blank(
							rangeSize, 
							Parent.getEmpty(),
							t1.getXtcType(),
							t1.getScopeName());
					
					freshType.setAddress(t2.getAddress());
					setType(e2, freshType);
					break;
				}
				default: {
					Size size2 = t2.getSize();
					if(!Size.isLessThan(rangeSize, size2)) expand(e2);
					break;
				}
				}
			}
			break;
		}
		case SIMPLE: {
			Size size1 = t1.getSize();
			if(!Size.isLessThan(rangeSize, size1)) {
				expand(e1); 
			} else {
				SimpleType sim1 = t1.asSimple();
				switch(t2.getKind()) {
				case BOTTOM: {
					ValueType freshType = ValueType.simple(
							sim1.getLoc(), 
							sim1.getFunc(), 
							rangeSize, 
							Parent.getEmpty(),
							t1.getXtcType(),
							t1.getScopeName());
					
					freshType.setAddress(t2.getAddress());
					setType(e2, freshType);
					break;
				}
				case BLANK: {
					ValueType freshType = ValueType.simple(
							sim1.getLoc(), 
							sim1.getFunc(), 
							t2.getSize(), 
							t2.getParent(), 							
							t2.getXtcType(),
							t2.getScopeName());
					
					freshType.setAddress(t2.getAddress());
					setType(e2, freshType);
					if(!Size.isLessThan(rangeSize, t2.getSize())) expand(e2);
					break;
				}
				case SIMPLE: {
					SimpleType sim2 = t2.asSimple();
					join(sim1.getLoc(), sim2.getLoc());
					join(sim1.getFunc(), sim2.getFunc());
					if(!Size.isLessThan(rangeSize, t2.getSize())) expand(e2);
					break;
				}
				case STRUCT: {
					promote(e2, t2.getSize());
					break;
				}
				default: {
					ObjectType obj2 = t2.asObject();
					join(sim1.getLoc(), obj2.getLoc());
					join(sim1.getFunc(), obj2.getFunc());
					break;
				}
				}
			}
			break;
		}
		case STRUCT: {
			Size size1 = t1.getSize();
			if(!Size.isLessThan(rangeSize, size1)) {
				expand(e1);
			} else {
				StructType str1 = t1.asStruct();
				switch(t2.getKind()) {
				case BOTTOM: {
					ValueType t = ValueType.struct(
							str1.getMapping(), 
							rangeSize, 
							Parent.getEmpty(),
							str1.getXtcType(), 
							str1.getScopeName());
					t.setAddress(t2.getAddress());
					setType(e2, t);
					break;
				}
				case BLANK: {
					ValueType t = ValueType.struct(
							str1.getMapping(), 
							t2.getSize(), 
							t2.getParent(), 
							t2.getXtcType(), 
							t2.getScopeName());
					t.setAddress(t2.getAddress());
					setType(e2, t);
					if(!(Size.isLessThan(rangeSize, t2.getSize()))) expand(e2);
					break;
				}
				case SIMPLE: {
					promote(e2, t2.getSize());
					break;
				}
				case STRUCT: {
					if(Size.isLessThan(rangeSize, t2.getSize())) {
						boolean isCompatible = true;
						Map<Long, ECR> mapping1 = str1.getMapping();
						Map<Long, ECR> mapping2 = t2.asStruct().getMapping();
						for(Entry<Long, ECR> entry : mapping1.entrySet()) {
							long offset = entry.getKey();
							ECR ecr = entry.getValue();
							ValueType ecrType = getType(ecr);
							if(!makeCompatible(e2, ecrType.getXtcType(), offset, mapping2)) {
								isCompatible = false; break;
							}
						}
						if(isCompatible) {
							for(long offset : mapping1.keySet()) {
								ECR ecr1 = mapping1.get(offset);
								ECR ecr2 = mapping2.get(offset);
								Size size = getType(ecr1).getSize();
								cjoin(size, ecr1, ecr2);
							}
						}
					}
					
					expand(e2);
					break;
				}
				default: {
					ObjectType obj2 = t2.asObject();
					assert(obj2.getSize().isTop());
					assert(obj2.getParent().isEmpty());
					for(ECR e : str1.getMapping().values()) {
						Size size = getType(e).getSize();
						cjoin(size, e, e2);
					}
					break;
				}
				}
			}
			break;
		}
		default: {
			ObjectType obj1 = t1.asObject();
			switch(t2.getKind()) {
			case OBJECT: {
				ObjectType obj2 = t2.asObject();
				join(obj1.getLoc(), obj2.getLoc());
				join(obj2.getFunc(), obj2.getFunc());
				break;
			}
			case BOTTOM: {
				Pair<Pair<ECR, Offset>, Function> pair = createBottomLocFunc(e2);
		  	ValueType objType = ValueType.object(
		  			pair.fst(), 
		  			pair.snd(), 
		  			rangeSize, 
		  			Parent.getEmpty(), 
		  			obj1.getXtcType(), 
		  			obj1.getScopeName());
		  	objType.setAddress(t2.getAddress());
		  	setType(e2, objType);
				break;
			}
			default: {
				promote(e2, rangeSize);
				break;
			}
			}
			break;
		}
		}
	}

	/**
	 * ECR-union e1 and e2, return the updated root
	 * @param e1
	 * @param e2
	 * @return
	 */
	ECR union(ECR e1, ECR e2) {
	  uf.union(e1, e2);
	  return (ECR) e1.findRoot();
	}

	/**
   * Compute the least upper bound of <code>t1</code>
   * and <code>t2</code>
   * 
   * @param t1
   * @param t2
   * @return
   */
  ValueType unify(ValueType t1, ValueType t2) {
  	Pair<ValueType, ValueType> pair = swap(t1, t2);
  	t1 = pair.fst();
  	t2 = pair.snd();
  	
  	if(t1.getKind().equals(ValueTypeKind.BOTTOM))	return t2;
  	
  	switch(t1.getKind()) {		
		case BLANK: {
	  	Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());		
			Size size = Size.getLUB(t1.getSize(), t2.getSize());
			if(!t1.getXtcType() .equals(t2.getXtcType())) {
				IOUtils.debug().pln("WARNING: unifying xtc types " + t1.getXtcType() + ", " + t2.getXtcType());
			}
	  	Type xtcType = CType.getBottomType(t1.getXtcType(), t2.getXtcType());
	  	String scopeName = CScopeAnalyzer.getTopScope(t1.getScopeName(), t2.getScopeName());
	  	
			switch(t2.getKind()) {
			case BLANK:		return ValueType.blank(size, parent, xtcType, scopeName);
			case SIMPLE:
				return ValueType.simple(
					  t2.asSimple().getLoc(), 
						t2.asSimple().getFunc(), 
						size, 
						parent,
						xtcType, 
						scopeName);
			case STRUCT: 
				return ValueType.struct(
						t2.asStruct().getMapping(), 
						size, 
						parent,
						xtcType, 
						scopeName);
			case OBJECT:
				return ValueType.object(
						t2.asObject().getLoc(), 
						t2.asObject().getFunc(), 
						size, 
						parent,
						xtcType, 
						scopeName);
			default:
				throw new IllegalArgumentException(
						"Incompatible kinds " + t1.getKind() + ", " + t2.getKind());
			}
		}
		case SIMPLE: {
	  	Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());		
			Size size = Size.getLUB(t1.getSize(), t2.getSize());
	  	Type xtcType = CType.getBottomType(t1.getXtcType(), t2.getXtcType());
	  	String scopeName = CScopeAnalyzer.getTopScope(t1.getScopeName(), t2.getScopeName());
	  	
			switch(t2.getKind()) {
			case SIMPLE: {
				SimpleType sim1 = t1.asSimple();
				SimpleType sim2 = t2.asSimple();
				
				Pair<ECR, Offset> ptr1 = sim1.getLoc();
				Pair<ECR, Offset> ptr2 = sim2.getLoc();
				Function func1 = sim1.getFunc();
				Function func2 = sim2.getFunc();
				
				join(ptr1, ptr2);
				join(func1, func2);
				
				return ValueType.simple(
						ptr1, 
						func1, 
						size, 
						parent, 
						xtcType, 
						scopeName);
			}
			case STRUCT: {
				SimpleType sim1 = t1.asSimple();
				StructType str2 = t2.asStruct();
				
				// join components when promote structure to object
				Iterator<ECR> itr = str2.getMapping().values().iterator();
				ECR merge = itr.next();
				while(itr.hasNext()) {
					join(merge, itr.next());
				}
				
				Pair<ECR, Offset> ptr1 = sim1.getLoc();
				Pair<ECR, Offset> ptr2 = Pair.of(merge, Offset.createZero());
				join(ptr1, ptr2);
				Function func1 = sim1.getFunc();
				return ValueType.object(
						ptr1, 
						func1, 
						size, 
						parent, 
						xtcType, 
						scopeName);
			}
			case OBJECT: {
				SimpleType sim1 = t1.asSimple();
				ObjectType obj2 = t2.asObject();
				
				Pair<ECR, Offset> ptr1 = sim1.getLoc();
				Pair<ECR, Offset> ptr2 = obj2.getLoc();
				join(ptr1, ptr2);
				
				Function func1 = sim1.getFunc();
				Function func2 = obj2.getFunc();
				join(func1, func2);
				
				return ValueType.object(
						ptr1, 
						func1, 
						size, 
						parent, 
						xtcType, 
						scopeName);
			}
			default:
				throw new IllegalArgumentException(
						"Incompatible kinds " + t1.getKind() + ", " + t2.getKind());
			}
		}
		case STRUCT: {
	  	Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());		
			Size size = Size.getLUB(t1.getSize(), t2.getSize());
	  	Type xtcType = CType.getBottomType(t1.getXtcType(), t2.getXtcType());
	  	String scopeName = CScopeAnalyzer.getTopScope(t1.getScopeName(), t2.getScopeName());
	  	
			switch(t2.getKind()) {
			case STRUCT: {
				StructType str1 = t1.asStruct(), str2 = t2.asStruct();
				Map<Long, ECR> map = getCompatibleMap(str1, str2);
				return ValueType.struct(
						map, 
						size, 
						parent, 
						xtcType, 
						scopeName);
			}
			case OBJECT: {
				StructType str1 = t1.asStruct();
				ObjectType obj2 = t2.asObject();
				
				// join components when promote structure to object
				Iterator<ECR> itr = str1.getMapping().values().iterator();
				ECR merge = itr.next();
				while(itr.hasNext()) {
					join(merge, itr.next());
				}
				
				Pair<ECR, Offset> ptr1 = Pair.of(merge, Offset.createZero());
				Pair<ECR, Offset> ptr2 = obj2.getLoc();
				join(ptr1, ptr2);
				return ValueType.object(
						ptr1, 
						obj2.getFunc(), 
						size, 
						parent, 
						xtcType, 
						scopeName);
			}
			default:
				throw new IllegalArgumentException(
						"Incompatible kinds " + t1.getKind() + ", " + t2.getKind());
			}
		}
		case OBJECT: {
	  	Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());		
			Size size = Size.getLUB(t1.getSize(), t2.getSize());
	  	Type xtcType = CType.getBottomType(t1.getXtcType(), t2.getXtcType());
	  	String scopeName = CScopeAnalyzer.getTopScope(t1.getScopeName(), t2.getScopeName());
	  	
			switch(t2.getKind()) {
			case OBJECT: {
				Pair<ECR, Offset> ptr1 = t1.asObject().getLoc();
				Pair<ECR, Offset> ptr2 = t2.asObject().getLoc();
				join(ptr1, ptr2);
				
				Function func1 = t1.asObject().getFunc();
				Function func2 = t2.asObject().getFunc();
				join(func1, func2);
				
				return ValueType.object(ptr1, func1, size, parent, xtcType, scopeName);
			}
			default:
				throw new IllegalArgumentException(
						"Incompatible kinds " + t1.getKind() + ", " + t2.getKind());			
			}
		}
		
		default: // Lambda
			throw new IllegalArgumentException(
					"Incompatible kinds " + t1.getKind() + ", " + t2.getKind());
  	}
  }
  
  /**
   * Side-effecting predicate that modifies mapping <code>m</code>
   * to be compatible with access of structure element with 
   * <code>type</code> and <code>fieldName</code>, where <code>parent</code>
   * is the parent for the newly created ECR
   * 
   * @param parent
   * @param type
   * @param fieldName
   * @param m
   * @return
   */
  boolean makeCompatible(ECR parent, Type type, String fieldName, Map<Long, ECR> m) {
  	StructOrUnionT suType = type.resolve().toStructOrUnion();
  	long offset = CType.getOffset(suType, fieldName);
  	Type fieldType = CType.getOffsetType(suType, fieldName);
  	return makeCompatible(parent, fieldType, offset, m);
  }
  
  /**
   * Pick up the ECR for the <code>offset</code> in <code>mapping</code>,
   * if there's no ECR corresponding to the <code>offset</code>, then 
   * return the next larger offset's ECR (should be the last one).
   * 
   * @param mapping
   * @param offset
   * @return
   */
  ECR getComponent(Map<Long, ECR> mapping, final long offset) {
	  if(mapping.containsKey(offset)) return mapping.get(offset);
	  
	  // Find the first entry whose offset is larger than the target offset
	  Entry<Long, ECR> nextEntry = Iterables.find(mapping.entrySet(), new Predicate<Entry<Long, ECR>>(){
			@Override
      public boolean apply(Entry<Long, ECR> entry) {
				Size size = getType(entry.getValue()).getSize();
				if(size.isTop()) return true;
	      return entry.getKey() + size.getValue() > offset;
      }
	  });
	  
	  return nextEntry.getValue();
	}

	/**
   * Make the <code>o</code> as unknown
   * @param o
   */
  void makeUnknown(Offset o) {
  	if(o.isUnknown()) return;
  	
	  o.setKind(Kind.UNKNOWN);
	  for(ECR ecr : o.getCollapse()) {
	  	collapse(ecr);
	  }
	  
	  for(Offset offset : o.getMakeUnknown()) {
	  	makeUnknown(offset);
	  }
	  
	  o.cleanMakeunknown();
	  o.clearCollapse();
  }
  
  /**
   * If <code>o</code> is <code>ZERO</code>, add <code>ecr</code>
   * to the collapse pendings of <code>o</code>, otherwise, collapse
   * <code>ecr</code>
   * 
   * @param o
   * @param ecr
   */
  void unlessZero(Offset o, ECR ecr) {
  	switch(o.getKind()) {
		case ZERO: 
			o.addCollapse(ecr);
			break;
		default: 
			collapse(ecr);
			break;
  	}
  }
  
  /**
   * Expand <code>e</code> to size <code>T</code>
   * @param e
   */
  void expand(ECR e) {
  	ValueType eType = getType(e);
  	ValueType blankType = BlankType.getTop();
  	ValueType unifyType = unify(eType, blankType);
  	unifyType.setAddress(eType.getAddress());
  	setType(e, unifyType);
  }
  
  /**
   * Promote <code>e</code> to object type with <code>size</code>
   * @param e
   * @param size
   */
  void promote(ECR e, Size size) {
  	Preconditions.checkArgument(!getType(e).isBottom());
  	Pair<Pair<ECR, Offset>, Function> pair = createBottomLocFunc(e);
  	ValueType type = getType(e);
  	
  	ValueType objType = ValueType.object(
  			pair.fst(), 
  			pair.snd(), 
  			size, 
  			Parent.getEmpty(), 
  			type.getXtcType(), 
  			type.getScopeName());
  	
  	ValueType unifyType = unify(type, objType);
  	unifyType.setAddress(type.getAddress());
  	setType(e, unifyType);
  }
  
  /**
   * Collapse <code>e</code> to object type with size as <code>T</code>
   * @param e
   */
  void collapse(ECR e) {
  	Pair<Pair<ECR, Offset>, Function> pair = createBottomLocFunc(e);
  	ValueType type = getType(e);
  	
  	ValueType objType = ValueType.object(
  			pair.fst(), 
  			pair.snd(), 
  			Size.getTop(), 
  			Parent.getTop(), 
  			type.getXtcType(), 
  			type.getScopeName());
  	ValueType unifyType = unify(type, objType);
  	unifyType.setAddress(type.getAddress());
  	setType(e, unifyType);
  }

	/**
	 * Get the root of ECR <code>e</code>
	 * @param e
	 * @return
	 */
	ECR findRoot(ECR e) {
		return (ECR) e.findRoot();
	}
	
  /**
   * Get the snapshot of union find
   */
  ImmutableMap<ECR, Collection<IRVar>> snapshot() {
    SetMultimap<Partition, IRVar> map = uf.snapshot();
    ImmutableMap.Builder<ECR, Collection<IRVar>> builder = ImmutableMap.builder();
    for (Partition ecr : map.asMap().keySet()) {
      builder.put(findRoot((ECR) ecr), ImmutableSet.copyOf(map.asMap().get(ecr)));
    }
    return builder.build();
  }
  
  Collection<IRVar> getEquivClass(ECR key) {
  	return uf.getEquivClass(key);
  }
  
  /**
	 * Create a pair of bottom location and bottom function with source 
	 * ECR <code>srcECR</code>
	 * @param srcECR
	 * @return
	 */
	Pair<Pair<ECR, Offset>, Function> createBottomLocFunc(ECR srcECR) {
		ECR base = ECR.createBottom();
		base.getType().setAddress(srcECR);
		Offset off = Offset.createZero();
		Pair<ECR, Offset> loc = Pair.of(base, off);
		Function func = Function.getBottom();
		return Pair.of(loc, func);		
	}

	/**
   * Create a field ECR with <code>xtcType</code>, <code>scopeName</code>,
   * and <code>parent</code>. If <code>xtcType</code> is scalar, this
   * method creates a single field ECR, otherwise, two ECRs will be created,
   * one for the field and the other for the region it points to. For the
   * field ECR, whose address ECR will be the same as the address attached
   * with the ECR of <code>parent</code>.
   * 
   * @param xtcType
   * @param scopeName
   * @param parent
   * @return
   */
  private ECR createFieldECR(Type xtcType, String scopeName, Parent parent) {
  	Preconditions.checkArgument(!parent.isEmpty());
  	
		if(xtcType.resolve().isArray()) {
			Type cellType = CType.getArrayCellType(xtcType);
		  BlankType regionType = ValueType.blank(
		  		Size.createForType(cellType), 
		  		parent, 
		  		cellType, 
		  		scopeName);
			ECR regECR = ECR.create(regionType);
			
			Type addrXtcType = new PointerT(xtcType);
			SimpleType addrType = ValueType.simple(
					Pair.of(regECR, Offset.createZero()), 
					Function.getBottom(), 
					Size.createForType(addrXtcType), 
					Parent.getEmpty(), 
					addrXtcType, 
					scopeName);
			
			ECR addrECR = ECR.create(addrType);
			regionType.setAddress(addrECR);
			addrType.setAddress(addrECR);
			return addrECR;
		} 
		
		if(xtcType.resolve().isStruct() || xtcType.resolve().isUnion()) {
		  BlankType regionType = ValueType.blank(
		  		Size.createForType(xtcType), 
		  		parent, 
		  		xtcType, 
		  		scopeName);
			ECR regECR = ECR.create(regionType);

			Type addrXtcType = new PointerT(xtcType);
			SimpleType addrType = ValueType.simple(
					Pair.of(regECR, Offset.createZero()), 
					Function.getBottom(), 
					Size.createForType(addrXtcType), 
					Parent.getEmpty(), 
					addrXtcType, 
					scopeName);
			
			ECR addrECR = ECR.create(addrType);
			regionType.setAddress(addrECR);
			return regECR;
		} 
		
	  BlankType varType = ValueType.blank(
	  		Size.createForType(xtcType), 
	  		parent, 
	  		xtcType, 
	  		scopeName);
	  
		ECR varECR = ECR.create(varType);
		
		Type addrXtcType = new PointerT(xtcType);
		SimpleType addrType = ValueType.simple(
				Pair.of(varECR, Offset.createZero()), 
				Function.getBottom(), 
				Size.createForType(addrXtcType), 
				Parent.getEmpty(), 
				addrXtcType, 
				scopeName);
		
		ECR addrECR = ECR.create(addrType);
		varType.setAddress(addrECR);
		return varECR;
  }

	/**
	 * Get the compatible map with respect to the mapping in struct types
	 * <code>str1</code> and <code>str2</code>
	 * @param str1
	 * @param str2
	 * @return
	 */
	private Map<Long, ECR> getCompatibleMap(StructType str1, StructType str2) {
		Map<Long, ECR> resMap = Maps.newTreeMap();
		Map<Long, ECR> str1Map = str1.getMapping();
		Map<Long, ECR> str2Map = str2.getMapping();
		
		resMap.putAll(str1Map);
		
		for(long offset : str2Map.keySet()) {
			ECR ecr2 = str2Map.get(offset);
			if(resMap.containsKey(offset)) {
				ECR ecr1 = str1Map.get(offset);
				join(ecr2, ecr1);
			} 
			
			resMap.put(offset, ecr2);
		}
		
		normalizeMap(resMap);
		return resMap;
	}

	/**
	 * Normalize the map <code>m</code> to make sure no field
	 * has been overlapped
	 * @param m
	 * @return if the map has been modified
	 */
	private boolean normalizeMap(Map<Long, ECR> m) {
		Preconditions.checkNotNull(m);
		if(m.isEmpty()) return false;
		
		boolean shouldModify = false;
		long lastOffset = 0, lastSize = 0;
		
		Iterator<Long> offsetItr = Sets.newHashSet(m.keySet()).iterator();
		
		while(offsetItr.hasNext()) {
			long offset = offsetItr.next();
			
			// The current field is overlapped with the last field
			if(offset < lastOffset + lastSize) {
				shouldModify = true; break;
			}
			
			ECR ecr = m.get(offset);
			Size size = getType(ecr).getSize();
			lastOffset = offset;
			
			// The current field is with top size
			if(size.isTop()) {
				shouldModify = true; break;
			}
			
			lastSize = size.getValue();
		}
		
		if(!shouldModify) 	return false;
		
		if(!offsetItr.hasNext()) return false; // nothing to be merged
		
		ECR lastECR = m.get(lastOffset);
		while(offsetItr.hasNext()) {
			long offset = offsetItr.next();
			ECR currECR = m.remove(offset);
			join(currECR, lastECR);
		}
		
		getType(lastECR).setSize(Size.getTop());
		return true;
	}

	/**
	 * Side-effecting predicate that modifies mapping <code>m</code>
	 * to be compatible with access of structure element with <code>fieldType</code>
	 * <code>offset</code> and <code>fieldSize</code>, where <code>parent</code>
	 * is the parent for the newly created ECR
	 * 
	 * @param parent
	 * @param fieldType
	 * @param offset
	 * @param m
	 * @return
	 */
	private boolean makeCompatible(ECR parent, 
			Type fieldType, long offset, Map<Long, ECR> m) {
		if(m.containsKey(offset)) return true;
		
		parent = findRoot(parent);
		String scopeName = getType(parent).getScopeName();
		ECR ecr = createFieldECR(fieldType, scopeName, Parent.createParent(parent));
		
		m.put(offset, ecr);
		
		normalizeMap(m);
		
		return m.containsKey(offset);
	}

	/**
	 * Swap <code>t1</code> and <code>t2</code> to keep the order 
	 * with respect to their kinds:
	 * 	BOTTOM < BLANK < SIMPLE < STRUCT < OBJECT < LAMBDA
	 * @param t1
	 * @param t2
	 * @return
	 */
	private Pair<ValueType, ValueType> swap(ValueType t1, ValueType t2) {
		ValueTypeKind kind1 = t1.getKind();
		switch(kind1) {
		case BOTTOM: return Pair.of(t1, t2);
		case BLANK:
			switch(t2.getKind()) {
			case BOTTOM:
			case BLANK:
				return Pair.of(t2, t1);
			case SIMPLE:
			case STRUCT:
			case OBJECT:
				return Pair.of(t1, t2);			
			}
		case SIMPLE:
			switch(t2.getKind()) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
				return Pair.of(t2, t1);
			case OBJECT:
			case STRUCT:
				return Pair.of(t1, t2);			
			}
		case STRUCT:
			switch(t2.getKind()) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
			case STRUCT:
				return Pair.of(t2, t1);
			case OBJECT:
				return Pair.of(t1, t2);			
			}
		default: //case OBJECT
			return Pair.of(t2, t1);
		}
	}
}
