package edu.nyu.cascade.c.preprocessor.steensfs;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.steensfs.Offset.Kind;
import edu.nyu.cascade.c.preprocessor.steensfs.ValueType.ValueTypeKind;
import edu.nyu.cascade.util.FieldRangeMap;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

class UnionFindECR {
  final UnionFind<IRVar> uf;
  
  private UnionFindECR () {
    uf = UnionFind.create();
  }

  static UnionFindECR create() {
    return new UnionFindECR();
  }
  
  void reset() {
  	uf.reset();
  }
  
  /**
   * Add <code>var</code> into union find
   * @param var
   */
  void add(VarImpl var) {
    uf.add(var, var.getECR());
  }
  
  /**
   * Set type <code>e</code> as <code>type</code>
   * @param e
   * @param type
   */
  void setType(ECR e, ValueType type) {
  	ECR root = findRoot(e);
  	root.setType(type);
  	
  	Collection<Pair<Size, ECR>> ccjoins = ImmutableList.copyOf(root.getCCjoins());
  	root.clearCCjoins(ccjoins);
  	for(Pair<Size, ECR> cjoinPair : ccjoins)
  		ccjoin(cjoinPair.fst(), root, cjoinPair.snd());
  	
  	Collection<ECR> cjoins = ImmutableList.copyOf(root.getCjoins());
  	root.clearCjoins(cjoins);
  	for(ECR joinECR : cjoins)	cjoin(root, joinECR);
  }
  
  /**
   * Get the type of the ECR @param e
   */
  ValueType getType(ECR e) {
    return findRoot(e).getType();
  }
  
  ECR join(ECR e1, ECR e2) {
		if(e1.equals(e2)) return e1;
		
		checkStructCollapse(e1, e2);
		
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		
		Offset o1 = getOffset(e1);
		Offset o2 = getOffset(e2);
		
		Collection<Pair<Size, ECR>> ccjoins1 = ImmutableList.copyOf(getCCjoins(e1));
		Collection<Pair<Size, ECR>> ccjoins2 = ImmutableList.copyOf(getCCjoins(e2));
		
		Collection<ECR> cjoins1 = ImmutableList.copyOf(getCjoins(e1));
		Collection<ECR> cjoins2 = ImmutableList.copyOf(getCjoins(e2));
		
		ECR root = union(e1, e2);
		
	  switch(t1.getKind()) {
		case BOTTOM: {
			switch(t2.getKind()) {
			case BOTTOM: {
				Collection<ECR> cjoins = Sets.newHashSet();
				cjoins.addAll(cjoins1);
				cjoins.addAll(cjoins2);
				root.addCjoins(cjoins);
				
				Collection<Pair<Size, ECR>> ccjoins = Sets.newHashSet();
				ccjoins.addAll(ccjoins1);
				ccjoins.addAll(ccjoins2);
				root.addCCjoins(ccjoins);
				
				break;
			}
			default: {
				root.setType(t2);
				
				root.clearCCjoins(ccjoins1);
				for(Pair<Size, ECR> pair : ccjoins1) ccjoin(pair.fst(), root, pair.snd());
				
				root.clearCjoins(cjoins1);
				for(ECR cjoin : cjoins1) cjoin(root, cjoin);
				
	      break;
			}
			}
			break;
		}
		default: {
			switch(t2.getKind()) {
			case BOTTOM: {
				root.setType(t1);
				
				root.clearCCjoins(ccjoins2);
				for(Pair<Size, ECR> pair : ccjoins2) ccjoin(pair.fst(), root, pair.snd());
				
				root.clearCjoins(cjoins2);
				for(ECR cjoin : cjoins2) cjoin(root, cjoin);
				
	      break;
			}
			default: {
				root.setType(t1);
				ValueType unionType = unify(t1, t2);
				
				ValueType freshType = getType(root);
				if(!freshType.equals(t1))	{
					unionType = resolveType(root, unionType, freshType);
				}
				
				root.setType(unionType);
				
				root.clearCCjoins(ccjoins1);
				root.clearCCjoins(ccjoins2);
				
				for(Pair<Size, ECR> pair : ccjoins1) ccjoin(pair.fst(), root, pair.snd());
				for(Pair<Size, ECR> pair : ccjoins2) ccjoin(pair.fst(), root, pair.snd());
				break;
			}
			}
			break;
		}
	  }
		
		if(o1 != null && o2 != null) {
	  	if(o1.isUnknown() || o2.isUnknown()) {
	  		makeUnknown(o1);
	  		makeUnknown(o2);
	  		setOffset(root, Offset.createUnknown());
	  	} else {
	  		o1.addUnknown(o2);
	  		o1.addCollapses(o2.getCollapse());
	  		o1.addUnknowns(o2.getUnknown());
	  		setOffset(root, o1);
	  	}
		}
		
		return root;
	}

	ECR cjoin(ECR e1, ECR e2) {
  	if(e1.equals(e2)) return findRoot(e1);
  	
  	if(getType(e1).isBottom()) {
  		
  		Collection<ECR> joins2 = getCjoins(e2);
  		Collection<Pair<Size, ECR>> cjoins2 = getCCjoins(e2);
  		
  		Offset o1 = getOffset(e1);
  		Offset o2 = getOffset(e2);
  		
  		addCjoin(e1, e2); 
  		addCjoins(e1, joins2);
  		addCCjoins(e1, cjoins2);
  		if(o1 != null && o1.isUnknown()) makeUnknown(o2);
  		
  		return findRoot(e1);
  	}
  	
		return join(e1, e2);
  }
  
  void ccjoin(Size rangeSize, ECR e1, ECR e2) {	
  	ValueType type1 = getType(e1);
  	if(type1.isBottom()) {
  		addCCjoin(rangeSize, e1, e2);
  		return;
  	}
  	
		Size size1 = type1.getSize();
		if(!Size.isLessThan(rangeSize, size1)) {
			addCCjoin(rangeSize, e1, e2);
			expand(e1); // expand(e1) would call setType(e1, ...) and thus ccjoin(e1, e2)
			return;
		}
		
		if(e1.equals(e2)) return;
		
  	switch(type1.getKind()) {
  	case BLANK: {
  		addCCjoin(rangeSize, e1, e2);
  		ValueType type2 = getType(e2);
  		switch(type2.getKind()) {
			case BOTTOM:
				setType(e2, ValueType.blank(rangeSize, Parent.getBottom()));
				return;
			default:
				Size size2 = type2.getSize();
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				return;
  		}
  	}
  	case SIMPLE: {
  		ValueType type2 = getType(e2);
  		switch(type2.getKind()) {
			case BOTTOM:
				setType(e2, ValueType.simple(
						type1.asSimple().getLoc(), type1.asSimple().getFunc(), rangeSize, Parent.getBottom()));
				return;
			case BLANK: {
				setType(e2, ValueType.simple(
						type1.asSimple().getLoc(), type1.asSimple().getFunc(), type2.getSize(), type2.getParent()));
				Size size2 = type2.getSize();
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				return;
			}
			case SIMPLE: {
				cjoin(type1.asSimple().getLoc(), type2.asSimple().getLoc());
				cjoin(type1.asSimple().getFunc(), type2.asSimple().getFunc());
				Size size2 = type2.getSize();
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				return;
			}
			case STRUCT: {
				addCCjoin(rangeSize, e1, e2);
				collapseStruct(e2, type2.asStruct());
				return;
			}
			case OBJECT: {
				cjoin(type1.asSimple().getLoc(), type2.asObject().getLoc());
				cjoin(type2.asObject().getFunc(), type2.asObject().getFunc());
				Size size2 = type2.getSize();
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				return;
			}
			default: // lambda
				return;
  		}
  	}
  	case STRUCT: {
  		ValueType type2 = getType(e2);
  		switch(type2.getKind()) {
			case BOTTOM: {
				RangeMap<Long, ECR> fieldMapCopy = FieldRangeMap.create();
				fieldMapCopy.putAll(type1.asStruct().getFieldMap());
				setType(e2, ValueType.struct(fieldMapCopy, rangeSize, Parent.getBottom()));
				return; 
  		}
			case BLANK: {
				RangeMap<Long, ECR> fieldMapCopy = FieldRangeMap.create();
				fieldMapCopy.putAll(type1.asStruct().getFieldMap());
				Size size2 = type2.getSize();
				setType(e2, ValueType.struct(fieldMapCopy, size2, type2.getParent()));
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				return;
			}
			case SIMPLE: {
				addCCjoin(rangeSize, e1, e2);
				Size size2 = type2.getSize();
				promote(e2, size2);
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				for(ECR elemECR : type1.asStruct().getFieldMap().asMapOfRanges().values()) {
					ValueType elemType = getType(elemECR);
					Size elemSize = elemType.getSize();
					ccjoin(elemSize, elemECR, e2);
				}
				return;
			}
			case OBJECT: {
				addCCjoin(rangeSize, e1, e2);
				Size size2 = type2.getSize();
				if(!Size.isLessThan(rangeSize, size2)) expand(e2);
				for(ECR elemECR : type1.asStruct().getFieldMap().asMapOfRanges().values()) {
					ValueType elemType = getType(elemECR);
					Size elemSize = elemType.getSize();
					ccjoin(elemSize, elemECR, e2);
				}
				return;
			}
			case STRUCT: {
				throw new IllegalArgumentException();
//				Size size2 = type2.getSize();
//				if(!Size.isLessThan(rangeSize, size2)) {
//					addCCjoin(rangeSize, e1, e2);
//					expand(e2); return;
//				}
//				
//				ValueType unifyStructType = unify(type1, type2); // unify structure type eagerly
//				setType(e1, unifyStructType);
//				setType(e2, unifyStructType);
//				return;
			}
			default: return; // lambda
  		}
  	}
  	case OBJECT: {
  		ValueType type2 = getType(e2);
  		if(!type2.isObject()) {
    		promote(e2, rangeSize);
    		type2 = getType(e2);
  		}

			cjoin(type1.asObject().getLoc(), type2.asObject().getLoc());
			cjoin(type1.asObject().getFunc(), type2.asObject().getFunc());
			return;
  	}
		default: return; // lambda
  	}
  }
  
  /**
   * Make the <code>o</code> as unknown
   * @param o
   */
  void makeUnknown(Offset o) {
  	if(o.isUnknown()) return;
  	
	  o.setKind(Kind.UNKNOWN);
	  for(ECR ecr : o.getCollapse()) collapse(ecr);
	  
	  o.clearCollapse();
	  
	  for(Offset off : o.getUnknown()) makeUnknown(off);
	  
	  o.clearUnknown();
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
  	ValueType blankType = ValueType.blank(Size.getTop(), Parent.getBottom());
  	ValueType unifyType = unify(eType, blankType);
  	setType(e, unifyType);
  }
  
  /**
   * Promote <code>e</code> to object type with <code>size</code>
   * @param e
   * @param size
   */
  void promote(ECR e, Size size) {
  	ValueType type = getType(e);
  	if(type.isStruct()) 
  		type = collapseStruct(e, type.asStruct());
  	
  	ValueType objType = ValueType.object(
  			createBottomLocFunc(), 
  			size, 
  			Parent.getBottom());
  	
  	ValueType unifyType = unify(type, objType);
  	setType(e, unifyType);
  }
  
  /**
   * Collapse <code>ecr</code> to object type with size as <code>T</code>
   * @param ecr
   */
  void collapse(ECR ecr) {
  	ValueType type = getType(ecr);
  	if(type.isStruct())
  		type = collapseStruct(ecr, type.asStruct());

  	Collection<ECR> parentECRs = type.getParent().getECRs();
  	
  	ValueType objType = ValueType.object(
  			createBottomLocFunc(), 
  			Size.getTop(), 
  			Parent.getTop());
  	
  	ValueType unifyType = unify(type, objType);
  	setType(ecr, unifyType);
  	
  	for(ECR parentECR : parentECRs)	collapse(parentECR);
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
	 * Unify value types <code>t1</code> and <code>t2</code>
	 * 
	 * @param t1
	 * @param t2
	 * @return a unified value type
	 */
	ValueType unify(ValueType t1, ValueType t2) {
		Pair<ValueType, ValueType> pair = swap(t1, t2);
		t1 = pair.fst();
		t2 = pair.snd();
		if(t1.equals(t2)) return t1;
		if(t1.isBottom()) return t2;
		
		Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());		
		Size size = Size.getLUB(t1.getSize(), t2.getSize());
		
		switch(t1.getKind()) {
		case BLANK: {
			switch(t2.getKind()) {
			case BLANK:		
				return ValueType.blank(size, parent);
			case SIMPLE:
				return ValueType.simple(
					  t2.asSimple().getLoc(), 
						t2.asSimple().getFunc(), 
						size, 
						parent);
			case STRUCT: 
				return ValueType.struct(
						t2.asStruct().getFieldMap(), 
						size, 
						parent);
			default: // case OBJECT: 
				return ValueType.object(
						t2.asObject().getLoc(), 
						t2.asObject().getFunc(), 
						size, 
						parent);
			}
		}
		case SIMPLE: {
			switch(t2.getKind()) {
			case SIMPLE: {
				ECR loc1 = t1.asSimple().getLoc();
				ECR loc2 = t2.asSimple().getLoc();
				ECR func1 = t1.asSimple().getFunc();
				ECR func2 = t2.asSimple().getFunc();
				
				ECR loc = join(loc1, loc2);
				ECR func = join(func1, func2);
				
				return ValueType.simple(loc, func, size, parent);
			}
			case STRUCT: {
				throw new IllegalArgumentException();
			}
			default: {				
				ECR loc1 = t1.asSimple().getLoc();
				ECR func1 = t1.asSimple().getFunc();
				
				ECR loc2 = t2.asObject().getLoc();
				ECR func2 = t2.asObject().getFunc();
				
				ECR loc = join(loc1, loc2);
				ECR func = join(func1, func2);
				
				return ValueType.object(loc, func, size, parent);
			}
			}
		}
		case STRUCT: {
			if(ValueTypeKind.STRUCT.equals(t2.getKind())) {
				RangeMap<Long, ECR> map = getCompatibleMap(t1.asStruct(), t2.asStruct());
				return ValueType.struct(map, size, parent);
			} else {
				throw new IllegalArgumentException();
			}
		}
		case OBJECT: {
			assert(ValueTypeKind.OBJECT.equals(t2.getKind()));
			ECR loc1 = t1.asObject().getLoc();
			ECR loc2 = t2.asObject().getLoc();
			ECR func1 = t1.asObject().getFunc();
			ECR func2 = t2.asObject().getFunc();
			
			ECR loc = join(loc1, loc2);
			ECR func = join(func1, func2);
			
			return ValueType.object(loc, func, size, parent);
		}
		default: // Lambda
			assert(t2.isLambda());
			
			List<ECR> params = Lists.newArrayList();
			Iterator<ECR> paramItr1 = t1.asLambda().getParams().iterator();
			Iterator<ECR> paramItr2 = t2.asLambda().getParams().iterator();
			while(paramItr1.hasNext() && paramItr2.hasNext()) {
				ECR param1 = paramItr1.next();
				ECR param2 = paramItr2.next();
				ECR param = join(param1, param2);
				params.add(param);
			}
			
			while(paramItr1.hasNext()) params.add(paramItr1.next());
			while(paramItr2.hasNext()) params.add(paramItr2.next());
			
			ECR ret1 = t1.asLambda().getRet();
			ECR ret2 = t2.asLambda().getRet();
			ECR ret = join(ret1, ret2);
			
			return ValueType.lam(ret, params, size, parent);
		}
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
  
  ECR getLoc(ECR srcECR) {
		ValueType type = getType(srcECR);
		ensureSimObj(srcECR, type.getSize());
		type = getType(srcECR);
		ECR loc = type.isSimple() ? type.asSimple().getLoc() 
				: type.asObject().getLoc();
  	
		Offset off = loc.getOffset();
		unlessZero(off, loc);
		return loc;
	}
	
	ECR getFunc(ECR srcECR) {
		ValueType type = getType(srcECR);
		ensureSimObj(srcECR, type.getSize());
		type = getType(srcECR);
  	return type.isSimple() ? type.asSimple().getFunc()
  			: type.asObject().getFunc();
	}
	
	/**
	 * Collapse <code>structECR</code> by merge it 
	 * with all its element ECRs, and set its type
	 * as object type with size Top
	 *  
	 * @param structECR
	 * @param structT
	 */
	private ValueType collapseStruct(ECR structECR, StructType structT) {		
		collapseStruct(structECR, structT, Sets.<ECR>newHashSet(structECR));
		ensureSimObj(structECR, Size.getTop());
		return getType(structECR);
	}

	/**
	 * Collapse <code>structECR</code> by merge it 
	 * with all its element ECRs, and set its type
	 * as the object type with structT's size
	 * 
	 * @param structECR
	 * @param structT
	 * @param ECRCache avoid structure cycle
	 * @return object type with size Top
	 */
	private ValueType collapseStruct(ECR structECR, StructType structT, Collection<ECR> ECRCache) {
		// Ensure collapsed type to be simple	
		ValueType unionType = null;
		
		// join components
		Collection<ECR> elems = structT.getFieldMap().asMapOfRanges().values();
		Collection<ECR> cjoins = Sets.newHashSet();
		Collection<Pair<Size,ECR>> ccjoins = Sets.newHashSet();
		
		for(ECR elem : elems) {			
			ECR elemLoc = getLoc(elem);
			ValueType elemLocType = getType(elemLoc);
			Parent parent = elemLocType.getParent().removeECR(structECR);
			elemLocType.setParent(parent);
			
			if(!ECRCache.add(elemLoc)) continue; // ECRCache has elemLoc
			
			cjoins.addAll(getCjoins(elemLoc));
			elemLoc.clearCCjoins(ccjoins);
			ccjoins.addAll(getCCjoins(elemLoc));
			elemLoc.clearCCjoins(ccjoins);
			
			if(elemLocType.isStruct()) {
				elemLocType = collapseStruct(elemLoc, elemLocType.asStruct(), ECRCache);
			}
			
			union(structECR, elemLoc);
			unionType = unionType == null ? elemLocType : unify(unionType, elemLocType);
		}
		unionType = unionType == null ? ValueType.bottom() : unionType;
		
		setType(structECR, unionType);
		ECR root = findRoot(structECR);
		
		for(Pair<Size, ECR> cjoinPair : ccjoins) {
			ccjoin(cjoinPair.fst(), root, cjoinPair.snd());
		}
		
		for(ECR joinECR : cjoins) {
			cjoin(root, joinECR);
		}
		
		return unionType;
	}

	/**
	 * Create a pair of location ECR and function ECR, both 
	 * with bottom type 
	 * 
	 * @return
	 */
	private Pair<ECR, ECR> createBottomLocFunc() {
		ECR loc = ECR.createBottom();
		loc.setOffset(Offset.createZero());
		ECR func = ECR.createBottom();
		return Pair.of(loc, func);		
	}

	private Offset getOffset(ECR e) {
		return findRoot(e).getOffset();
	}

	private Collection<ECR> getCjoins(ECR e) {
		return findRoot(e).getCjoins();
	}
	
	private Collection<Pair<Size, ECR>> getCCjoins(ECR e) {
		return findRoot(e).getCCjoins();
	}
	
	private void addCCjoin(Size size, ECR e1, ECR e2) {
		findRoot(e1).addCCjoin(size, e2);
	}
	
	private void addCjoin(ECR e1, ECR e2) {
		findRoot(e1).addCjoin(e2);
	}
	
	private void addCCjoins(ECR e1, Collection<Pair<Size, ECR>> ccjoins) {
		findRoot(e1).addCCjoins(ccjoins);
	}
	
	private void addCjoins(ECR e1, Collection<ECR> cjoins) {
		findRoot(e1).addCjoins(cjoins);
	}

	private void setOffset(ECR e, Offset offset) {
		findRoot(e).setOffset(offset);
	}

	/**
	 * ECR-union e1 and e2, return the updated root
	 * @param e1
	 * @param e2
	 * @return
	 */
	private ECR union(ECR e1, ECR e2) {
	  uf.union(e1, e2);
	  return findRoot(e1);
	}
	
	/**
	 * Get the compatible map of the field range maps in struct types
	 * <code>structT1</code> and <code>structT2</code>
	 * 
	 * @param structT1
	 * @param structT2
	 * @return a fresh and compatible field range map
	 */
	private RangeMap<Long, ECR> getCompatibleMap(StructType structT1, StructType structT2) {
		RangeMap<Long, ECR> fieldMap1 = structT1.getFieldMap();
		RangeMap<Long, ECR> fieldMap2 = structT2.getFieldMap();
		
		RangeMap<Long, ECR> fieldMap = FieldRangeMap.create();
		fieldMap.putAll(fieldMap1);
		
		for(Entry<Range<Long>, ECR> entry : fieldMap2.asMapOfRanges().entrySet()) {
			Range<Long> range = entry.getKey();
			ECR ecr = entry.getValue();
			RangeMap<Long, ECR> subMap = fieldMap.subRangeMap(range);
			Map<Range<Long>, ECR> subMapRanges = subMap.asMapOfRanges();
			if(subMapRanges.isEmpty()) {
				fieldMap.put(range, ecr); continue;
			}
			
			Range<Long> span = subMap.span();
			fieldMap.remove(span);
			
			Range<Long> newRange = range.span(span);
			ECR joinECR = ecr;
			
			for(ECR elemECR : subMapRanges.values()) {
				joinECR = join(joinECR, elemECR);
			}
			
			fieldMap.put(newRange, joinECR);
		}
		
		return fieldMap;
	}

	private void ensureSimObj(ECR e, Size rangeSize) {
		ValueType type = getType(e);
		
		switch(type.getKind()) {
		case BOTTOM: {  	
	  	ValueType simType = ValueType.simple(
	  			createBottomLocFunc(), 
	  			rangeSize, 
	  			Parent.getBottom());
	  	setType(e, simType);	  	
			return;
		}
		case BLANK: {
			BlankType blankType = type.asBlank();
	  	ValueType simType = ValueType.simple(
	  			createBottomLocFunc(), 
	  			blankType.getSize(), 
	  			blankType.getParent());
	  	setType(e, simType);
	  	
	  	if(!(Size.isLessThan(rangeSize, blankType.getSize()))) expand(e);
			return;
		}
		case SIMPLE: {
			Size size = type.getSize();
			if(!(Size.isLessThan(rangeSize, size))) expand(e);
			return;
		}
		case STRUCT: {
			promote(e, rangeSize);
			return;
		}
		default:
			return;
		}
	}

	/**
	 * Swap <code>t1</code> and <code>t2</code> if <code> kind(t1) > kind(t2) 
	 * </code>
	 * 
	 * @param t1
	 * @param t2
	 * @return the pair of value types <code>(t1', t2')</code> that 
	 * <code>kind(t1') <= kind(t2')</code>
	 */
	private Pair<ValueType, ValueType> swap(ValueType t1, ValueType t2) {
		
		if(t1.isBottom()) return Pair.of(t1, t2);
		if(t2.isBottom()) return Pair.of(t2, t1);
		
		if(t1.isLambda()) {
			assert t2.isLambda();
			return Pair.of(t1, t2);
		}
		
		if(t2.isLambda()) {
			assert t1.isLambda();
			return Pair.of(t1, t2);
		}
		
		ValueTypeKind kind1 = t1.getKind();
		ValueTypeKind kind2 = t2.getKind();
		
		switch(kind1) {
		case BOTTOM: return Pair.of(t1, t2);
		case BLANK:
			switch(kind2) {
			case BOTTOM:
			case BLANK:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		case SIMPLE:
			switch(kind2) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		case STRUCT:
			switch(kind2) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
			case STRUCT:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		default: // case OBJECT:
			return Pair.of(t2, t1);
		}
	}

	/**
	 * Check if one of <code>e1</code> or <code>e2</code> is a struct,
	 * and the other is either object or simple, collapse the one
	 * with struct type
	 * 
	 * @param e1
	 * @param e2
	 */
	private void checkStructCollapse(ECR e1, ECR e2) {
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		
		if(t2.isStruct() && 
				(t1.isSimple() || t1.isObject())) {
			collapseStruct(e2, t2.asStruct()); return;
		}
		
		if(t1.isStruct() && 
				(t2.isSimple() || t2.isObject())) {
			collapseStruct(e1, t1.asStruct()); return;
		}
		
		return;
	}
	
	/**
	 * During the join process, there might be cycle. It means the ECR <code>
	 * root</code> might be set to <code>freshType</code>. The type-union should
	 * take care of it -- union <code>freshType</code> to <code>unionType</code>.
	 * In particular, <code>freshType</code> is an object type, while <code>
	 * unionType</code> is a struct type, then <code>unionType</code> should be 
	 * collapsed before union with <code>freshType</code>.
	 * 
	 * @param root
	 * @param unionType
	 * @param freshType
	 * @return unified type
	 */
	private ValueType resolveType(ECR root, ValueType unionType, ValueType freshType) {
		Preconditions.checkArgument(!unionType.isLambda());
		Preconditions.checkArgument(!freshType.isLambda());
		
		Pair<ValueType, ValueType> pair = swap(unionType, freshType);
		ValueType t1 = pair.fst(), t2 = pair.snd();
		
		if(t1.isSimple() && t2.isStruct()) {
			Collection<ECR> elems = t2.asStruct().getFieldMap().asMapOfRanges().values();
	  	ValueType resType = t1;
			for(ECR elem : elems) {				
				ECR elemLoc = getLoc(elem);
				ValueType elemLocType = getType(elemLoc);
				Parent parent = elemLocType.getParent().removeECR(root);
				elemLocType.setParent(parent);
				if(elemLocType.isStruct())
					elemLocType = collapseStruct(elemLoc, elemLocType.asStruct());
				
				union(root, elemLoc);
				resType = unify(resType, elemLocType);
			}
			return resType;
		}
		
		if(t1.isStruct() && t2.isObject()) {
			Collection<ECR> elems = t1.asStruct().getFieldMap().asMapOfRanges().values();
	  	ValueType resType = t2;
			for(ECR elem : elems) {
				ValueType elemType = getType(elem);
				Parent parent = elemType.getParent().removeECR(root);
				elemType.setParent(parent);
				
				ECR elemLoc = getLoc(elem);
				ValueType elemLocType = getType(elemLoc);
				if(elemLocType.isStruct()) {
					elemLocType = collapseStruct(elemLoc, elemLocType.asStruct());
					setType(elemLoc, elemLocType);
				}
				
				union(root, elemLoc);
				resType = unify(resType, elemLocType);
			}
			return resType;
		}
		
		return unify(t1, t2);
	}
}
