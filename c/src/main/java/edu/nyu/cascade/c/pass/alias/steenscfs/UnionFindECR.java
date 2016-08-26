package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.pass.alias.steenscfs.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

public class UnionFindECR {
	private final UnionFind<IRVar> uf;
	/**
	 * Record the pointer arithmetic pending joins if the numeric operand is a
	 * constant
	 */
	private final Map<Pair<ECR, Long>, Pair<ECR, Long>> ptrAriJoins = Maps
			.newHashMap();
	private final Set<ECR> structECRs = Sets.newHashSet();

	private UnionFindECR() {
		uf = UnionFind.create();
	}

	static UnionFindECR create() {
		return new UnionFindECR();
	}

	ECR createECR(ValueType type) {
		ECR ecr = new ECR(type);
		if (type.isStruct()) {
			structECRs.add(ecr);
		}
		return ecr;
	}

	boolean normalizeStructECRs() {
		Map<ECR, TreeMap<Range<Long>, ECR>> structFlattenMap = flattenStructECRs(
				structECRs);

		boolean changed = false;
		for (Entry<ECR, TreeMap<Range<Long>, ECR>> entry : structFlattenMap
				.entrySet()) {
			changed |= mergeOverlapFields(entry.getKey(), entry.getValue());
		}

		return changed;

	}

	boolean mergeOverlapFields(ECR ecr,
			TreeMap<Range<Long>, ECR> flattenFieldMap) {
		Preconditions.checkArgument(getType(ecr).isStruct());
		Iterator<Range<Long>> fieldItr = flattenFieldMap.keySet().iterator();

		boolean changed = false;

		Range<Long> currRange = fieldItr.next();
		ECR currECR = flattenFieldMap.get(currRange);
		while (fieldItr.hasNext()) {
			Range<Long> nextRange = fieldItr.next();
			ECR nextECR = flattenFieldMap.get(nextRange);
			if (isDisjoint(currRange, nextRange)) {
				currECR = nextECR;
				currRange = nextRange;
			} else {
				currRange = merge(currRange, nextRange);
				cjoin(currECR, nextECR);
				changed = true;
			}
		}

		return changed;
	}

	private Map<ECR, TreeMap<Range<Long>, ECR>> flattenStructECRs(
			Set<ECR> structECRs) {
		Set<ECR> top_structECRs = Sets.newHashSet();
		for (ECR ecr : structECRs) {
			ValueType type = getType(ecr);
			if (type.isStruct() && type.asStruct().getParent().getECRs().isEmpty()) {
				top_structECRs.add(findRoot(ecr));
			}
		}

		Map<ECR, TreeMap<Range<Long>, ECR>> structFlattenMap = Maps.newHashMap();

		// Flatten the field range map within top struct ECRs.
		for (ECR top_ecr : top_structECRs) {

			TreeMap<Range<Long>, ECR> fieldRangeMap = Maps.newTreeMap(
					new Comparator<Range<Long>>() {
						@Override
						public int compare(Range<Long> o1, Range<Long> o2) {
							int res = o1.lowerEndpoint().compareTo(o2.lowerEndpoint());
							if (res != 0)
								return res;
							return o1.upperEndpoint().compareTo(o2.upperEndpoint());
						}
					});

			List<Pair<Long, ECR>> worklist = Lists.newArrayList();
			worklist.add(Pair.of(0L, top_ecr));

			while (!worklist.isEmpty()) {
				Pair<Long, ECR> curr = worklist.remove(0);
				long curr_offset = curr.fst();
				ECR curr_ecr = curr.snd();
				ValueType curr_type = getType(curr_ecr);
				assert curr_type.isStruct();
				Map<Range<Long>, ECR> curr_fieldRangeMap = curr_type.asStruct()
						.getFieldMap();
				for (Entry<Range<Long>, ECR> curr_entry : curr_fieldRangeMap
						.entrySet()) {
					Range<Long> range = curr_entry.getKey();
					Range<Long> range_offset = Range.closedOpen(range.lowerEndpoint()
							+ curr_offset, range.upperEndpoint() + curr_offset);
					ECR field_ecr = curr_entry.getValue();
					if (fieldRangeMap.containsKey(range_offset)) {
						join(field_ecr, fieldRangeMap.get(range_offset));
					} else {
						ECR field_loc_ecr = getLoc(field_ecr);
						if (getType(field_loc_ecr).isStruct()) {
							worklist.add(Pair.of(range_offset.lowerEndpoint(),
									field_loc_ecr));
						} else {
							fieldRangeMap.put(range_offset, field_ecr);
						}
					}
				}
			}

			structFlattenMap.put(top_ecr, fieldRangeMap);
		}

		return structFlattenMap;
	}

	private Range<Long> merge(Range<Long> range1, Range<Long> range2) {
		return Range.closedOpen(Math.min(range1.lowerEndpoint(), range2
				.lowerEndpoint()), Math.max(range1.upperEndpoint(), range2
						.upperEndpoint()));
	}

	private boolean isDisjoint(Range<Long> range1, Range<Long> range2) {
		return range1.upperEndpoint() <= range2.lowerEndpoint() || range2
				.upperEndpoint() <= range1.lowerEndpoint();
	}

	void reset() {
		uf.reset();
	}

	/**
	 * Add <code>var</code> into union find
	 * 
	 * @param var
	 */
	void add(VarImpl var) {
		uf.add(var, var.getECR());
	}

	/**
	 * Set type <code>e</code> as <code>type</code>
	 * 
	 * @param e
	 * @param type
	 */
	void setType(ECR e, ValueType type) {
		ECR root = findRoot(e);
		root.setType(type);
		if (type.isStruct()) {
			structECRs.add(root);
		}

		Collection<Pair<Size, ECR>> ccjoins = ImmutableList.copyOf(root
				.getCCjoins());
		root.clearCCjoins(ccjoins);
		for (Pair<Size, ECR> cjoinPair : ccjoins)
			ccjoin(cjoinPair.fst(), root, cjoinPair.snd());

		Collection<ECR> cjoins = ImmutableList.copyOf(root.getCjoins());
		root.clearCjoins(cjoins);
		for (ECR joinECR : cjoins)
			cjoin(root, joinECR);
	}

	/**
	 * Get the type of the ECR @param e
	 */
	ValueType getType(ECR e) {
		return findRoot(e).getType();
	}

	ECR join(ECR e1, ECR e2) {
		if (e1.equals(e2))
			return e1;

		checkStructCollapse(e1, e2);

		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);

		Collection<Pair<Size, ECR>> ccjoins1 = ImmutableList.copyOf(getCCjoins(e1));
		Collection<Pair<Size, ECR>> ccjoins2 = ImmutableList.copyOf(getCCjoins(e2));

		Collection<ECR> cjoins1 = ImmutableList.copyOf(getCjoins(e1));
		Collection<ECR> cjoins2 = ImmutableList.copyOf(getCjoins(e2));

		ECR root = union(e1, e2);

		switch (t1.getKind()) {
		case BOTTOM: {
			switch (t2.getKind()) {
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
				for (Pair<Size, ECR> pair : ccjoins1)
					ccjoin(pair.fst(), root, pair.snd());

				root.clearCjoins(cjoins1);
				for (ECR cjoin : cjoins1)
					cjoin(root, cjoin);

				break;
			}
			}
			break;
		}
		default: {
			switch (t2.getKind()) {
			case BOTTOM: {
				root.setType(t1);

				root.clearCCjoins(ccjoins2);
				for (Pair<Size, ECR> pair : ccjoins2)
					ccjoin(pair.fst(), root, pair.snd());

				root.clearCjoins(cjoins2);
				for (ECR cjoin : cjoins2)
					cjoin(root, cjoin);

				break;
			}
			default: {
				root.setType(t1);
				ValueType unionType = unify(t1, t2);

				ValueType freshType = getType(root);
				if (!freshType.equals(t1)) {
					unionType = resolveType(root, unionType, freshType);
				}

				root.setType(unionType);

				root.clearCCjoins(ccjoins1);
				root.clearCCjoins(ccjoins2);

				for (Pair<Size, ECR> pair : ccjoins1)
					ccjoin(pair.fst(), root, pair.snd());
				for (Pair<Size, ECR> pair : ccjoins2)
					ccjoin(pair.fst(), root, pair.snd());
				break;
			}
			}
			break;
		}
		}

		return root;
	}

	ECR cjoin(ECR e1, ECR e2) {
		if (e1.equals(e2))
			return findRoot(e1);

		if (getType(e1).isBottom()) {

			Collection<ECR> joins2 = getCjoins(e2);
			Collection<Pair<Size, ECR>> cjoins2 = getCCjoins(e2);

			addCjoin(e1, e2);
			addCjoins(e1, joins2);
			addCCjoins(e1, cjoins2);

			return findRoot(e1);
		}

		return join(e1, e2);
	}

	void ccjoin(Size rangeSize, ECR e1, ECR e2) {
		ValueType type1 = getType(e1);
		if (type1.isBottom()) {
			addCCjoin(rangeSize, e1, e2);
			return;
		}

		Size size1 = type1.getSize();
		if (!Size.isLessThan(rangeSize, size1)) {
			addCCjoin(rangeSize, e1, e2);
			expand(e1, rangeSize); // expand(e1) would call setType(e1, ...) and thus
															// ccjoin(e1, e2)
			return;
		}

		if (e1.equals(e2))
			return;

		switch (type1.getKind()) {
		case BLANK: {
			addCCjoin(rangeSize, e1, e2);
			ValueType type2 = getType(e2);
			switch (type2.getKind()) {
			case BOTTOM:
				setType(e2, ValueType.blank(rangeSize, Parent.getBottom()));
				return;
			default:
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
		}
		case SIMPLE: {
			ValueType type2 = getType(e2);
			switch (type2.getKind()) {
			case BOTTOM:
				setType(e2, ValueType.simple(type1.asSimple().getLoc(), type1.asSimple()
						.getFunc(), rangeSize, Parent.getBottom()));
				return;
			case BLANK: {
				setType(e2, ValueType.simple(type1.asSimple().getLoc(), type1.asSimple()
						.getFunc(), type2.getSize(), type2.getParent()));
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			case SIMPLE: {
				cjoin(type1.asSimple().getLoc(), type2.asSimple().getLoc());
				cjoin(type1.asSimple().getFunc(), type2.asSimple().getFunc());
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			case STRUCT: {
				addCCjoin(rangeSize, e1, e2);
				collapseStruct(e2, type2.asStruct());
				return;
			}
			default: // lambda
				return;
			}
		}
		case STRUCT: {
			ValueType type2 = getType(e2);
			switch (type2.getKind()) {
			case BOTTOM: {
				setType(e2, ValueType.struct(type1.asStruct().getFieldMap(), rangeSize,
						Parent.getBottom()));
				return;
			}
			case BLANK: {
				Size size2 = type2.getSize();
				setType(e2, ValueType.struct(type1.asStruct().getFieldMap(), size2,
						type2.getParent()));
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			case SIMPLE: {
				addCCjoin(rangeSize, e1, e2);
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				for (ECR elemECR : type1.asStruct().getFieldMap().values()) {
					ValueType elemType = getType(elemECR);
					Size elemSize = elemType.getSize();
					ccjoin(elemSize, elemECR, e2);
				}
				return;
			}
			case STRUCT: {
				throw new IllegalArgumentException();
			}
			default:
				return; // lambda
			}
		}
		default:
			return; // lambda
		}
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
		if (t1.equals(t2))
			return t1;
		if (t1.isBottom()) {
			return t2;
		}

		Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());
		Size size = Size.getLUB(t1.getSize(), t2.getSize());

		switch (t1.getKind()) {
		case BLANK: {
			switch (t2.getKind()) {
			case BLANK:
				return ValueType.blank(size, parent);
			case SIMPLE: {
				return ValueType.simple(t2.asSimple().getLoc(), t2.asSimple().getFunc(),
						size, parent);
			}
			default: { // case STRUCT:
				return ValueType.struct(t2.asStruct().getFieldMap(), size, parent);
			}
			}
		}
		case SIMPLE: {
			switch (t2.getKind()) {
			case SIMPLE: {
				ECR loc1 = t1.asSimple().getLoc();
				ECR loc2 = t2.asSimple().getLoc();
				ECR func1 = t1.asSimple().getFunc();
				ECR func2 = t2.asSimple().getFunc();

				ECR loc = join(loc1, loc2);
				ECR func = join(func1, func2);

				return ValueType.simple(loc, func, size, parent);
			}
			default: // case STRUCT:
				throw new IllegalArgumentException();
			}
		}
		case STRUCT: {
			if (ValueTypeKind.STRUCT.equals(t2.getKind())) {
				Map<Range<Long>, ECR> map = getCompatibleMap(t1.asStruct(), t2
						.asStruct());
				return ValueType.struct(map, size, parent);
			} else {
				throw new IllegalArgumentException();
			}
		}
		default: { // Lambda
			assert (t2.isLambda());

			List<ECR> params = Lists.newArrayList();
			Iterator<ECR> paramItr1 = t1.asLambda().getParams().iterator();
			Iterator<ECR> paramItr2 = t2.asLambda().getParams().iterator();
			while (paramItr1.hasNext() && paramItr2.hasNext()) {
				ECR param1 = paramItr1.next();
				ECR param2 = paramItr2.next();
				ECR param = join(param1, param2);
				params.add(param);
			}

			while (paramItr1.hasNext())
				params.add(paramItr1.next());
			while (paramItr2.hasNext())
				params.add(paramItr2.next());

			ECR ret1 = t1.asLambda().getRet();
			ECR ret2 = t2.asLambda().getRet();
			ECR ret = join(ret1, ret2);
			return ValueType.lam(ret, params, parent);
		}
		}
	}

	/**
	 * Expand <code>e</code> to the <code>size</code>
	 * 
	 * @param e
	 * @param size
	 */
	void expand(ECR e, Size size) {
		ValueType eType = getType(e);
		ValueType blankType = ValueType.blank(size, Parent.getBottom());
		ValueType unifyType = unify(eType, blankType);
		setType(e, unifyType);
	}

	/**
	 * Get the root of ECR <code>e</code>
	 * 
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
		ImmutableMap.Builder<ECR, Collection<IRVar>> builder = ImmutableMap
				.builder();
		for (Partition ecr : map.asMap().keySet()) {
			builder.put(findRoot((ECR) ecr), ImmutableSet.copyOf(map.asMap().get(
					ecr)));
		}
		return builder.build();
	}

	Collection<IRVar> getEquivClass(ECR key) {
		return uf.getEquivClass(key);
	}

	ECR getLoc(ECR srcECR) {
		ensureSimple(srcECR);
		ValueType type = getType(srcECR);
		return type.asSimple().getLoc();
	}

	ECR getFunc(ECR srcECR) {
		ensureSimple(srcECR);
		ValueType type = getType(srcECR);
		return type.asSimple().getFunc();
	}

	/**
	 * Collapse <code>structECR</code> by merge it with all its element ECRs, and
	 * set its type as object type
	 * 
	 * @param structECR
	 * @param structT
	 */
	ValueType collapseStruct(ECR structECR, StructType structT) {
		collapseStruct(structECR, structT, Sets.<ECR> newHashSet(structECR));
		ensureSimple(structECR);
		return getType(structECR);
	}

	void ptrAri(ECR resLocECR, long size, ECR lhsLocECR, long shift) {
		ptrAriJoins.put(Pair.of(resLocECR, size), Pair.of(lhsLocECR, shift));
	}

	/**
	 * Collapse <code>structECR</code> by merge it with all its element ECRs, and
	 * set its type as the cell type (simple type might with top size)
	 * 
	 * @param structECR
	 * @param structT
	 * @param ECRCache
	 *          avoid structure cycle
	 * @return
	 */
	private ValueType collapseStruct(ECR structECR, StructType structT,
			Collection<ECR> ECRCache) {
		// Ensure collapsed type to be simple
		ValueType unionType = null;

		// join components
		Collection<ECR> elems = structT.getFieldMap().values();
		Collection<ECR> cjoins = Sets.newHashSet();
		Collection<Pair<Size, ECR>> ccjoins = Sets.newHashSet();

		for (ECR elem : elems) {
			ECR elemLoc = getLoc(elem);
			ValueType elemLocType = getType(elemLoc);
			Parent parent = elemLocType.getParent().removeECR(structECR);
			elemLocType.setParent(parent);

			if (!ECRCache.add(elemLoc))
				continue; // ECRCache has elemLoc

			cjoins.addAll(getCjoins(elemLoc));
			elemLoc.clearCCjoins(ccjoins);
			ccjoins.addAll(getCCjoins(elemLoc));
			elemLoc.clearCCjoins(ccjoins);

			if (elemLocType.isStruct()) {
				elemLocType = collapseStruct(elemLoc, elemLocType.asStruct(), ECRCache);
			}

			union(structECR, elemLoc);
			unionType = unionType == null ? elemLocType
					: unify(unionType, elemLocType);
		}
		unionType = unionType == null ? ValueType.bottom() : unionType;

		setType(structECR, unionType);
		ECR root = findRoot(structECR);

		for (Pair<Size, ECR> cjoinPair : ccjoins)
			ccjoin(cjoinPair.fst(), root, cjoinPair.snd());

		for (ECR joinECR : cjoins)
			cjoin(root, joinECR);

		return unionType;
	}

	/**
	 * Create a pair of location ECR and function ECR, both with bottome type
	 * 
	 * @return
	 */
	private Pair<ECR, ECR> createBottomLocFunc() {
		ECR loc = ECR.createBottom();
		ECR func = ECR.createBottom();
		return Pair.of(loc, func);
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

	/**
	 * ECR-union e1 and e2, return the updated root
	 * 
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
	private Map<Range<Long>, ECR> getCompatibleMap(StructType structT1,
			StructType structT2) {
		Map<Range<Long>, ECR> fieldMap1 = structT1.getFieldMap();
		Map<Range<Long>, ECR> fieldMap2 = structT2.getFieldMap();

		Map<Range<Long>, ECR> fieldMap = Maps.newHashMap();
		fieldMap.putAll(fieldMap1);

		for (Entry<Range<Long>, ECR> entry : fieldMap2.entrySet()) {
			Range<Long> range2 = entry.getKey();
			ECR ecr2 = entry.getValue();
			if (fieldMap.containsKey(range2)) {
				ECR ecr1 = fieldMap.get(range2);
				ECR ecr = join(ecr1, ecr2);
				fieldMap.put(range2, ecr);
			} else {
				fieldMap.put(range2, ecr2);
			}
		}
		return fieldMap;
	}

	void ensureSimple(ECR e) {
		ValueType type = getType(e);

		switch (type.getKind()) {
		case BOTTOM: {
			ValueType simType = ValueType.simple(createBottomLocFunc(), Size.getBot(),
					Parent.getBottom());
			setType(e, simType);
			return;
		}
		case BLANK: {
			BlankType blankType = type.asBlank();
			ValueType simType = ValueType.simple(createBottomLocFunc(), blankType
					.getSize(), blankType.getParent());
			setType(e, simType);
			return;
		}
		case SIMPLE: {
			return;
		}
		case STRUCT: {
			collapseStruct(e, type.asStruct());
			return;
		}
		default: // lambda
			throw new IllegalArgumentException("Invalid type " + type.getKind());
		}
	}

	/**
	 * Swap <code>t1</code> and <code>t2</code> if <code> kind(t1) > kind(t2) 
	 * </code>
	 * 
	 * @param t1
	 * @param t2
	 * @return the pair of value types <code>(t1', t2')</code> that
	 *         <code>kind(t1') <= kind(t2')</code>
	 */
	private Pair<ValueType, ValueType> swap(ValueType t1, ValueType t2) {

		if (t1.isBottom())
			return Pair.of(t1, t2);
		if (t2.isBottom())
			return Pair.of(t2, t1);

		if (t1.isLambda()) {
			assert t2.isLambda();
			return Pair.of(t1, t2);
		}

		if (t2.isLambda()) {
			assert t1.isLambda();
			return Pair.of(t1, t2);
		}

		ValueTypeKind kind1 = t1.getKind();
		ValueTypeKind kind2 = t2.getKind();

		switch (kind1) {
		case BOTTOM:
			return Pair.of(t1, t2);
		case BLANK:
			switch (kind2) {
			case BOTTOM:
			case BLANK:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		case SIMPLE:
			switch (kind2) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		default: // case STRUCT:
			switch (kind2) {
			case BLANK:
			case BOTTOM:
			case SIMPLE:
			case STRUCT:
				return Pair.of(t2, t1);
			default:
				return Pair.of(t1, t2);
			}
		}
	}

	/**
	 * Check if one of <code>e1</code> or <code>e2</code> is a struct, and the
	 * other is either object or simple, collapse the one with struct type
	 * 
	 * @param e1
	 * @param e2
	 */
	private void checkStructCollapse(ECR e1, ECR e2) {
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);

		if (t2.isStruct() && t1.isSimple()) {
			collapseStruct(e2, t2.asStruct());
			return;
		}

		if (t1.isStruct() && t2.isSimple()) {
			collapseStruct(e1, t1.asStruct());
			return;
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
	private ValueType resolveType(ECR root, ValueType unionType,
			ValueType freshType) {
		Preconditions.checkArgument(!unionType.isLambda());
		Preconditions.checkArgument(!freshType.isLambda());

		Pair<ValueType, ValueType> pair = swap(unionType, freshType);
		ValueType t1 = pair.fst(), t2 = pair.snd();

		if (t1.isSimple() && t2.isStruct()) {
			Collection<ECR> elems = t2.asStruct().getFieldMap().values();
			ValueType resType = t1;
			for (ECR elem : elems) {
				ECR elemLoc = getLoc(elem);
				ValueType elemLocType = getType(elemLoc);
				Parent parent = elemLocType.getParent().removeECR(root);
				elemLocType.setParent(parent);
				if (elemLocType.isStruct()) {
					elemLocType = collapseStruct(elemLoc, elemLocType.asStruct());
				}

				union(root, elemLoc);
				resType = unify(resType, elemLocType);
			}
			return resType;
		}

		return unify(t1, t2);
	}

	void clearPointerArithmetic() {
		if (ptrAriJoins.isEmpty())
			return;
		for (Entry<Pair<ECR, Long>, Pair<ECR, Long>> cell : ptrAriJoins
				.entrySet()) {
			ECR resECR = findRoot(cell.getKey().fst());
			final ECR origECR = findRoot(cell.getValue().fst());
			long shift = cell.getValue().snd();
			if (shift >= 0) {
				// TODO: could do more precise analysis here.
				collapse(origECR, resECR);
				continue;
			}

			ValueType origType = getType(origECR);
			Parent parent = origType.getParent();
			if (parent.getECRs().isEmpty()) {
				// TODO: could do more precise analysis here.
				collapse(origECR, resECR);
				continue;
			}

			for (ECR parentECR : parent.getECRs()) {
				ValueType parentType = getType(parentECR);
				if (!parentType.isStruct()) {
					IOUtils.errPrinter().pln("WARNING: non-struct parent");
					join(parentECR, origECR);
					continue;
				}

				Map<Range<Long>, ECR> fieldMap = parentType.asStruct().getFieldMap();
				Entry<Range<Long>, ECR> fieldRange = Iterables.find(fieldMap.entrySet(),
						new Predicate<Entry<Range<Long>, ECR>>() {
							@Override
							public boolean apply(Entry<Range<Long>, ECR> input) {
								return origECR.equals(getLoc(input.getValue()));
							}
						});
				long low = fieldRange.getKey().lowerEndpoint() + shift;
				Size parentSize = parentType.getSize();
				long size = cell.getKey().snd();
				if (low == 0 && (parentSize.isBottom() || parentSize.isNumber()
						&& parentSize.getValue() == size)) {
					join(parentECR, resECR);
					continue;
				}

				collapse(origECR, resECR);
			}
		}
	}

	void collapse(ECR e1, ECR e2) {
		ECR root = join(e1, e2);

		// Parent is stored at the points-to loc of
		Parent parent = getType(root).getParent();
		Collection<ECR> parentECRs = ImmutableList.copyOf(parent.getECRs());

		for (ECR ecr : parentECRs) {
			ValueType ecrType = getType(ecr);
			if (ecrType.isStruct())
				collapseStruct(ecr, ecrType.asStruct());
		}
	}

	boolean containsPtrAritJoin(ECR locECR, long size) {
		return ptrAriJoins.containsKey(Pair.of(locECR, size));
	}

	void replacePtrAriJoin(ECR freshLocECR, long freshSize, ECR locECR,
			long size) {
		Pair<ECR, Long> value = ptrAriJoins.remove(Pair.of(locECR, size));
		ptrAriJoins.put(Pair.of(freshLocECR, freshSize), value);
	}
}
