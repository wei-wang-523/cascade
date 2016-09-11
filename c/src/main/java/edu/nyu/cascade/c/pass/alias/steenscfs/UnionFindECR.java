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
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.steenscfs.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;
import xtc.type.Type;

public class UnionFindECR {
	private final UnionFind<IRVar> uf;
	private final Set<ECR> structECRs = Sets.newLinkedHashSet();
	private final Set<ECR> collapseECRs = Sets.newLinkedHashSet();
	private final Set<ECR> injectFieldECRs = Sets.newLinkedHashSet();

	private UnionFindECR() {
		uf = UnionFind.create();
	}

	static UnionFindECR create() {
		return new UnionFindECR();
	}

	boolean addCollapseECR(ECR ecr) {
		return collapseECRs.add(ecr);
	}

	ECR createECR(ValueType type) {
		ECR ecr = new ECR(type);
		if (type.isStruct()) {
			structECRs.add(ecr);
		}
		return ecr;
	}

	ECR createECR(Type type) {
		type = type.resolve();
		Size size = Size.createForType(type);
		Parent parent = Parent.getBottom();
		if (CType.isScalar(type)) {
			return createECR(ValueType.simple(ECR.createBottom(), size, parent));
		} else if (CType.isStructOrUnion(type)) {
			return createECR(ValueType.struct(size, parent));
		} else {
			return createECR(ValueType.blank(size, Parent.getBottom()));
		}
	}

	boolean normalizeStructECRs() {
		boolean changed = false;

		do {
			injectFieldECRs.clear();
			Set<ECR> top_structECRs = Sets.newLinkedHashSet();
			Set<ECR> visited_structECRs = Sets.newHashSet();
			List<ECR> worklist = Lists.newArrayList(structECRs);
			while (!worklist.isEmpty()) {
				ECR ecr = worklist.remove(0);
				if (visited_structECRs.contains(ecr))
					continue;
				visited_structECRs.add(ecr);

				ValueType type = getType(ecr);
				Collection<ECR> parents = type.getParent().getECRs();
				if (parents.isEmpty() && type.isStruct()) {
					top_structECRs.add(ecr);
				} else {
					worklist.addAll(parents);
				}
			}

			Map<ECR, TreeMap<Range<Long>, ECR>> structFlattenMap = Maps.newHashMap();
			for (ECR ecr : top_structECRs) {
				// Skip ECR if it has been collapsed when flattening other struct.
				if (!getType(ecr).isStruct())
					continue;
				TreeMap<Range<Long>, ECR> flattenMap = flattenStructECRs(ecr);
				if (!getType(ecr).isStruct()) {
					IOUtils.err()
							.println("Top struct ECR has been collapsed when flattening.");
				}
				structFlattenMap.put(ecr, flattenMap);
			}

			for (TreeMap<Range<Long>, ECR> flattenFieldMap : structFlattenMap
					.values()) {
				changed |= mergeOverlapFields(flattenFieldMap);
			}
		} while (!injectFieldECRs.isEmpty());

		return changed;
	}

	private boolean mergeOverlapFields(
			TreeMap<Range<Long>, ECR> flattenFieldMap) {
		Iterator<Range<Long>> fieldItr = flattenFieldMap.keySet().iterator();
		if (!fieldItr.hasNext()) {
			return false;
		}

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
				// Merge field ECR (the points-to ECR of the field entry)
				join(getLoc(currECR), getLoc(nextECR));
				currRange = merge(currRange, nextRange);
				changed = true;
			}
		}

		return changed;
	}

	/** Flatten the field range map within top struct ECR. */
	private TreeMap<Range<Long>, ECR> flattenStructECRs(ECR top_ecr) {
		TreeMap<Range<Long>, ECR> fieldRangeMap = Maps
				.newTreeMap(new Comparator<Range<Long>>() {
					@Override
					public int compare(Range<Long> o1, Range<Long> o2) {
						int res = o1.lowerEndpoint().compareTo(o2.lowerEndpoint());
						if (res != 0) {
							return res;
						} else if (o1.hasUpperBound() && o2.hasUpperBound()) {
							return o1.upperEndpoint().compareTo(o2.upperEndpoint());
						} else if (o1.hasUpperBound() && !o2.hasUpperBound()) {
							return 1;
						} else if (!o1.hasUpperBound() && o2.hasUpperBound()) {
							return -1;
						} else {
							return 0;
						}
					}
				});

		List<Pair<Long, ECR>> worklist = Lists.newArrayList();
		worklist.add(Pair.of(0L, top_ecr));
		Set<ECR> visited = Sets.newHashSet();

		while (!worklist.isEmpty()) {
			Pair<Long, ECR> curr = worklist.remove(0);
			long curr_offset = curr.fst();
			ECR curr_ecr = curr.snd();
			if (visited.contains(curr_ecr)) {
				continue;
			}
			visited.add(curr_ecr);
			ValueType curr_type = getType(curr_ecr);
			if (!curr_type.isStruct())
				continue;
			Map<Range<Long>, ECR> curr_fieldRangeMap = curr_type.asStruct()
					.getFieldMap();
			for (Entry<Range<Long>, ECR> curr_entry : curr_fieldRangeMap.entrySet()) {
				Range<Long> range = curr_entry.getKey();
				Range<Long> range_offset = range.hasUpperBound()
						? Range.closedOpen(range.lowerEndpoint() + curr_offset,
								range.upperEndpoint() + curr_offset)
						: Range.atLeast(range.lowerEndpoint() + curr_offset);
				ECR field_ecr = curr_entry.getValue();
				if (fieldRangeMap.containsKey(range_offset)) {
					join(field_ecr, fieldRangeMap.get(range_offset));
				} else {
					ECR field_loc_ecr = getLoc(field_ecr);
					if (getType(field_loc_ecr).isStruct()) {
						worklist.add(Pair.of(range_offset.lowerEndpoint(), field_loc_ecr));
					} else {
						fieldRangeMap.put(range_offset, field_ecr);
					}
				}
			}
		}

		return fieldRangeMap;
	}

	private Range<Long> merge(Range<Long> range1, Range<Long> range2) {
		long min = Math.min(range1.lowerEndpoint(), range2.lowerEndpoint());
		if (range1.hasUpperBound() && range2.hasUpperBound()) {
			long max = Math.max(range1.upperEndpoint(), range2.upperEndpoint());
			return Range.closedOpen(min, max);
		} else {
			return Range.atLeast(min);
		}
	}

	private boolean isDisjoint(Range<Long> range1, Range<Long> range2) {
		if (range1.hasUpperBound()) {
			return range1.upperEndpoint() <= range2.lowerEndpoint();
		} else if (range2.hasUpperBound()) {
			return range2.upperEndpoint() <= range1.lowerEndpoint();
		} else {
			return false;
		}
	}

	boolean normalizeCollapseECRs() {
		List<ECR> worklist = Lists.newArrayList();
		// Initialize work list with ECR has parents (optimization for arrays, no
		// need for collapsing).
		for (ECR ecr : collapseECRs) {
			ValueType type = getType(ecr);
			if (type.isSimple()) {
				ECR loc = getLoc(ecr);
				ValueType loc_type = getType(loc);
				if (loc_type.getParent().getECRs().isEmpty()) {
					continue;
				} else {
					worklist.add(loc);
				}
			}
		}

		// Collect the top level parents
		Collection<ECR> topECRs = Sets.newLinkedHashSet();
		Collection<ECR> visitedParent = Sets.newHashSet();
		while (!worklist.isEmpty()) {
			ECR ecr = worklist.remove(0);
			if (visitedParent.contains(ecr)) {
				continue;
			}

			visitedParent.add(ecr);
			ValueType type = getType(ecr);

			if (type.getParent().getECRs().isEmpty()) {
				// Got top-level parent.
				topECRs.add(findRoot(ecr));
			} else {
				worklist.addAll(type.getParent().getECRs());
			}
		}

		if (topECRs.isEmpty())
			return false;

		for (ECR topECR : topECRs) {
			Collection<ECR> collapseECRs = Sets.newHashSet();

			// Reuse the work list
			worklist.clear();
			worklist.add(topECR);
			while (!worklist.isEmpty()) {
				ECR ecr = worklist.remove(0);
				collapseECRs.add(ecr);
				ValueType type = getType(ecr);
				if (type.isStruct()) {
					Collection<ECR> elems = type.asStruct().getFieldMap().values();
					for (ECR elem : elems) {
						ECR elemLoc = getLoc(elem);
						if (collapseECRs.contains(elemLoc))
							continue;
						worklist.add(elemLoc);
					}
				}
			}

			// Collapse the collapseECRs
			Collection<ECR> cjoins = Sets.newHashSet();
			Collection<Pair<Size, ECR>> ccjoins = Sets.newHashSet();

			ECR root = ECR.createBottom();
			ValueType unionType = ValueType.bottom();
			for (ECR elem : collapseECRs) {
				ValueType elemType = getType(elem);
				cjoins.addAll(getCjoins(elem));
				elem.clearCjoins(cjoins);
				ccjoins.addAll(getCCjoins(elem));
				elem.clearCCjoins(ccjoins);

				union(root, elem);
				elemType.setParent(Parent.getBottom());
				if (!elemType.isStruct()) {
					unionType = unify(unionType, elemType);
				}
			}

			setType(root, unionType);
			root = findRoot(root);

			for (Pair<Size, ECR> cjoinPair : ccjoins)
				ccjoin(cjoinPair.fst(), root, cjoinPair.snd());

			for (ECR joinECR : cjoins)
				cjoin(root, joinECR);

			ensureSimple(root);
		}
		return true;
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

		Collection<Pair<Size, ECR>> ccjoins = ImmutableList
				.copyOf(root.getCCjoins());
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

	boolean join(ECR e1, ECR e2) {
		Preconditions.checkNotNull(e1);
		Preconditions.checkNotNull(e2);
		if (e1.equals(e2)) {
			return false;
		}
		Pair<ECR, ECR> ecr_pair = swap(e1, e2);
		e1 = ecr_pair.fst();
		e2 = ecr_pair.snd();

		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);

		boolean changed = false;
		switch (t1.getKind()) {
		case BOTTOM: {
			processBottomUnion(e1, e2);
			changed = true;
			break;
		}
		case SIMPLE: {
			if (t2.isStruct()) {
				changed = injectFieldIntoStruct(e1, e2);
			} else {
				assert t2.isSimple();
				processUnion(e1, e2);
				changed = true;
			}
			break;
		}
		default: { // t1 is BLANK or both are STRUCT
			processUnion(e1, e2);
			changed = true;
			break;
		}
		}
		return changed;
	}

	private boolean injectFieldIntoStruct(ECR simp_ecr, ECR struct_ecr) {
		ValueType simple_type = getType(simp_ecr);
		ValueType struct_type = getType(struct_ecr);

		// Update the parent of simp_ecr with the new one struct_ecr
		Parent new_parent = Parent.create(struct_ecr);
		simple_type.setParent(Parent.getLUB(new_parent, simple_type.getParent()));
		Map<Range<Long>, ECR> field_map = struct_type.asStruct().getFieldMap();

		Size size = simple_type.getSize();
		Range<Long> range;
		if (size.isBottom()) {
			range = Range.closedOpen((long) 0, (long) 1);
		} else {
			range = Range.closedOpen((long) 0, size.getValue());
		}
		
		boolean changed = false;

		// If contains the field range, merge the field (avoid struct field to
		// ensure termination. Otherwise, add a new field.
		if (field_map.containsKey(range)) {
			ECR field_ecr = getLoc(field_map.get(range));
			while (getType(field_ecr).isStruct()) {
				ValueType tmp_type = getType(field_ecr);
				Map<Range<Long>, ECR> tmp_field_map = tmp_type.asStruct().getFieldMap();
				field_ecr = getLoc(tmp_field_map.get(range));
			}
			changed |= join(field_ecr, simp_ecr);
		} else {
			ECR addr_ecr = createECR(
					ValueType.simple(simp_ecr, Size.getBot(), Parent.getBottom()));
			field_map.put(range, addr_ecr);
			injectFieldECRs.add(struct_ecr);
			changed = true;
		}
		
		return changed;
	}

	private void processBottomUnion(ECR e1, ECR e2) {
		Preconditions.checkArgument(getType(e1).isBottom());
		Collection<ECR> cjoins1 = ImmutableList.copyOf(getCjoins(e1));
		Collection<ECR> cjoins2 = ImmutableList.copyOf(getCjoins(e2));
		Collection<Pair<Size, ECR>> ccjoins1 = ImmutableList.copyOf(getCCjoins(e1));
		Collection<Pair<Size, ECR>> ccjoins2 = ImmutableList.copyOf(getCCjoins(e2));

		ValueType t2 = getType(e2);

		ECR root = union(e1, e2);
		if (t2.isBottom()) {
			Collection<ECR> cjoins = Sets.newHashSet();
			cjoins.addAll(cjoins1);
			cjoins.addAll(cjoins2);
			root.addCjoins(cjoins);

			Collection<Pair<Size, ECR>> ccjoins = Sets.newHashSet();
			ccjoins.addAll(ccjoins1);
			ccjoins.addAll(ccjoins2);
			root.addCCjoins(ccjoins);
		} else {
			setType(root, t2);

			root.clearCCjoins(ccjoins1);
			for (Pair<Size, ECR> pair : ccjoins1)
				ccjoin(pair.fst(), root, pair.snd());

			root.clearCjoins(cjoins1);
			for (ECR cjoin : cjoins1) {
				cjoin(root, cjoin);
			}
		}
	}

	private void processUnion(ECR e1, ECR e2) {
		Preconditions.checkArgument(getType(e1).isBlank()
				|| (getType(e1).isStruct() && getType(e2).isStruct())
				|| (getType(e1).isSimple() && getType(e2).isSimple()));

		Collection<Pair<Size, ECR>> ccjoins1 = ImmutableList.copyOf(getCCjoins(e1));
		Collection<Pair<Size, ECR>> ccjoins2 = ImmutableList.copyOf(getCCjoins(e2));
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		ECR root = union(e1, e2);

		setType(root, t1);
		ValueType unionType = unify(t1, t2);
		ValueType freshType = getType(root);
		if (!freshType.equals(t1)) {
			unionType = resolveType(root, unionType, freshType);
		}

		setType(root, unionType);
		root.clearCCjoins(ccjoins1);
		root.clearCCjoins(ccjoins2);

		for (Pair<Size, ECR> pair : ccjoins1) {
			ccjoin(pair.fst(), root, pair.snd());
		}
		for (Pair<Size, ECR> pair : ccjoins2) {
			ccjoin(pair.fst(), root, pair.snd());
		}
	}

	private void cjoin(ECR e1, ECR e2) {
		if (e1.equals(e2))
			return;

		if (getType(e1).isBottom()) {
			Collection<ECR> joins2 = getCjoins(e2);
			Collection<Pair<Size, ECR>> cjoins2 = getCCjoins(e2);

			addCjoin(e1, e2);
			addCjoins(e1, joins2);
			addCCjoins(e1, cjoins2);
		} else {
			join(e1, e2);
		}
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
			// expand(e1) would call setType(e1, ...) and thus ccjoin(e1, e2)
			expand(e1, rangeSize);
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
				setType(e2, ValueType.simple(type1.asSimple().getLoc(), rangeSize,
						Parent.getBottom()));
				return;
			case BLANK: {
				setType(e2, ValueType.simple(type1.asSimple().getLoc(), type2.getSize(),
						type2.getParent()));
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			case SIMPLE: {
				cjoin(type1.asSimple().getLoc(), type2.asSimple().getLoc());
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			default: { // case STRUCT
				addCCjoin(rangeSize, e1, e2);
				collapseStruct(e2, type2.asStruct());
				return;
			}
			}
		}
		default: { // case STRUCT
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
			default: { // case STRUCT
				throw new IllegalArgumentException();
			}
			}
		}
		}
	}

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
			t2.setParent(parent);
			t2.setSize(size);
			return t2;
		}
		case SIMPLE: {
			assert t2.isSimple();
			ECR loc1 = t1.asSimple().getLoc();
			ECR loc2 = t2.asSimple().getLoc();
			join(loc1, loc2);
			t2.setParent(parent);
			t2.setSize(size);
			return t2;
		}
		default: { // case STRUCT
			assert t2.isStruct();
			Map<Range<Long>, ECR> map = getCompatibleMap(t1.asStruct(),
					t2.asStruct());
			return ValueType.struct(map, size, parent);
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
			builder.put(findRoot((ECR) ecr),
					ImmutableSet.copyOf(map.asMap().get(ecr)));
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
			elemLoc.clearCjoins(cjoins);
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
		if (!structT.getParent().getECRs().isEmpty()) {
			unionType.setParent(structT.getParent());
		}
		setType(structECR, unionType);
		ECR root = findRoot(structECR);

		for (Pair<Size, ECR> cjoinPair : ccjoins)
			ccjoin(cjoinPair.fst(), root, cjoinPair.snd());

		for (ECR joinECR : cjoins)
			cjoin(root, joinECR);

		return unionType;
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
	 */
	private Map<Range<Long>, ECR> getCompatibleMap(StructType structT1,
			StructType structT2) {
		Map<Range<Long>, ECR> fieldMap1 = structT1.getFieldMap();
		Map<Range<Long>, ECR> fieldMap2 = structT2.getFieldMap();

		Map<Range<Long>, ECR> fieldMap = Maps.newHashMap();
		fieldMap.putAll(fieldMap1);

		for (Entry<Range<Long>, ECR> entry : ImmutableSet
				.copyOf(fieldMap2.entrySet())) {
			Range<Long> range2 = entry.getKey();
			ECR ecr2 = entry.getValue();
			if (fieldMap.containsKey(range2)) {
				ECR ecr1 = fieldMap.get(range2);
				join(ecr1, ecr2);
			}
			fieldMap.put(range2, ecr2);
		}
		return fieldMap;
	}

	void ensureSimple(ECR e) {
		ValueType type = getType(e);

		switch (type.getKind()) {
		case BOTTOM: {
			ValueType simType = ValueType.simple(ECR.createBottom(), Size.getBot(),
					Parent.getBottom());
			setType(e, simType);
			break;
		}
		case BLANK: {
			BlankType blankType = type.asBlank();
			ValueType simType = ValueType.simple(ECR.createBottom(),
					blankType.getSize(), blankType.getParent());
			setType(e, simType);
			return;
		}
		case STRUCT: {
			collapseStruct(e, type.asStruct());
			break;
		}
		default: { // SIMPLE
			break;
		}
		}
		return;
	}

	private Pair<ECR, ECR> swap(ECR e1, ECR e2) {
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		Pair<ValueType, ValueType> pair = swap(t1, t2);
		if (pair.fst() == t1) {
			return Pair.of(e1, e2);
		} else {
			return Pair.of(e2, e1);
		}
	}

	/**
	 * Swap <code>t1</code> and <code>t2</code> if <code> kind(t1) > kind(t2) 
	 * </code> the pair of value types <code>(t1', t2')</code> that
	 * <code>kind(t1') <= kind(t2')</code>
	 */
	private Pair<ValueType, ValueType> swap(ValueType t1, ValueType t2) {

		if (t1.isBottom())
			return Pair.of(t1, t2);
		if (t2.isBottom())
			return Pair.of(t2, t1);

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
}
