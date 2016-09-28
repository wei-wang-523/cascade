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
import edu.nyu.cascade.util.Triple;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;
import xtc.type.PointerT;
import xtc.type.Type;

public class UnionFindECR {
	private final UnionFind<IRVar> uf;
	private final Set<ECR> structECRs = Sets.newLinkedHashSet();
	private final Set<ECR> collapseECRs = Sets.newLinkedHashSet();
	private final Set<Pair<ECR, ECR>> unionCastECRs = Sets.newLinkedHashSet();
	private final Map<ECR, Collection<Pair<Range<Long>, ECR>>> nestFieldECRMap = Maps
			.newHashMap();
	private final Set<Triple<Long, ECR, ECR>> injectFields = Sets
			.newLinkedHashSet();

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

	ECR createPointerECR(Type type) {
		ECR varECR = createECR(type);
		if (type.isInternal()) {
			return varECR;
		} else {
			SimpleType addrType = ValueType.simple(varECR,
					Size.createForType(PointerT.TO_VOID), Parent.getBottom());
			return createECR(addrType);
		}
	}

	ECR createECR(Type type) {
		Type cellType = CType.getCellType(type);
		Size size = Size.createForType(cellType);
		Parent parent = Parent.getBottom();
		if (CType.isScalar(cellType)) {
			return createECR(ValueType.simple(ECR.createBottom(), size, parent));
		} else if (CType.isStructOrUnion(cellType)) {
			return createECR(ValueType.struct(size, parent));
		} else {
			return createECR(ValueType.blank(size, Parent.getBottom()));
		}
	}

	boolean normalizeStructECRs() {
		boolean changed = false;

		Collection<ECR> top_structECRs = getTopParents(structECRs);
		structECRs.retainAll(top_structECRs);

		Map<ECR, TreeMap<Range<Long>, ECR>> structFlattenMap = Maps.newHashMap();
		for (ECR ecr : top_structECRs) {
			// Skip ECR if it has been collapsed when flattening other struct.
			if (!getType(ecr).isStruct()) {
				continue;
			}

			TreeMap<Range<Long>, ECR> flattenMap = flattenStructECRs(ecr);
			structFlattenMap.put(ecr, flattenMap);

			if (!getType(ecr).isStruct()) {
				IOUtils.err()
						.println("Top struct ECR has been collapsed when flattening.");
			}
		}

		for (TreeMap<Range<Long>, ECR> flattenFieldMap : structFlattenMap
				.values()) {
			changed |= mergeOverlapFields(flattenFieldMap);
		}

		return changed;
	}

	private boolean mergeOverlapFields(
			TreeMap<Range<Long>, ECR> flattenFieldMap) {
		Iterator<Entry<Range<Long>, ECR>> fieldItr = flattenFieldMap.entrySet()
				.iterator();
		if (!fieldItr.hasNext()) {
			return false;
		}

		boolean changed = false;
		Entry<Range<Long>, ECR> currPair = fieldItr.next();
		ECR currECR = currPair.getValue();
		long currOffset = currPair.getKey().lowerEndpoint();
		long currSize = getType(getLoc(currECR)).getSize().getValue();
		long currEndPoint = Math.max(currPair.getKey().upperEndpoint(),
				currOffset + currSize);
		Range<Long> currRange = Range.closedOpen(currOffset, currEndPoint);
		while (fieldItr.hasNext()) {
			Entry<Range<Long>, ECR> nextPair = fieldItr.next();
			ECR nextECR = nextPair.getValue();
			long nextOffset = nextPair.getKey().lowerEndpoint();
			long nextSize = getType(getLoc(nextECR)).getSize().getValue();
			long nextEndPoint = Math.max(nextPair.getKey().upperEndpoint(),
					nextOffset + nextSize);
			Range<Long> nextRange = Range.closedOpen(nextOffset, nextEndPoint);

			if (isDisjoint(currRange, nextRange)) {
				currECR = nextECR;
				currRange = nextRange;
			} else {
				// Merge field ECR (the points-to ECR of the field entry)
				changed |= join(currECR, nextECR);
				currRange = merge(currRange, nextRange);
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
				ECR field_loc_ecr = getLoc(field_ecr);
				if (fieldRangeMap.containsKey(range_offset)) {
					ECR curr_loc_ecr = getLoc(fieldRangeMap.get(range_offset));
					join(field_loc_ecr, curr_loc_ecr);
				} else {
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

	boolean normalizeUnionCastECRs() {
		boolean changed = false;
		Iterator<Pair<ECR, ECR>> unionCastItr = ImmutableSet.copyOf(unionCastECRs)
				.iterator();
		while (unionCastItr.hasNext()) {
			Pair<ECR, ECR> cast_pair = unionCastItr.next();
			Pair<ECR, ECR> pair = swap(cast_pair.fst(), cast_pair.snd());
			ECR e1 = pair.fst();
			ECR e2 = pair.snd();
			
			ValueType t1 = getType(e1);
			ValueType t2 = getType(e2);
			if (t1.isBlank() || t2.isBlank()) {
				continue;
			}
			
			if (t1.isSimple() && t2.isSimple()) {
				changed |= join(e2, e2);
				unionCastECRs.remove(cast_pair);
				continue;
			}

			Collection<Pair<Long, ECR>> sourceFieldEntries1 = getSourceFieldEntries(
					e1);
			Collection<Pair<Long, ECR>> sourceFieldEntries2 = getSourceFieldEntries(
					e2);
			
			if (!sourceFieldEntries1.isEmpty()) {
				changed |= injectFieldIntoSourceParent(sourceFieldEntries1, e2);
			}

			if (!sourceFieldEntries2.isEmpty()) {
				changed |= injectFieldIntoSourceParent(sourceFieldEntries2, e1);
			}
		}
		return changed;
	}

	/** Inject field into the source parents of source */
	private boolean injectFieldIntoSourceParent(
			Collection<Pair<Long, ECR>> sourceFieldEntries, ECR field) {
		boolean changed = false;

		for (Pair<Long, ECR> source_entry : sourceFieldEntries) {
			long offset = source_entry.fst();
			ECR struct = source_entry.snd();
			ValueType struct_type = getType(struct);
			if (struct_type.isStruct()) {
				ValueType field_type = getType(field);
				long struct_size = struct_type.getSize().getValue();
				long field_size = field_type.getSize().getValue();
				if (field_size + offset > struct_size) {
					Collection<Entry<Range<Long>, ECR>> fieldEntrySet = ImmutableSet
							.copyOf(struct_type.asStruct().getFieldMap().entrySet());
					for (Entry<Range<Long>, ECR> field_entry : fieldEntrySet) {
						Range<Long> range = field_entry.getKey();
						if (offset <= range.lowerEndpoint()) {
							ECR field_loc = getLoc(field_entry.getValue());

							if (field_type.isSimple()) {
								ensureSimple(field_loc);
								changed |= join(field_loc, field);
							} else {
								changed |= injectFieldIntoStruct(range.lowerEndpoint() - offset,
										field_loc, field);
							}
						}
					}
				} else {
					changed |= injectFieldIntoStruct(offset, field, struct);
				}
			}
		}

		return changed;
	}

	boolean normalizeCollapseECRs() {
		// Collect ECR has parents (optimization for arrays, no collapsing).
		Set<ECR> toCollapseECRs = Sets.newHashSet();
		for (ECR ecr : collapseECRs) {
			ValueType type = getType(ecr);
			if (type.isSimple()) {
				ECR loc = getLoc(ecr);
				ValueType loc_type = getType(loc);
				if (loc_type.getParent().isEmpty()) {
					continue;
				} else {
					toCollapseECRs.add(loc);
				}
			}
		}

		Collection<ECR> topECRs = getTopParents(toCollapseECRs);
		if (topECRs.isEmpty()) {
			return false;
		}

		boolean changed = false;
		for (ECR topECR : topECRs) {
			changed |= collapseStruct(topECR);
		}

		return changed;
	}

	void reset() {
		uf.reset();
		collapseECRs.clear();
		unionCastECRs.clear();
		structECRs.clear();
		injectFields.clear();
		// nestFieldECRMap.clear();
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

		if (!(type.isBlank() || type.isBottom())) {
			Collection<Pair<Size, ECR>> ccjoins = ImmutableList
					.copyOf(root.getCCjoins());
			root.clearCCjoins(ccjoins);
			for (Pair<Size, ECR> cjoinPair : ccjoins) {
				ccjoin(cjoinPair.fst(), root, cjoinPair.snd());
			}
		}

		if (!(type.isBottom())) {
			Collection<ECR> cjoins = ImmutableList.copyOf(root.getCjoins());
			root.clearCjoins(cjoins);
			for (ECR joinECR : cjoins) {
				cjoin(root, joinECR);
			}
		}
	}

	private boolean collapseStruct(ECR topECR) {
		Collection<ECR> collapseECRs = Sets.newHashSet();
		Collection<ValueType> nonStructTypes = Sets.newLinkedHashSet();
		Parent parent = Parent.getBottom();

		List<ECR> worklist = Lists.newArrayList();
		worklist.add(topECR);
		while (!worklist.isEmpty()) {
			ECR ecr = worklist.remove(0);
			collapseECRs.add(ecr);
			ValueType type = getType(ecr);
			parent = Parent.getLUB(parent, type.getParent());
			if (type.isStruct()) {
				Collection<ECR> elems = type.asStruct().getFieldMap().values();
				for (ECR elem : elems) {
					ECR elemLoc = getLoc(elem);
					if (collapseECRs.contains(elemLoc))
						continue;
					worklist.add(elemLoc);
				}
			} else {
				nonStructTypes.add(type);
			}
		}

		if (collapseECRs.size() <= 1) {
			return false;
		}

		// Collapse the collapseECRs
		Collection<ECR> cjoins = Sets.newHashSet();
		Collection<Pair<Size, ECR>> ccjoins = Sets.newHashSet();

		boolean changed = false;
		Iterator<ECR> collapse_itr = collapseECRs.iterator();
		ECR result = collapse_itr.next();
		while (collapse_itr.hasNext()) {
			ECR elem = collapse_itr.next();
			if (elem.equals(result))
				continue;

			cjoins.addAll(getCjoins(elem));
			elem.clearCjoins(cjoins);
			ccjoins.addAll(getCCjoins(elem));
			elem.clearCCjoins(ccjoins);

			union(result, elem);
			changed = true;
		}

		ValueType result_type = ValueType.bottom();
		for (ValueType elem_type : nonStructTypes) {
			result_type = unify(result_type, elem_type);
		}

		Parent new_parent = parent.removeParent(result);
		result_type.setParent(new_parent);

		setType(result, result_type);
		assert result_type.isSimple();
		for (Pair<Size, ECR> cjoinPair : ccjoins)
			ccjoin(cjoinPair.fst(), result, cjoinPair.snd());

		for (ECR joinECR : cjoins)
			cjoin(result, joinECR);

		return changed;
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
		case BLANK: {
			processBlankUnion(e1, e2);
			changed = true;
			break;
		}
		case SIMPLE: {
			if (t2.isStruct()) {
				unionCastECRs.add(Pair.of(e1, e2));
				changed = true;
			} else {
				assert t2.isSimple();
				changed |= processUnion(e1, e2);
			}
			break;
		}
		default: { // both are STRUCT
			changed |= processStructUnion(e1, e2);
			break;
		}
		}
		return changed;
	}

	private boolean injectFieldIntoStruct(long offset, ECR field_ecr,
			ECR struct_ecr) {
		Preconditions.checkArgument(getType(struct_ecr).isStruct());
		if (injectFields.contains(Triple.of(offset, field_ecr, struct_ecr))) {
			return false;
		}

		injectFields.add(Triple.of(offset, field_ecr, struct_ecr));
		if (field_ecr.equals(struct_ecr) && offset == 0) {
			return false;
		}

		ValueType struct_type = getType(struct_ecr);
		ValueType field_type = getType(field_ecr);
		long struct_size = struct_type.getSize().getValue();
		long field_size = field_type.getSize().getValue();
		assert (offset + field_size <= struct_size);

		Map<Range<Long>, ECR> field_map = struct_type.asStruct().getFieldMap();
		Range<Long> range = Range.closedOpen(offset, offset + field_size);
		if (field_map.containsKey(range)) {
			ECR _field_ecr = getLoc(field_map.get(range));
			return joinField(_field_ecr, field_ecr);
		} else {
			ECR addr_ecr = createECR(
					ValueType.simple(field_ecr, Size.getBot(), Parent.getBottom()));
			field_map.put(range, addr_ecr);
			// Update the parent of simp_ecr, inject a contains edge.
			Parent new_parent = Parent.create(struct_ecr);
			field_type.setParent(Parent.getLUB(new_parent, field_type.getParent()));
			return true;
		}
	}

	private boolean joinField(ECR e1, ECR e2) {
		Pair<ECR, ECR> swap_pair = swap(e1, e2);
		ECR e1_prime = swap_pair.fst();
		ECR e2_prime = swap_pair.snd();
		ValueType t1 = getType(e1_prime);
		ValueType t2 = getType(e2_prime);
		if (t1.isSimple() && t2.isStruct()) {
			collapseStruct(e2);
			join(e1, e2);
			return true;
		} else {
			return join(e1, e2);
		}
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

	private void processBlankUnion(ECR e1, ECR e2) {
		Preconditions.checkArgument(getType(e1).isBlank());
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		Size size1 = t1.getSize();
		Size size2 = t2.getSize();
		if (size1.isBottom() || size2.isBottom()
				|| size1.getValue() == size2.getValue()) {
			processUnion(e1, e2);
		} else {
			if (size1.getValue() < size2.getValue()) {
				unionCastECRs.add(Pair.of(e1, e2));
			} else {
				unionCastECRs.add(Pair.of(e2, e1));
			}
		}
	}

	private boolean processStructUnion(ECR e1, ECR e2) {
		Preconditions.checkArgument(getType(e1).isStruct());
		Preconditions.checkArgument(getType(e2).isStruct());
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);
		Size size1 = t1.getSize();
		Size size2 = t2.getSize();
		assert !size1.isBottom();
		assert !size2.isBottom();
		if (size1.equals(size2)) {
			return processUnion(e1, e2);
		} else {
			long value1 = size1.getValue();
			long value2 = size2.getValue();
			assert value1 != value2;
			if (value1 < value2) {
				unionCastECRs.add(Pair.of(e1, e2));
			} else {
				unionCastECRs.add(Pair.of(e2, e1));
			}
			return false;
		}
	}

	private boolean processUnion(ECR e1, ECR e2) {
		ValueType t1 = getType(e1);
		ValueType t2 = getType(e2);

		Collection<Pair<Size, ECR>> ccjoins1 = ImmutableList.copyOf(getCCjoins(e1));
		Collection<Pair<Size, ECR>> ccjoins2 = ImmutableList.copyOf(getCCjoins(e2));

		ECR root = union(e1, e2);
		ValueType unionType = unify(t1, t2);

		// Struct must have a compatible field map, set the root as the parent of
		// every field loc ECR.
		if (unionType.isStruct()) {
			Parent new_parent = Parent.create(root);
			for (ECR field_ecr : unionType.asStruct().getFieldMap().values()) {
				ECR field_loc_ecr = getLoc(field_ecr);
				ValueType field_type = getType(field_loc_ecr);
				Parent parent = Parent.getLUB(field_type.getParent(), new_parent);
				field_type.setParent(parent);
				setType(field_loc_ecr, field_type);
			}
		}

		// During the join process, there might be cycle. It means root might be set
		// to freshType. The type-union should take care of it -- union freshType to
		// unionType.
		ValueType freshType = getType(root);
		if (!freshType.equals(t1) && !freshType.equals(t2)) {
			unionType = unify(unionType, freshType);
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

		return true;
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
			expand(e1, rangeSize);
		}

		if (e1.equals(e2)) {
			return;
		}

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
				collapseStruct(e2);
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
		boolean isSource = t1.isSource() || t2.isSource();

		switch (t1.getKind()) {
		case BLANK: {
			t2.setParent(parent);
			t2.setSize(size);
			if (isSource) {
				t2.setSource();
			}
			return t2;
		}
		case SIMPLE: {
			assert t2.isSimple();
			ECR loc1 = t1.asSimple().getLoc();
			ECR loc2 = t2.asSimple().getLoc();
			join(loc1, loc2);
			ValueType loc_type1 = getType(loc1);
			ValueType loc_type2 = getType(loc2);
			long loc_size1 = loc_type1.getSize().getValue();
			long loc_size2 = loc_type2.getSize().getValue();
			if (loc_size1 != loc_size2) {
				IOUtils.errPrinter()
						.p("Join simple type with locations of different sizes: ")
						.p(loc_size1).p(',').p(loc_size2)
						.p("-- CFS always pick the smaller one.").pln();
			}
			ValueType t = loc_size1 < loc_size2 ? t1 : t2;
			t.setParent(parent);
			t.setSize(size);
			if (isSource) {
				t.setSource();
			}
			return t;
		}
		default: { // case STRUCT
			assert t2.isStruct();
			// assert t1.getSize().equals(t2.getSize());
			Map<Range<Long>, ECR> map = getCompatibleMap(t1.asStruct(),
					t2.asStruct());
			ValueType t = ValueType.struct(map, size, parent);
			if (isSource) {
				t.setSource();
			}
			return t;
		}
		}
	}

	void expand(ECR e, Size size) {
		ValueType eType = getType(e);
		if (eType.getSize().equals(size)) {
			return;
		}

		if (eType.isBottom()) {
			ValueType blankType = ValueType.blank(size, Parent.getBottom());
			setType(e, blankType);
		} else {
			Size sizePrime = Size.getLUB(size, eType.getSize());
			eType.setSize(sizePrime);
		}
	}

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
		Preconditions.checkNotNull(srcECR);
		ensureSimple(srcECR);
		ValueType type = getType(srcECR);
		return type.asSimple().getLoc();
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
		Preconditions.checkNotNull(e);
		ValueType type = getType(e);

		switch (type.getKind()) {
		case BOTTOM: {
			ValueType simType = ValueType.simple(ECR.createBottom(), Size.getBot(),
					Parent.getBottom());
			setType(e, simType);
			break;
		}
		case BLANK: {
			ValueType simType = ValueType.simple(ECR.createBottom(), type.getSize(),
					type.getParent());
			setType(e, simType);
			return;
		}
		case STRUCT: {
			collapseStruct(e);
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

	private Collection<ECR> getTopParents(Collection<ECR> ecrs) {
		Set<ECR> top_structECRs = Sets.newLinkedHashSet();
		Set<ECR> visited = Sets.newHashSet();

		List<ECR> worklist = Lists.newArrayList(ecrs);
		while (!worklist.isEmpty()) {
			ECR curr_ecr = worklist.remove(0);
			if (visited.contains(curr_ecr)) {
				continue;
			}
			visited.add(curr_ecr);

			ValueType type = getType(curr_ecr);
			Collection<ECR> parents = type.getParent().getECRs();
			if (parents.isEmpty()) {
				top_structECRs.add(curr_ecr);
			} else {
				if (IOUtils.debugEnabled()) {
					for (ECR ecr : parents) {
						boolean found_it = false;
						ValueType parent_type = getType(ecr);
						for (Entry<Range<Long>, ECR> entry : parent_type.asStruct()
								.getFieldMap().entrySet()) {
							found_it |= getLoc(entry.getValue()).equals(curr_ecr);
						}
						if (!found_it) {
							throw new IllegalStateException();
						}
					}
				}
				worklist.addAll(parents);
			}
		}

		return top_structECRs;
	}

	Collection<Pair<Long, ECR>> getSourceFieldEntries(ECR ecr) {
		Collection<Pair<Long, ECR>> top_parents = Sets.newLinkedHashSet();
		Set<Pair<Long, ECR>> visited = Sets.newHashSet();

		List<Pair<Long, ECR>> worklist = Lists.newArrayList();
		worklist.add(Pair.of((long) 0, ecr));
		while (!worklist.isEmpty()) {
			Pair<Long, ECR> pair = worklist.remove(0);
			if (visited.contains(pair)) {
				continue;
			}
			visited.add(pair);

			ECR curr_ecr = pair.snd();
			ValueType type = getType(curr_ecr);
			top_parents.add(pair);

			long offset = pair.fst();
			for (ECR parent : type.getParent().getECRs()) {
				ValueType parent_type = getType(parent);
				assert (parent_type.isStruct());
				boolean found_it = false;
				for (Entry<Range<Long>, ECR> entry : parent_type.asStruct()
						.getFieldMap().entrySet()) {
					Range<Long> range = entry.getKey();
					ECR field_ecr = getLoc(entry.getValue());
					if (field_ecr.equals(curr_ecr)) {
						long incr_offset = offset + range.lowerEndpoint();
						worklist.add(Pair.of(incr_offset, parent));
						found_it |= true;
					}
				}
				assert found_it;
			}
		}

		return top_parents;
	}

	private Collection<Pair<Range<Long>, ECR>> getOrCreateNestedFields(ECR ecr) {
		if (nestFieldECRMap.containsKey(ecr)) {
			return nestFieldECRMap.get(ecr);
		}

		Collection<Pair<Range<Long>, ECR>> nestFields = Sets.newLinkedHashSet();
		List<Pair<Range<Long>, ECR>> worklist = Lists.newArrayList();

		worklist.add(Pair.of(
				Range.closedOpen((long) 0, getType(ecr).getSize().getValue()), ecr));
		while (!worklist.isEmpty()) {
			Pair<Range<Long>, ECR> curr_entry = worklist.remove(0);
			if (nestFields.contains(curr_entry)) {
				continue;
			}

			nestFields.add(curr_entry);

			long curr_low = curr_entry.fst().lowerEndpoint();
			ECR curr_ecr = curr_entry.snd();
			ValueType curr_type = getType(curr_ecr);

			if (curr_type.isStruct()) {
				for (Entry<Range<Long>, ECR> entry : curr_type.asStruct().getFieldMap()
						.entrySet()) {
					ECR field_ecr = getLoc(entry.getValue());
					ValueType field_type = getType(field_ecr);
					long field_size = field_type.getSize().getValue();
					long field_low = curr_low + entry.getKey().lowerEndpoint();
					long field_high = curr_low + Math.max(field_size + field_low,
							entry.getKey().upperEndpoint());
					worklist
							.add(Pair.of(Range.closedOpen(field_low, field_high), field_ecr));
				}
			}
		}

		nestFieldECRMap.put(ecr, nestFields);
		return nestFields;
	}

	Collection<ECR> getNestedFields(ECR ecr, long offset, long size) {
		Preconditions.checkArgument(getType(ecr).isStruct());
		Collection<Pair<Range<Long>, ECR>> nested_fields = getOrCreateNestedFields(
				ecr);
		Range<Long> range = size == Integer.MAX_VALUE ? Range.atLeast(offset)
				: Range.closedOpen(offset, offset + size);
		Collection<ECR> fields = Sets.newLinkedHashSet();
		for (Pair<Range<Long>, ECR> field_entry : nested_fields) {
			Range<Long> field_range = field_entry.fst();
			if (isDisjoint(field_range, range)) {
				continue;
			} else {
				fields.add(findRoot(field_entry.snd()));
			}
		}

		return fields;
	}

	void pointerCast(ECR src_ecr, ECR target_ecr) {
		Preconditions.checkArgument(getType(src_ecr).isSimple());
		Preconditions.checkArgument(getType(target_ecr).isSimple());
		ECR src_loc = getLoc(src_ecr);
		ECR target_loc = getLoc(target_ecr);
		join(src_loc, target_loc);
	}
}
