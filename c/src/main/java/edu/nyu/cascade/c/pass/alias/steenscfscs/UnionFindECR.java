package edu.nyu.cascade.c.pass.alias.steenscfscs;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.type.PointerT;
import xtc.type.Type;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.steenscfscs.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.util.FieldRangeMap;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.UnionFind;
import edu.nyu.cascade.util.UnionFind.Partition;

public class UnionFindECR {
	private final UnionFind<IRVar> uf;
	/**
	 * Record the pointer arithmetic pending joins if the numeric operand is a
	 * constant
	 */
	private final Table<Pair<ECR, Long>, Pair<ECR, Long>, Long> ptrAriJoins = HashBasedTable
			.create();
	/**
	 * Track the pointer cast pending joins
	 */
	private final Map<Pair<ECR, Long>, Pair<ECR, Long>> ptrCastJoins = Maps
			.newLinkedHashMap();
	/**
	 * Track the source ecr (created for nodes as operands of statement)
	 */
	private final Collection<ECR> sourceECRs = Sets.newHashSet();

	private Multimap<Pair<ECR, ECR>, Range<Long>> missingMatches = HashMultimap
			.create();
	private Map<ECR, ECR> missingAlign = Maps.newHashMap();

	private UnionFindECR() {
		uf = UnionFind.create();
	}

	static UnionFindECR create() {
		return new UnionFindECR();
	}

	void reset() {
		uf.reset();
		ptrAriJoins.clear();
		ptrCastJoins.clear();
		sourceECRs.clear();
		missingMatches.clear();
		missingAlign.clear();
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
				setType(e2,
						ValueType.simple(type1.asSimple().getLoc(),
								type1.asSimple().getFunc(), rangeSize, Parent.getBottom(),
								type2.hasOpTag()));
				return;
			case BLANK: {
				setType(e2,
						ValueType.simple(type1.asSimple().getLoc(),
								type1.asSimple().getFunc(), type2.getSize(), type2.getParent(),
								type2.hasOpTag()));
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
				RangeMap<Long, ECR> fieldMapCopy = FieldRangeMap.create();
				fieldMapCopy.putAll(type1.asStruct().getFieldMap());
				setType(e2, ValueType.struct(fieldMapCopy, rangeSize,
						Parent.getBottom(), type2.hasOpTag()));
				return;
			}
			case BLANK: {
				RangeMap<Long, ECR> fieldMapCopy = FieldRangeMap.create();
				fieldMapCopy.putAll(type1.asStruct().getFieldMap());
				Size size2 = type2.getSize();
				setType(e2, ValueType.struct(fieldMapCopy, size2, type2.getParent(),
						type2.hasOpTag()));
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				return;
			}
			case SIMPLE: {
				addCCjoin(rangeSize, e1, e2);
				Size size2 = type2.getSize();
				if (!Size.isLessThan(rangeSize, size2))
					expand(e2, rangeSize);
				for (ECR elemECR : type1.asStruct().getFieldMap().asMapOfRanges()
						.values()) {
					ValueType elemType = getType(elemECR);
					Size elemSize = elemType.getSize();
					ccjoin(elemSize, elemECR, e2);
				}
				return;
			}
			case STRUCT: {
				throw new IllegalArgumentException();
				// Size size2 = type2.getSize();
				// if(!Size.isLessThan(rangeSize, size2)) {
				// addCCjoin(rangeSize, e1, e2);
				// expand(e2, rangeSize); return;
				// }
				//
				// ValueType unifyStructType = unify(type1, type2); // unify structure
				// type eagerly
				// setType(e1, unifyStructType);
				// setType(e2, unifyStructType);
				// return;
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
			if (t1.hasOpTag())
				t2.enableOpTag();
			return t2;
		}

		Parent parent = Parent.getLUB(t1.getParent(), t2.getParent());
		Size size = Size.getLUB(t1.getSize(), t2.getSize());
		boolean hasOpTag = t1.hasOpTag() || t2.hasOpTag();

		switch (t1.getKind()) {
		case BLANK: {
			switch (t2.getKind()) {
			case BLANK:
				return ValueType.blank(size, parent, hasOpTag);
			case SIMPLE: {
				return ValueType.simple(t2.asSimple().getLoc(), t2.asSimple().getFunc(),
						size, parent, hasOpTag);
			}
			default: { // case STRUCT:
				return ValueType.struct(t2.asStruct().getFieldMap(), size, parent,
						hasOpTag);
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

				return ValueType.simple(loc, func, size, parent, hasOpTag);
			}
			default: // case STRUCT:
				throw new IllegalArgumentException();
			}
		}
		case STRUCT: {
			if (ValueTypeKind.STRUCT.equals(t2.getKind())) {
				RangeMap<Long, ECR> map = getCompatibleMap(t1.asStruct(),
						t2.asStruct());
				return ValueType.struct(map, size, parent, hasOpTag);
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
		return findRoot(type.asSimple().getLoc());
	}

	ECR getFunc(ECR srcECR) {
		ensureSimple(srcECR);
		ValueType type = getType(srcECR);
		return type.asSimple().getFunc();
	}

	void enableOp(ECR loc) {
		getType(loc).enableOpTag();
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

	void ptrAri(ECR targetECR, long targetSize, ECR srcECR, long srcSize,
			long shift) {
		Pair<ECR, Long> targetPair = Pair.of(targetECR, targetSize);
		Pair<ECR, Long> srcPair = Pair.of(srcECR, srcSize);
		if (ptrCastJoins.containsKey(srcPair)) {
			Pair<ECR, Long> rootPair = ptrCastJoins.get(srcPair);
			if (!sourceECRs.contains(srcPair.fst())) {
				ptrCastJoins.remove(srcPair);
			}
			ptrAriJoins.put(targetPair, rootPair, shift);
		} else {
			ptrAriJoins.put(targetPair, srcPair, shift);
		}
	}

	void ptrCast(ECR targetECR, long targetSize, ECR srcECR, long srcSize) {
		Pair<ECR, Long> targetKey = Pair.of(targetECR, targetSize);
		Pair<ECR, Long> srcKey = Pair.of(srcECR, srcSize);
		if (ptrCastJoins.containsKey(srcKey)) {
			ptrCastJoins.put(targetKey, ptrCastJoins.get(srcKey));

			if (!sourceECRs.contains(srcKey.fst())) {
				ptrCastJoins.remove(srcKey);
			}
		} else {
			ptrCastJoins.put(targetKey, srcKey);
		}
	}

	void addSourceECR(ECR ecr) {
		sourceECRs.add(ecr);
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
			ValueType simType = ValueType.simple(createBottomLocFunc(),
					blankType.getSize(), blankType.getParent());
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

	private void collapse(ECR e1, ECR e2) {
		ECR root = join(e1, e2);

		// Parent is stored at the points-to loc of
		Parent parent = getType(root).getParent();
		Collection<ECR> parentECRs = ImmutableList.copyOf(parent.getECRs());

		for (ECR ecr : parentECRs) {
			ValueType ecrType = getType(ecr);
			if (ecrType.isStruct())
				collapseStruct(ecr, ecrType.asStruct());
		}

		enableOp(root);
	}

	boolean containsPtrAritJoin(ECR locECR, long size) {
		return ptrAriJoins.containsRow(Pair.of(locECR, size));
	}

	void replacePtrAriJoin(ECR freshECR, long freshSize, ECR oldECR,
			long oldSize) {
		Pair<ECR, Long> oldKey = Pair.of(oldECR, oldSize);
		Pair<ECR, Long> freshKey = Pair.of(freshECR, freshSize);
		Entry<Pair<ECR, Long>, Long> entry = ptrAriJoins.row(oldKey).entrySet()
				.iterator().next();
		Pair<ECR, Long> targetKey = entry.getKey();
		long value = ptrAriJoins.remove(oldKey, targetKey);
		ptrAriJoins.put(freshKey, targetKey, value);
	}

	void cleanup() {
		boolean changed;
		do {
			changed = false;
			changed |= clearPtrCast();
			changed |= clearPointerArithmetic();
		} while (changed);

		for (Cell<Pair<ECR, Long>, Pair<ECR, Long>, Long> cell : ptrAriJoins
				.cellSet()) {
			ECR srcLocECR = getLoc(cell.getColumnKey().fst());
			ECR targetLocECR = getLoc(cell.getRowKey().fst());
			collapse(targetLocECR, srcLocECR);
		}
		ptrAriJoins.clear();

		for (Entry<Pair<ECR, Long>, Pair<ECR, Long>> cell : ptrCastJoins
				.entrySet()) {
			Pair<ECR, Long> targetPair = cell.getKey();
			ECR targetECR = findRoot(targetPair.fst());
			long targetSize = cell.getKey().snd();
			Pair<ECR, Long> sourcePair = cell.getValue();
			ECR srcECR = findRoot(sourcePair.fst());
			smash(srcECR, targetECR, targetSize);
		}
		ptrCastJoins.clear();
	}

	void smash(ECR srcECR, ECR targetECR, long targetSize) {
		ECR srcLocECR = getLoc(srcECR);
		ECR targetLocECR = getLoc(targetECR);
		join(targetLocECR, srcLocECR);

		ValueType srcLocType = getType(srcLocECR);
		for (ECR parent : srcLocType.getParent().getECRs()) {
			ValueType parentType = getType(parent);
			if (!parentType.isStruct())
				continue;

			for (Range<Long> range : getFieldInterval(parentType, srcLocECR)) {
				long offset = range.lowerEndpoint();
				Range<Long> newRange = Range.closedOpen(offset, offset + targetSize);
				addField(parentType.asStruct(), targetECR, newRange);
			}
		}
	}

	void normalize(ECR srcECR, Type fieldType, Range<Long> range,
			RangeMap<Long, ECR> fieldMap) {

		if (fieldMap.asMapOfRanges().containsKey(range))
			return;

		RangeMap<Long, ECR> subMap = fieldMap.subRangeMap(range);
		Map<Range<Long>, ECR> subMapRanges = subMap.asMapOfRanges();

		if (subMapRanges.isEmpty()) {
			ECR ecr = createFieldECR(range, fieldType, srcECR);
			fieldMap.put(range, ecr);
			return;
		}

		Range<Long> span = subMap.span();
		fieldMap.remove(span);

		Range<Long> newRange = subMap.span().span(range);

		Iterator<ECR> elemECRItr = subMapRanges.values().iterator();
		ECR joinECR = elemECRItr.next();
		while (elemECRItr.hasNext())
			joinECR = cjoin(elemECRItr.next(), joinECR);
		// uf.collapse(joinECR);

		fieldMap.put(newRange, joinECR);
		return;
	}

	/**
	 * Create a field ECR with <code>xtcType</code>, <code>scopeName</code>, and
	 * <code>parent</code>. If <code>xtcType</code> is scalar, this method creates
	 * a single field ECR, otherwise, two ECRs will be created, one for the field
	 * and the other for the region it points to. For the field ECR, whose address
	 * ECR will be the same as the address attached with the ECR of
	 * <code>parent</code>.
	 * 
	 * @param range
	 * @param type
	 * @param srcECR
	 * @return
	 */
	private ECR createFieldECR(Range<Long> range, Type type, ECR srcECR) {
		Parent parent = Parent.create(findRoot(srcECR));
		Size size = CType.isScalar(type) ? Size.createForType(type) : Size.getBot();
		ECR fieldECR = ECR.create(ValueType.blank(size, parent));

		SimpleType addrType = ValueType.simple(fieldECR, ECR.createBottom(),
				Size.createForType(new PointerT(type)), Parent.getBottom());

		ECR addrECR = ECR.create(addrType);

		StructType srcType = getType(srcECR).asStruct();
		srcType.getFieldMap().put(range, addrECR);
		return addrECR;
	}

	private boolean clearPointerArithmetic() {
		int origSize = ptrAriJoins.size();
		List<Cell<Pair<ECR, Long>, Pair<ECR, Long>, Long>> worklist = Lists
				.newArrayList(ptrAriJoins.cellSet());
		ptrAriJoins.clear();
		while (!worklist.isEmpty()) {
			Cell<Pair<ECR, Long>, Pair<ECR, Long>, Long> cell = worklist.remove(0);
			Pair<ECR, Long> targetPair = cell.getRowKey();
			Pair<ECR, Long> srcPair = cell.getColumnKey();
			assert (!ptrCastJoins.containsKey(srcPair));

			ECR targetECR = findRoot(targetPair.fst());
			ECR srcECR = findRoot(srcPair.fst());

			ECR srcLocECR = getLoc(srcECR);

			long targetSize = targetPair.snd();

			long shift = cell.getValue();

			Multimap<Pair<ECR, ECR>, Range<Long>> missingMatch = HashMultimap
					.create();
			boolean success = processCast(targetECR, srcLocECR,
					Range.closedOpen(shift, shift + targetSize), missingMatch);
			if (!success) {
				ptrAriJoins.put(targetPair, srcPair, shift);
				missingMatch.clear();
			} else {
				missingMatches.putAll(missingMatch);
			}
		}
		return ptrAriJoins.size() != origSize;
	}

	private boolean clearPtrCast() {
		int origSize = ptrCastJoins.size();
		List<Entry<Pair<ECR, Long>, Pair<ECR, Long>>> worklist = Lists
				.newArrayList(ptrCastJoins.entrySet());
		ptrCastJoins.clear();

		while (!worklist.isEmpty()) {
			Entry<Pair<ECR, Long>, Pair<ECR, Long>> cell = worklist.remove(0);
			Pair<ECR, Long> targetPair = cell.getKey();
			Pair<ECR, Long> srcPair = cell.getValue();
			ECR targetECR = targetPair.fst(), srcECR = srcPair.fst();

			ECR targetLocECR = getLoc(targetECR), srcLocECR = getLoc(srcECR);
			ValueType srcLocType = getType(srcLocECR);
			long targetSize = targetPair.snd();

			Size srcLocSize = srcLocType.getSize();
			if (srcLocSize.isBottom()) {
				join(targetLocECR, srcLocECR);
				continue;
			}

			Multimap<Pair<ECR, ECR>, Range<Long>> missingMatch = HashMultimap
					.create();
			boolean success = processCast(targetECR, srcLocECR,
					Range.closedOpen((long) 0, targetSize), missingMatch);
			if (!success) {
				ptrCastJoins.put(targetPair, srcPair);
			} else {
				missingMatches.putAll(missingMatch);
			}
		}

		return ptrCastJoins.size() != origSize;
	}

	private boolean processCast(ECR targetECR, ECR srcLocECR,
			Range<Long> targetRange,
			Multimap<Pair<ECR, ECR>, Range<Long>> missingMatch) {
		boolean match = mathincWithinSrcECR(targetECR, srcLocECR, targetRange);
		if (match)
			return true;

		ValueType srcLocType = getType(srcLocECR);
		Parent srcLocParent = srcLocType.getParent();
		if (srcLocParent.isBottom()) {
			missingMatch.put(Pair.of(targetECR, srcLocECR), targetRange);
			return false;
		}

		boolean matchAny = false;
		for (ECR parent : srcLocParent.getECRs()) {
			// Only find the matching parent to cast. If the parent size is
			// not compatible with targetSize, then skip.
			// FIXME: not sound for pointer analysis!
			ValueType parentType = getType(parent);
			Iterable<Range<Long>> fieldIntervals = getFieldInterval(parentType,
					srcLocECR);
			boolean matchParent = false;
			Collection<Pair<ECR, Range<Long>>> outofSizeParents = Lists
					.newArrayList();

			for (Range<Long> fieldInterval : fieldIntervals) {
				long low = fieldInterval.lowerEndpoint();
				long targetLower = targetRange.lowerEndpoint();
				long targetUpper = targetRange.upperEndpoint();
				Range<Long> fieldTargetRange = Range.closedOpen(low + targetLower,
						low + targetUpper);
				boolean matchInterval = mathincWithinSrcECR(targetECR, parent,
						fieldTargetRange);
				if (!matchInterval)
					outofSizeParents.add(Pair.of(parent, fieldTargetRange));
				matchParent |= matchInterval;
			}

			// If fails matching, check its grandparents
			for (Pair<ECR, Range<Long>> pair : outofSizeParents) {
				matchParent |= processCast(targetECR, pair.fst(), pair.snd(),
						missingMatch);
			}

			matchAny |= matchParent;
		}
		return matchAny;
	}

	private boolean mathincWithinSrcECR(ECR targetECR, ECR srcLocECR,
			Range<Long> range) {
		Preconditions.checkArgument(!getType(srcLocECR).isBottom());
		ValueType srcLocType = getType(srcLocECR);
		ECR targetLocECR = getLoc(targetECR);
		long low = range.lowerEndpoint();
		if (low < 0)
			return false;

		final long high = range.upperEndpoint();

		if (srcLocType.isSimple()) {
			Size srcLocSize = srcLocType.getSize();
			if (srcLocSize.isTop())
				return false;
			long srcSize = srcLocSize.getValue();
			if (srcSize < high)
				return false;

			join(targetLocECR, srcLocECR);
			return true;
		}

		else if (srcLocType.isBlank()) {
			Size srcLocSize = srcLocType.getSize();
			assert (!srcLocSize.isBottom());
			if (srcLocSize.isTop())
				return false;
			long srcSize = srcLocSize.getValue();
			if (srcSize < high)
				return false;

			if (low == 0 && high == srcSize) {
				join(targetLocECR, srcLocECR);
				return true;
			}

			join(targetLocECR, srcLocECR);
			return true;
		}

		else { // srcLocType is structure type
			Size srcLocSize = srcLocType.getSize();
			assert (!srcLocSize.isBottom());
			if (srcLocSize.isTop()) {
				boolean targetLocWithinSrcLoc = Iterables.any(
						srcLocType.asStruct().getFieldMap().asMapOfRanges().keySet(),
						new Predicate<Range<Long>>() {
							@Override
							public boolean apply(Range<Long> range) {
								return range.upperEndpoint() >= high;
							}
						});
				if (!targetLocWithinSrcLoc)
					return false;

				addFieldIfAlign(srcLocType.asStruct(), targetECR, range);
				return true;
			} else {
				long srcSize = srcLocSize.getValue();
				if (srcSize < high)
					return false;

				if (low == 0 && srcSize == high) {
					join(srcLocECR, targetLocECR);
					return true;
				}

				addFieldIfAlign(srcLocType.asStruct(), targetECR, range);
				return true;
			}
		}
	}

	private void addFieldIfAlign(StructType structT, ECR fieldAddrECR,
			Range<Long> fieldInterval) {
		RangeMap<Long, ECR> fieldMap = structT.getFieldMap();
		Map<Range<Long>, ECR> spanMap = fieldMap.subRangeMap(fieldInterval)
				.asMapOfRanges();
		if (spanMap.isEmpty()) {
			fieldMap.put(fieldInterval, fieldAddrECR);
			return;
		}
		ECR fieldECR = getLoc(fieldAddrECR);

		for (Entry<Range<Long>, ECR> fieldEntry : spanMap.entrySet()) {
			ValueType fieldType = getType(fieldECR);
			Range<Long> spanFieldInterval = fieldEntry.getKey();
			ECR spanFieldAddrECR = fieldEntry.getValue();
			ECR spanFieldECR = getLoc(spanFieldAddrECR);
			ValueType spanFieldType = getType(spanFieldECR);
			if (spanFieldInterval.equals(fieldInterval)) {
				join(spanFieldECR, fieldECR);
			} else if (spanFieldInterval.encloses(fieldInterval)) {
				long low = fieldInterval.lowerEndpoint()
						- spanFieldInterval.lowerEndpoint();
				long high = fieldInterval.upperEndpoint()
						- spanFieldInterval.lowerEndpoint();
				Range<Long> subFieldInterval = Range.closedOpen(low, high);

				if (spanFieldType.isBlank()) {
					StructType structFieldType = ValueType.struct(spanFieldType.getSize(),
							spanFieldType.getParent());
					addFieldIfAlign(structFieldType, fieldAddrECR, subFieldInterval);
					setType(spanFieldECR, structFieldType);
				} else if (spanFieldType.isStruct()) {
					addFieldIfAlign(spanFieldType.asStruct(), fieldAddrECR,
							subFieldInterval);
				} else {
					missingAlign.put(spanFieldECR, fieldECR);
				}
			} else if (fieldInterval.encloses(spanFieldInterval)) {
				long low = spanFieldInterval.lowerEndpoint()
						- fieldInterval.lowerEndpoint();
				long high = spanFieldInterval.upperEndpoint()
						- fieldInterval.lowerEndpoint();
				Range<Long> subFieldRange = Range.closedOpen(low, high);

				if (fieldType.isBlank()) {
					StructType structFieldType = ValueType.struct(fieldType.getSize(),
							fieldType.getParent());
					addFieldIfAlign(structFieldType, spanFieldAddrECR, subFieldRange);
					setType(fieldECR, structFieldType);
				} else if (fieldType.isStruct()) {
					addFieldIfAlign(fieldType.asStruct(), spanFieldAddrECR,
							subFieldRange);
				} else {
					missingAlign.put(spanFieldECR, fieldECR);
				}
			} else {
				missingAlign.put(spanFieldECR, fieldECR);
			}
		}
	}

	private void addField(StructType structT, ECR fieldAddrECR,
			Range<Long> fieldInterval) {
		RangeMap<Long, ECR> fieldMap = structT.getFieldMap();
		Map<Range<Long>, ECR> spanMap = fieldMap.subRangeMap(fieldInterval)
				.asMapOfRanges();
		if (spanMap.isEmpty()) {
			fieldMap.put(fieldInterval, fieldAddrECR);
			return;
		}

		ECR fieldECR = getLoc(fieldAddrECR);
		ValueType fieldType = getType(fieldECR);

		for (Entry<Range<Long>, ECR> fieldEntry : spanMap.entrySet()) {
			Range<Long> spanFieldInterval = fieldEntry.getKey();
			ECR spanFieldAddrECR = fieldEntry.getValue();
			ECR spanFieldECR = getLoc(spanFieldAddrECR);
			ValueType spanFieldType = getType(spanFieldECR);
			if (spanFieldInterval.encloses(fieldInterval)) {
				long low = fieldInterval.lowerEndpoint()
						- spanFieldInterval.lowerEndpoint();
				long high = fieldInterval.upperEndpoint()
						- spanFieldInterval.lowerEndpoint();
				Range<Long> subFieldInterval = Range.closedOpen(low, high);

				if (spanFieldType.isBlank()) {
					StructType structFieldType = ValueType.struct(spanFieldType.getSize(),
							spanFieldType.getParent());
					addField(structFieldType, fieldAddrECR, subFieldInterval);
					setType(spanFieldECR, structFieldType);
				} else if (spanFieldType.isStruct()) {
					addField(spanFieldType.asStruct(), fieldAddrECR, subFieldInterval);
				} else {
					join(spanFieldECR, fieldECR);
				}
			} else if (fieldInterval.encloses(spanFieldInterval)) {
				long low = spanFieldInterval.lowerEndpoint()
						- fieldInterval.lowerEndpoint();
				long high = spanFieldInterval.upperEndpoint()
						- fieldInterval.lowerEndpoint();
				Range<Long> subFieldRange = Range.closedOpen(low, high);

				if (fieldType.isBlank()) {
					StructType structFieldType = ValueType.struct(fieldType.getSize(),
							fieldType.getParent());
					addField(structFieldType, spanFieldAddrECR, subFieldRange);
					setType(fieldECR, structFieldType);
				} else if (fieldType.isStruct()) {
					addField(fieldType.asStruct(), spanFieldAddrECR, subFieldRange);
				} else {
					join(spanFieldECR, fieldECR);
				}
			} else {
				join(spanFieldECR, fieldECR);
			}
		}
	}

	private Iterable<Range<Long>> getFieldInterval(ValueType parentType,
			final ECR fieldECR) {
		RangeMap<Long, ECR> fieldRangeMap = parentType.asStruct().getFieldMap();
		Iterable<Entry<Range<Long>, ECR>> entries = Iterables.filter(
				fieldRangeMap.asMapOfRanges().entrySet(),
				new Predicate<Entry<Range<Long>, ECR>>() {
					@Override
					public boolean apply(Entry<Range<Long>, ECR> entry) {
						return getLoc(entry.getValue()).equals(fieldECR);
					}
				});

		Iterable<Range<Long>> entryKeys = Iterables.transform(entries,
				new Function<Entry<Range<Long>, ECR>, Range<Long>>() {
					@Override
					public Range<Long> apply(Entry<Range<Long>, ECR> input) {
						return input.getKey();
					}
				});
		return entryKeys;
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
		Collection<ECR> elems = structT.getFieldMap().asMapOfRanges().values();
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
	private RangeMap<Long, ECR> getCompatibleMap(StructType structT1,
			StructType structT2) {
		RangeMap<Long, ECR> fieldMap1 = structT1.getFieldMap();
		RangeMap<Long, ECR> fieldMap2 = structT2.getFieldMap();

		RangeMap<Long, ECR> fieldMap = FieldRangeMap.create();
		fieldMap.putAll(fieldMap1);

		for (Entry<Range<Long>, ECR> entry : fieldMap2.asMapOfRanges().entrySet()) {
			Range<Long> range = entry.getKey();
			ECR ecr = entry.getValue();
			RangeMap<Long, ECR> subMap = fieldMap.subRangeMap(range);
			Map<Range<Long>, ECR> subMapRanges = subMap.asMapOfRanges();
			if (subMapRanges.isEmpty()) {
				fieldMap.put(range, ecr);
				continue;
			}

			Range<Long> span = subMap.span();
			fieldMap.remove(span);

			Range<Long> newRange = range.span(span);
			ECR joinECR = ecr;

			for (ECR elemECR : subMapRanges.values()) {
				joinECR = join(joinECR, elemECR);
			}

			fieldMap.put(newRange, joinECR);
		}

		return fieldMap;
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
			Collection<ECR> elems = t2.asStruct().getFieldMap().asMapOfRanges()
					.values();
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
