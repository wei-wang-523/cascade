package edu.nyu.cascade.ir.memory.layout;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.MemoryVarSets;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;

public class OrderLinearMemLayoutEncoding implements IROrderMemLayoutEncoding {

	private final ExpressionEncoding exprEncoding;
	private final IRDataFormatter dataFormatter;
	private final Type addrType, sizeType;
	private final CType cTypeAnalyzer;

	private OrderLinearMemLayoutEncoding(ExpressionEncoding exprEncoding,
			IRDataFormatter dataFormatter) {
		this.exprEncoding = exprEncoding;
		this.dataFormatter = dataFormatter;
		addrType = dataFormatter.getAddressType();
		sizeType = dataFormatter.getSizeType();
		cTypeAnalyzer = exprEncoding.getCTypeAnalyzer();
	}

	public static OrderLinearMemLayoutEncoding create(
			ExpressionEncoding exprEncoding, IRDataFormatter dataFormatter) {
		return new OrderLinearMemLayoutEncoding(exprEncoding, dataFormatter);
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression lastRegion) {
		Preconditions.checkNotNull(lastRegion);
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();

		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();

		try {

			/* The upper bound of the stack variable won't overflow */
			for (Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
				Expression stVar = stVarEntry.getKey();
				xtc.type.Type stVarType = stVarEntry.getValue();
				long stVarSize = cTypeAnalyzer.getSize(stVarType);
				if (stVarSize < 0)
					continue;

				Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
				builder.add(exprEncoding.notOverflow(stVar, stVarSizeExpr)
						.asBooleanExpression());
			}

			/* All the stack vars are ordered */
			Iterator<Entry<Expression, xtc.type.Type>> stVarItr = stVarsMap.entrySet()
					.iterator();
			Expression stackBound = null;

			if (stVarItr.hasNext()) {
				stackBound = stVarItr.next().getKey();
			}

			while (stVarItr.hasNext()) {
				Entry<Expression, xtc.type.Type> stVarEntry2 = stVarItr.next();
				Expression stVar2 = stVarEntry2.getKey();
				xtc.type.Type stVarType2 = stVarEntry2.getValue();
				long stVarSize2 = cTypeAnalyzer.getSize(stVarType2);
				if (stVarSize2 < 0)
					continue;

				Expression stVarSizeExpr2 = exprEncoding.integerConstant(stVarSize2);
				Expression stVarBound2 = exprEncoding.plus(stVar2, stVarSizeExpr2);
				builder.add(exprEncoding.greaterThan(stackBound, stVarBound2)
						.asBooleanExpression());
				stackBound = stVar2;
			}

			if (stackBound != null) {
				Expression nullPtr = dataFormatter.getNullAddress();
				if (sizeArr == null) {
					builder.add(exprEncoding.greaterThan(stackBound, nullPtr)
							.asBooleanExpression());
				} else {
					/*
					 * lastRegionBound = lastRegion != 0 ? lastRegion + size[lastRegion] :
					 * 0;
					 */
					Expression heapBound = lastRegion.neq(nullPtr).ifThenElse(
							exprEncoding.plus(lastRegion, sizeArr.index(lastRegion)),
							nullPtr);

					builder.add(exprEncoding.greaterThan(stackBound, heapBound)
							.asBooleanExpression());
				}
			}
		} catch (TheoremProverException e) {
			throw new ExpressionFactoryException(e);
		}
		return builder.build();
	}

	@Override
	public BooleanExpression validMalloc(ArrayExpression sizeArr,
			Expression lastRegion, Expression ptr, Expression size) {
		Preconditions.checkNotNull(sizeArr);
		Preconditions.checkNotNull(lastRegion);
		Preconditions
				.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions
				.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));

		try {
			Expression lastRegionBound = exprEncoding.plus(lastRegion,
					sizeArr.index(lastRegion));
			Expression ptrBound = exprEncoding.plus(ptr, size);
			Expression nullPtr = dataFormatter.getNullAddress();

			BooleanExpression notNull = ptr.neq(nullPtr);
			BooleanExpression validMalloc = exprEncoding
					.and(exprEncoding.lessThanOrEqual(ptr, ptrBound),
							// not over flow but size could be zero
							exprEncoding.or(lastRegion.eq(nullPtr),
									// last region is null (not allocated)
									exprEncoding.lessThanOrEqual(lastRegionBound, ptr)
							// larger than the last allocated region
							)).asBooleanExpression();

			return notNull.and(validMalloc);
		} catch (TheoremProverException e) {
			throw new ExpressionFactoryException(e);
		}
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(MemoryVarSets varSets,
			ArrayExpression sizeArr, Expression ptr) {
		Preconditions
				.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions
				.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));

		ImmutableSet.Builder<BooleanExpression> disjs = new ImmutableSet.Builder<BooleanExpression>();

		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
		Collection<Expression> hpRegs = varSets.getHeapRegions();

		try {
			/*
			 * TODO: Check the scope of local variable, this will be unsound to take
			 * address of local variable out of scope
			 */

			/* In any stack variable */
			for (Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
				Expression stVar = stVarEntry.getKey();
				xtc.type.Type stVarType = stVarEntry.getValue();
				long stVarSize = cTypeAnalyzer.getSize(stVarType);
				Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
				disjs.add(exprEncoding.within(stVar, stVarSizeExpr, ptr)
						.asBooleanExpression());
			}

			/* In any heap region */
			Expression nullPtr = dataFormatter.getNullAddress();
			Expression sizeZro = dataFormatter.getSizeZero();

			for (Expression hpReg : hpRegs) {
				Expression hpRegSizeExpr = sizeArr.index(hpReg);
				disjs.add(exprEncoding
						.and(hpReg.neq(nullPtr), hpRegSizeExpr.neq(sizeZro),
								exprEncoding.within(hpReg, hpRegSizeExpr, ptr))
						.asBooleanExpression());
			}
		} catch (TheoremProverException e) {
			throw new ExpressionFactoryException(e);
		}
		return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(MemoryVarSets varSets,
			ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions
				.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions
				.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));

		ImmutableSet.Builder<BooleanExpression> disjs = new ImmutableSet.Builder<BooleanExpression>();

		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
		Collection<Expression> hpRegs = varSets.getHeapRegions();

		try {

			/* In any stack variable */
			for (Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
				Expression stVar = stVarEntry.getKey();
				xtc.type.Type stVarType = stVarEntry.getValue();
				long stVarSize = cTypeAnalyzer.getSize(stVarType);
				Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
				disjs.add(exprEncoding.within(stVar, stVarSizeExpr, ptr, size)
						.asBooleanExpression());
			}

			Expression nullPtr = dataFormatter.getNullAddress();
			Expression sizeZro = dataFormatter.getSizeZero();

			/* In any heap region */
			for (Expression hpReg : hpRegs) {
				Expression hpRegSizeExpr = sizeArr.index(hpReg);

				disjs.add(exprEncoding
						.and(hpReg.neq(nullPtr), hpRegSizeExpr.neq(sizeZro),
								exprEncoding.within(hpReg, hpRegSizeExpr, ptr, size))
						.asBooleanExpression());
			}
		} catch (TheoremProverException e) {
			throw new ExpressionFactoryException(e);
		}

		return disjs.build();
	}

	@Override
	public BooleanExpression validFree(ArrayExpression markArr,
			Expression region) {
		Preconditions
				.checkArgument(markArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(markArr.getType().getElementType().isBoolean());
		Preconditions.checkArgument(region.getType().equals(addrType));

		BooleanExpression mark = markArr.index(region).asBooleanExpression();
		BooleanExpression tt = mark.getType().asBooleanType().tt();
		return mark.eq(tt);
	}
}
