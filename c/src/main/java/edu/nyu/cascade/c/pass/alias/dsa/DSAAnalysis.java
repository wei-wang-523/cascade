package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Range;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.addrtaken.AddressTakenAnalysis;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import xtc.tree.Node;
import xtc.type.Type;

public class DSAAnalysis implements IRAliasAnalyzer<DSNodeHandle> {
	private final AddressTakenAnalysis addrTaken;
	private final LocalDataStructureImpl local;
	private final SteensDataStructureImpl steens;
	private final RegionPassImpl regPass;
	private final Multimap<DSNodeHandle, Expression> snapshot = HashMultimap.create();
	
	private DSAAnalysis(SymbolTable symTbl) { 
		addrTaken = AddressTakenAnalysis.create(symTbl);
		local = LocalDataStructureImpl.create(addrTaken).init(symTbl);
		steens = SteensDataStructureImpl.create(local).init(symTbl);
		regPass = RegionPassImpl.create(steens);
	}

	public static DSAAnalysis create(SymbolTable symbolTable) {
		return new DSAAnalysis(symbolTable);
	}

	@Override
	public String displaySnapShot() {
		return snapshot.asMap().toString();
	}

	@Override
	public void buildSnapShot() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public DSNodeHandle getPtsToRep(Node node) {
		Type ty = CType.getType(node);
		DSNodeHandle reg = getRep(node);
		assert !CType.isArithmetic(ty) : "Invalid pointer type";
		if (ty.resolve().isPointer()) 
			return reg.getLink(0);
		else
			return reg;
	}
	
	public DSNodeHandle getPtsToFieldRep(DSNodeHandle rep) {
		return rep;
	}

	@Override
	public long getRepWidth(DSNodeHandle NH) {
		//TODO: word-level analysis
		return CType.getInstance().getByteSize();
	}

	@Override
	public String getRepId(DSNodeHandle NH) {
		Preconditions.checkNotNull(NH);
		return NH.getNode().getID() + ":" + NH.getOffset();
	}

	@Override
	public DSNodeHandle getRep(Node Node) {
		Map<Pair<Node,String>, Region> regionMap = regPass.getRegionMap();
		String Scope = CType.getScopeName(Node);
		assert regionMap.containsKey(Pair.of(Node, Scope)) : "No region for node";
		Region region = regionMap.get(Pair.of(Node, Scope));
		return new DSNodeHandle(region.getNode(), region.getOffset());
	}
	
	@Override
	public DSNodeHandle getStackRep(Node Node) {
		return getRep(Node);
	}

	@Override
	public Collection<DSNodeHandle> getFieldReps(DSNodeHandle NH, Type ty) {
		Preconditions.checkNotNull(NH);
		long length = ty.resolve().isVoid() ? Long.MAX_VALUE
				: CType.getInstance().getSize(ty);
		Region newReg = new Region(NH.getNode(), null, NH.getOffset(), length);
		Collection<DSNodeHandle> overlapNHs = Lists.newArrayList();
		Iterator<Region> RegItr = regPass.getRegions().iterator();
		while(RegItr.hasNext()) {
			Region reg = RegItr.next();
			if (reg.overlaps(newReg)) 
				overlapNHs.add(new DSNodeHandle(reg.getNode(), reg.getOffset()));
		}
		if(!overlapNHs.isEmpty()) {
			return overlapNHs;
		} else {
			return Collections.singleton(NH);
		}
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		addrTaken.analysis(globalCFG, CFGs);
		local.analysis(globalCFG, CFGs);
		steens.analysis(globalCFG, CFGs);
		
		if (IOUtils.debugEnabled()) {
			IOUtils.out().println("steensgaard analysis: ");
			steens.getResultGraph().dump(IOUtils.outPrinter());
			steens.getGlobalsGraph().dump(IOUtils.outPrinter());
		}
		regPass.analysis(globalCFG, CFGs);
	}

	@Override
	public void addRegion(Expression regExpr, Node node) {
		if (!IOUtils.debugEnabled())	return;
		DSNodeHandle region = getPtsToRep(node);
		snapshot.put(region, regExpr);
		IOUtils.out().println(displaySnapShot());
	}

	@Override
	public void addVar(Expression lval, Node node) {
		if (!IOUtils.debugEnabled())	return;
		if (CType.getType(node).resolve().isFunction()) return;
		String scope = CType.getScopeName(node);
		Region region = regPass.getRegionMap().get(Pair.of(node, scope));
		snapshot.put(new DSNodeHandle(region.getNode(), region.getOffset()), lval);
		IOUtils.out().println(displaySnapShot());
	}

	@Override
	public Map<Range<Long>, DSNodeHandle> getStructMap(DSNodeHandle NH, long length) {
		Region newReg = new Region(NH.getNode(), null, NH.getOffset(), length);
		Map<Range<Long>, DSNodeHandle> overlapRegions = Maps.newHashMap();
		Iterator<Region> RegItr = regPass.getRegions().iterator();
		while(RegItr.hasNext()) {
			Region reg = RegItr.next();
			if (reg.overlaps(newReg)) {
				long offset = reg.getOffset() - NH.getOffset();
				assert (offset >= 0) : "negative offset";
				overlapRegions.put(Range.closedOpen(offset, offset + reg.getLength()), 
						new DSNodeHandle(reg.getNode(), reg.getOffset()));
			}
		}
		return overlapRegions;
	}

	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		Type funcTy = CType.getType(funcNode);
		DSNodeHandle NH;
		if (funcTy.resolve().isPointer()) {
			NH = getPtsToRep(funcNode);
		} else {
			NH = getRep(funcNode);
		}
		Collection<GlobalValue> GVs = NH.getNode().getGlobals();
		Collection<IRVar> Functions = Lists.newArrayList();
		for(GlobalValue GV : GVs) {
			if (!(GV instanceof Function)) continue;
			Functions.add(GV); 
		}
		return Functions;
	}

	@Override
	public void reset() {
		snapshot.clear();
		regPass.reset();
	}

	@Override
	public boolean isAccessTypeSafe(DSNodeHandle rep) {
		// TODO Auto-generated method stub
		return false;
	}

}
