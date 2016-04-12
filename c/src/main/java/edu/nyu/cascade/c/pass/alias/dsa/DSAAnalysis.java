package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
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
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.c.pass.addrtaken.AddressTakenAnalysis;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import xtc.tree.Node;
import xtc.type.Type;

public class DSAAnalysis implements IRAliasAnalyzer<Region> {
	private final AddressTakenAnalysis addrTaken;
	private final LocalDataStructureImpl local;
	private final SteensDataStructureImpl steens;
	private final RegionPassImpl regPass;
	private final Multimap<Region, Expression> snapshot = HashMultimap.create();
	private final SymbolTable SymbolTable;
	
	private DSAAnalysis(SymbolTable symTbl) { 
		addrTaken = AddressTakenAnalysis.create(symTbl);
		local = LocalDataStructureImpl.create(addrTaken).init(symTbl);
		steens = SteensDataStructureImpl.create(local).init(symTbl);
		regPass = RegionPassImpl.create(steens);
		SymbolTable = symTbl;
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
	public Region getPointsToLoc(Region region) {
		return region;
	}

	@Override
	public long getRepTypeWidth(Region region) {
		//TODO: word-level analysis
		return CType.getInstance().getByteSize();
	}

	@Override
	public String getRepId(Region region) {
		Preconditions.checkNotNull(region);
		return region.toString();
	}

	@Override
	public Region getRep(Node Node) {
		Map<Node, Region> regionMap = regPass.getRegionMap();
		assert regionMap.containsKey(Node) : "No region for node";
		return regionMap.get(Node);
	}
	
	@Override
	public Region getStackRep(Node Node) {
		return getRep(Node);
	}

	@Override
	public Collection<Region> getFillInReps(Region Region, long length) {
		Region newReg = new Region(Region.N, null, Region.offset, length);
		Collection<Region> overlapRegions = Lists.newArrayList();
		Iterator<Region> RegItr = regPass.getRegions().iterator();
		while(RegItr.hasNext()) {
			Region reg = RegItr.next();
			if (reg.overlaps(newReg)) overlapRegions.add(reg);
		}
		return overlapRegions;
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		addrTaken.analysis(globalCFG, CFGs);
		local.analysis(globalCFG, CFGs);
		IOUtils.out().println("local analysis: ");
		ValueManager valueManager = local.getValueManager();
		for(IRControlFlowGraph CFG : CFGs) {
			String FuncID = CFG.getName();
			Type FuncTy = SymbolTable.lookupType(FuncID);
			Function func = (Function) valueManager.get(FuncID, FuncTy);
			local.getDSGraph(func).dump(IOUtils.outPrinter());
		}
		
		steens.analysis(globalCFG, CFGs);
		IOUtils.out().println("steensgaard analysis: ");
		steens.getResultGraph().dump(IOUtils.outPrinter());
		
		regPass.analysis(globalCFG, CFGs);
	}

	@Override
	public void addAllocRegion(Expression regExpr, Node node) {
//		if (!IOUtils.debugEnabled())	return;
		Region region = regPass.getRegionMap().get(node);
		snapshot.put(region, regExpr);
		IOUtils.out().println(displaySnapShot());
	}

	@Override
	public void addStackVar(Expression lval, Node node) {
//		if (!IOUtils.debugEnabled())	return;
		if (CType.getType(node).resolve().isFunction()) return;
		Region region = regPass.getRegionMap().get(node);
		snapshot.put(region, lval);
		IOUtils.out().println(displaySnapShot());
	}

	@Override
	public Map<Range<Long>, Region> getStructMap(Region Region, long length) {
		Region newReg = new Region(Region.N, null, Region.offset, length);
		Map<Range<Long>, Region> overlapRegions = Maps.newHashMap();
		Iterator<Region> RegItr = regPass.getRegions().iterator();
		while(RegItr.hasNext()) {
			Region reg = RegItr.next();
			if (reg.overlaps(newReg)) {
				long offset = reg.offset - Region.offset;
				assert (offset >= 0) : "negative offset";
				overlapRegions.put(Range.closedOpen(offset, offset + reg.length), reg);
			}
		}
		return overlapRegions;
	}

	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		DSNodeHandle NH = steens.getResultGraph().getNodeMap().get(funcNode);
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
	public boolean isAccessTypeSafe(Region rep) {
		// TODO Auto-generated method stub
		return false;
	}

}
