package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeSet;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CPrinter;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.pass.IRPass;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Visitor;
import xtc.type.Type;

public final class RegionPassImpl implements IRPass {
	private SteensDataStructureImpl SteensDS;
	private Map<Node, Region> RegionMap = Maps.newHashMap();
	private TreeSet<Region> Regions = Sets.newTreeSet();
	
	static RegionPassImpl create(IRPass... prePasses) {
		Preconditions.checkArgument(prePasses.length == 1);

		RegionPassImpl regionPass = new RegionPassImpl();
		assert(prePasses[0] instanceof SteensDataStructureImpl);
		SteensDataStructureImpl steensDS = (SteensDataStructureImpl) prePasses[0];
		
		regionPass.SteensDS = steensDS;
		return regionPass;
	}
	
	public boolean runOnModule(
			IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		
		RegionBuilder regionBuilder = new RegionBuilder();
		
		// First step, build the globals graph
		regionBuilder.visit(globalCFG);
		
		// build the graph for each function CFG
		for(IRControlFlowGraph CFG : CFGs) {
			regionBuilder.visit(CFG);
		}
		
		normalizeRegionMap();
		return false;
	}

	class RegionBuilder {
		
		private IRControlFlowGraph currCFG;

		private class LvalVisitor extends Visitor {
			void encode(Node node) {
				dispatch(node);  
				init(node);
			}
			
			@Override
			public Object unableToVisit(Node node) {
				IOUtils.err()
		          .println(
		              "APPROX: Treating unexpected node type as NULL: "
		                  + node.getName());
				return null;
			}
			
			@SuppressWarnings("unused")
			public void visitSimpleDeclarator(GNode node) {}
			
			@SuppressWarnings("unused")
			public void visitPrimaryIdentifier(GNode node) {}
			
			@SuppressWarnings("unused")
			public void visitIndirectionExpression(GNode node) {
				rvalVisitor.encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitIndirectComponentSelection(GNode node) {
				rvalVisitor.encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitDirectComponentSelection(GNode node) {
				encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitSubscriptExpression(GNode node) {
				encode(node.getNode(0));
				rvalVisitor.encode(node.getNode(1));
			}
		}
		
		private class RvalVisitor extends Visitor {
			void encode(Node node) {
				dispatch(node);
			}
			
			@Override
			public Object unableToVisit(Node node) {
				IOUtils.err()
		          .println(
		              "APPROX: Treating unexpected node type as NULL: "
		                  + node.getName());
				return null;
			}
			
			@SuppressWarnings("unused")
			public void visitPrimaryIdentifier(GNode node) {
				Type Ty = CType.getType(node);
				if (Ty.isEnumerator()) return;
				lvalVisitor.encode(node);
			}
			
			@SuppressWarnings("unused")
			public void visitIntegerConstant(GNode node) { }
			
			@SuppressWarnings("unused")
			public void visitCharacterConstant(GNode node) { }
			
			@SuppressWarnings("unused")
			public void visitEqualityExpression(GNode node) { 
				encode(node.getNode(0));
				encode(node.getNode(2));
			}
			
			@SuppressWarnings("unused")
			public void visitShiftExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}
			
			@SuppressWarnings("unused")
			public void visitTypeName(GNode node) { }
			
			@SuppressWarnings("unused")
			public void visitSizeofExpression(GNode node) {
				encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitUnaryMinusExpression(GNode node) {
				encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitIndirectComponentSelection(GNode node) {
				lvalVisitor.encode(node);
			}
			
			@SuppressWarnings("unused")
			public void visitDirectComponentSelection(GNode node) {
				lvalVisitor.encode(node);
			}
			
			@SuppressWarnings("unused")
			public void visitSubscriptExpression(GNode node) {
				lvalVisitor.encode(node);
			}
			
			@SuppressWarnings("unused")
			public void visitRelationalExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}
			
			@SuppressWarnings("unused")
			public void visitMultiplicativeExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
			}
			
			@SuppressWarnings("unused")
			public void visitCastExpression(GNode node) {
				encode(node.getNode(1));
			}
			
			@SuppressWarnings("unused")
			public void visitIndirectionExpression(GNode node) {
				lvalVisitor.encode(node);
			}
			
			@SuppressWarnings("unused")
			public void visitAddressExpression(GNode node) {
				lvalVisitor.encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public void visitAdditiveExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));			
			}
			
			@SuppressWarnings("unused")
			public void visitAssignmentExpression(GNode node) {
				lvalVisitor.encode(node.getNode(0));
				encode(node.getNode(2));
			}
		}
		
		private LvalVisitor lvalVisitor = new LvalVisitor();
		private RvalVisitor rvalVisitor = new RvalVisitor();
		
		void visit(IRStatement stmt) {
			switch (stmt.getType()) {
			case DECLARE:
			case DECLARE_ARRAY: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				lvalVisitor.encode(lhs);
			  	break;
			}
			case INIT:
			case ASSIGN: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				Node rhs = stmt.getOperand(1).getSourceNode();
				lvalVisitor.encode(lhs);
				rvalVisitor.encode(rhs);
				break;
			}
			case FREE:
			case ASSUME:
			case ASSERT: {
				Node opNode = stmt.getOperand(0).getSourceNode();
				rvalVisitor.encode(opNode);
				break;
			}
			case RETURN: {
				if(stmt.getOperands() != null && !stmt.getOperands().isEmpty()) {
					Node ret = stmt.getOperand(0).getSourceNode();
					lvalVisitor.encode(ret);
				}
				break;
			}
			case ALLOCA:
			case CALLOC:
			case MALLOC: {
				Node lhs = stmt.getOperand(0).getSourceNode();
			    lvalVisitor.encode(lhs);
			    break;
			}
			case CALL: {
				// Set up the return value...
				Type retTy = CType.getType(stmt.getSourceNode());
				
				if (!retTy.resolve().isVoid()) {
					Node retNode = stmt.getOperand(1).getSourceNode();
					lvalVisitor.encode(retNode);
				}
				
				Node funcNode = stmt.getOperand(0).getSourceNode();
				Type funcTy = CType.getType(funcNode);
					
				Node funcId = CAnalyzer.getIdentifier((GNode) funcNode);
				if (funcId == null || !CType.getType(funcId).resolve().isFunction()) {
					lvalVisitor.encode(funcNode);
				}
					
				// Get the type of function. Normalize the function to call
				// as a function pointer via pointerizing the function type
				funcTy = CType.getInstance().pointerize(funcTy);
				funcTy = funcTy.toPointer().getType();
					
				// Calculate the arguments vector...
				// Add all fixed pointer arguments, then merge the rest together
				Iterator<IRExpression> ArgItr = stmt.getOperands().iterator();
				ArgItr.next();
				if (!funcTy.resolve().toFunction().getResult().isVoid())	ArgItr.next();
				
				while (ArgItr.hasNext()) {
					Node ArgNode = ArgItr.next().getSourceNode();
					rvalVisitor.encode(ArgNode);
				}
				
				break;
			}
			default:
				break;
			}
		}
		
		void visit(IRControlFlowGraph CFG) {
			currCFG = CFG;
			
			Collection<IRBasicBlock> BBs =
					Lists.reverse(CFG.topologicalSeq(CFG.getEntry()));
			for(IRBasicBlock BB : BBs) {
				for(IRStatement stmt : BB.getStatements()) visit(stmt);
				
				for(IREdge<?> outgoing : CFG.getOutgoingEdges(BB)) {
					if(null != outgoing.getGuard()) {
						Node opNode = outgoing.getGuard().getSourceNode();
						rvalVisitor.encode(opNode);
					}
				}
			}
		}

		private void init(Node N) {
			Type Ty = CType.getType(N);
//			if (Ty.resolve().isFunction()) return;
			
			DSNodeHandle NH = null;
			if (Identifiers.GLOBAL_CFG.equals(currCFG.getName())) {
				NH = SteensDS.getGlobalsGraph().getNodeMap().get(N); 
			} else {
				NH = SteensDS.getResultGraph().getNodeMap().get(N);
			}
			
			long length = getPointedTypeSize(Ty);
			Region region = new Region(NH.getNode(), Ty, NH.getOffset(), length);
			region = idx(region);
			RegionMap.put(N, region);
		}
		
		private long getPointedTypeSize(Type Ty) {			
			Ty = Ty.resolve();
			
			if (Ty.isStruct() || Ty.isUnion()) {
				Ty = Ty.toStructOrUnion().getMember(0);
				return getPointedTypeSize(Ty);
			} else if (Ty.isArray()) {
				Ty = Ty.toArray().getType();
				return getPointedTypeSize(Ty);
			} else {
				return CType.getInstance().getSize(Ty);
			}
		}

		private Region idx(Region R) {
			if(Regions.contains(R)) return R;
			
			Iterator<Region> regItr = Regions.iterator();
			
			Region overlapReg = null;
			while (regItr.hasNext()) {
				Region reg = regItr.next();
				if (reg.overlaps(R)) {
					reg.merge(R); 
					overlapReg = reg; break;
				}
			}
			
			if (overlapReg == null) {
				Regions.add(R); return R;
			}
			
			// Remove the following overlapped regions
			Collection<Region> removeRegs = Lists.newArrayList();
			while (regItr.hasNext()) {
				Region reg = regItr.next();
				if (!overlapReg.overlaps(reg)) break;
				
				overlapReg.merge(reg);
				removeRegs.add(reg);
			}
			Regions.removeAll(removeRegs);
			
			return overlapReg;
		}
	}
	
	public Map<Node, Region> getRegionMap() {
		return RegionMap;
	}

	@Override
	public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		runOnModule(globalCFG, CFGs);
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	private void normalizeRegionMap() {
		for(Node N : ImmutableSet.copyOf(RegionMap.keySet())) {
			Region NR = RegionMap.get(N);
			if (Regions.contains(NR)) continue;
			
			Region R1 = Regions.lower(NR);
			Region R2 = Regions.higher(NR);
			Region R = R1.overlaps(NR)? R1 : R2;
			
			assert (R.offset <= NR.offset && 
					R.offset + R.length >= NR.offset + NR.length);
			RegionMap.put(N, R);
		}
	}

	TreeSet<Region> getRegions() {
		return Regions;
	}
}