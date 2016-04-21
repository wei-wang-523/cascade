package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.Function;
import edu.nyu.cascade.c.pass.GlobalValue;
import edu.nyu.cascade.c.pass.GlobalVariable;
import edu.nyu.cascade.c.pass.Value;
import edu.nyu.cascade.c.pass.ValueManager;
import edu.nyu.cascade.c.pass.addrtaken.AddressTakenAnalysis;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRPass;
import xtc.Constants;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Visitor;
import xtc.type.PointerT;
import xtc.type.StaticReference;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

public final class LocalDataStructureImpl extends DataStructuresImpl {
	private AddressTakenAnalysis AddrTakenPass;

	private LocalDataStructureImpl() {
		super("Local");
	}
	
	static LocalDataStructureImpl create(IRPass... prePasses) {
		LocalDataStructureImpl ds = new LocalDataStructureImpl();
		assert (prePasses.length == 1);
		assert (prePasses[0] instanceof AddressTakenAnalysis);
		ds.AddrTakenPass = (AddressTakenAnalysis) prePasses[0];
		return ds;
	}
	
	@Override
	public LocalDataStructureImpl init(SymbolTable symbolTable) {
		return (LocalDataStructureImpl) super.init(symbolTable);
	}

	@Override
	public boolean runOnModule(SymbolTable symTbl,
			IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		
		// First step, build the globals graph
		{
			GraphBuilder GGB = new GraphBuilder(GlobalsGraph);
			symTbl.enterScope(globalCFG);
			GGB.visit(globalCFG);
			
			// Add Functions to the globals graph
			for(IRControlFlowGraph CFG : CFGs) {
				String FuncID = CFG.getName();
				Type FuncTy = symTbl.lookupType(FuncID);
				Function FB = (Function) ValueManager.get(FuncID, FuncTy);
				if (AddrTakenPass.hasAddressTaken(FB)) {
					GGB.mergeFunction(FB);
				}
			}
		}
		
		// Next step, iterate through the nodes in the globals graph, union
		// together the globals into equivalence classes.
		formGlobalECs();

		// Iterate through the address taken functions in the globals graph,
		// collecting them in a list, to be used as target for call sites that
		// cannot be resolved.
		formGlobalFunctionList();
		GlobalsGraph.maskIncompleteMarkers();
		
		// Calculate all of the graphs...
		for(IRControlFlowGraph CFG : CFGs) {
			symTbl.enterScope(CFG);
			DSGraph G = new DSGraphImpl(GlobalECs, TypeSS, GlobalsGraph);
			String FuncID = CFG.getName();
			Type FuncTy = symTbl.lookupType(FuncID);
			Function FB = (Function) ValueManager.get(FuncID, FuncTy);
			setDSGraph(FB, G);
			
			@SuppressWarnings("unused")
			GraphBuilder GGB = new GraphBuilder(CFG, G);
			
			Collection<DSCallSite> AuxFuncCalls = G.getAuxFunctionCalls();
			AuxFuncCalls.addAll(G.getFunctionCalls());
			propagateUnknownFlag(G);
			
			CallGraph.insureEntry(FB);
			G.buildCallGraph(CallGraph, GlobalFunctionList, true);
			
			G.maskIncompleteMarkers();
			G.markIncompleteNodes(DSSupport.MarkIncompleteFlags.MarkFormalArgs.value() 
					| DSSupport.MarkIncompleteFlags.IgnoreGlobals.value());
			cloneIntoGlobals(G, DSSupport.CloneFlags.DontCloneCallNodes.value()
					| DSSupport.CloneFlags.DontCloneAuxCallNodes.value()
					| DSSupport.CloneFlags.StripAllocaBit.value());
			
			formGlobalECs();
		}
		
		GlobalsGraph.markIncompleteNodes(DSSupport.MarkIncompleteFlags.MarkFormalArgs.value() 
				| DSSupport.MarkIncompleteFlags.IgnoreGlobals.value());
		GlobalsGraph.computeExternalFlags(DSSupport.ComputeExternalFlags.ProcessCallSites.value());
		

		// Now that we've computed all of the graphs, and merged all of the info into
		// the globals graph, see if we have further constrained the globals in the
		// program if so, update GlobalECs and remove the extraneous globals from the
		// program.
		formGlobalECs();

		propagateUnknownFlag(GlobalsGraph);
		for (IRControlFlowGraph CFG : CFGs) {
			String FuncID = CFG.getName();
			Type FuncTy = symTbl.lookupType(FuncID);
			Function FB = (Function) ValueManager.get(FuncID, FuncTy);
			DSGraph Graph = getOrCreateGraph(FB);
			Graph.maskIncompleteMarkers();
			cloneGlobalsInto(Graph, DSSupport.CloneFlags.DontCloneCallNodes.value() |
					DSSupport.CloneFlags.DontCloneAuxCallNodes.value());
			Graph.markIncompleteNodes(DSSupport.MarkIncompleteFlags.MarkFormalArgs.value() 
					| DSSupport.MarkIncompleteFlags.IgnoreGlobals.value());
		}
		return false;
	}
	
	@Override
	ValueManager getValueManager() {
		return ValueManager;
	}

	private void propagateUnknownFlag(DSGraph g) {
	    List<DSNode> workList = Lists.newArrayList();
	    Set<DSNode> visited = Sets.newHashSet();
	    for (DSNode I : g.getNodes()) {
	      if (I.isUnknownNode())	workList.add(I);
	    }

	    while (!workList.isEmpty()) {
	      DSNode N = workList.remove(0);
	      if (visited.contains(N)) continue;
	      visited.add(N);
	      N.setUnknownMarker();
	      for (Entry<Long, DSNodeHandle> I : N.Links.entrySet()) {
	        if (!I.getValue().isNull())
	          workList.add(I.getValue().getNode());
	      }
	    }
	}

	class GraphBuilder {
		
		private DSNodeHandle load(DSNodeHandle PtrNH, Type Ty) {
			
			// Create a DSNode for the pointer dereferenced by the load.  If the DSNode
			// is NULL, do nothing more (this can occur if the load is loading from a
			// NULL pointer constant (bug-point can generate such code).
			//
			PtrNH = getValueDest(PtrNH, Ty);
			assert !PtrNH.isNull() : "Load from null";
			
			// Make that the node is read from...
			PtrNH.getNode().setReadMarker();
			
			// Ensure a type-record exists...
			PtrNH.getNode().growSizeForType(Ty, PtrNH.getOffset());
			
			PtrNH.getNode().mergeTypeInfo(Ty, PtrNH.getOffset());
			
			
			// Do not load the content if it is composite value. 
			// It is viewed as a pointer to the composite value.
			//
			return CType.isScalar(Ty) ? getLink(PtrNH, 0) : PtrNH;
		}
		
		private DSNodeHandle fieldSelect(DSNodeHandle NodeH, Type StructTy, String FieldName) {
			// Ensure that the indexed pointer has a DSNode.
			if (NodeH.isNull()) {
				NodeH.setTo(createNode(), 0);
			}
			
			// There are a few quick and easy cases to handle.  If  the DSNode of the
			// indexed pointer is already folded, then we know that the result of the
			// GEP will have the same offset into the same DSNode
			// as the indexed pointer.
			if (!NodeH.isNull() && NodeH.getNode().isNodeCompletelyFolded()) {
				return NodeH;
			}
			
			// Okay, no easy way out.  Calculate the offset into the object being
			// indexed  into a structure
			
			// Determine the offset (in bytes) between the result of the GEP and the
			// GEP's pointer operand.
			long requiredSize = CType.getInstance().getSize(StructTy) + NodeH.getOffset();
			
			// Grow the DSNode size as needed.
			if (!NodeH.getNode().isArrayNode() || NodeH.getNode().getSize() <= 0) {
				if (requiredSize > NodeH.getNode().getSize()) {
					NodeH.getNode().growSize(requiredSize);
				}
			}
			
			long offset = CType.getInstance().getOffset(StructTy, FieldName);
			
			// Add in the offset calculated...
			DSNodeHandle FieldNodeH = new DSNodeHandle(NodeH.getNode(), NodeH.getOffset() + offset);
			
			// Check the offset
			DSNode N = FieldNodeH.getNode();
			if (N != null) {
				N.checkOffsetFoldIfNeeded(FieldNodeH.getOffset());
			}
			
			// NodeH is now the pointer we want to GEP to be...
			return FieldNodeH;
		}
		
		private DSNodeHandle getElemPtr(Node lhs, Node rhs, String op) {
			DSNodeHandle lhsNH = lvalVisitor.encode(lhs);
			Type lhsTy = CType.getType(lhs);
			
			// Get the points-to DSNodeHandle if lhsTy is pointer type,
			// otherwise, ptrNH is lhsNH if lhsTy is array type.
			DSNodeHandle ptrNH = load(lhsNH, lhsTy);
			Type ptrTy = CType.getInstance().pointerize(lhsTy);
			Type idxTy = CType.getType(rhs);
			boolean isPlus = op.equals("+");
			
			// Get the updated pointed DSNodeHandle
			DSNodeHandle resPtrNH = getElemPtrNH(ptrNH, ptrTy, idxTy, isPlus);
			// Create the new DSNodeHandle for the pointer arithmetic expression
			// which points-to resPtrNH
			DSNodeHandle resNH = new DSNodeHandle(createNode(), 0);
			resNH.getNode().growSize(CType.getInstance().getSize(PointerT.TO_VOID));
			resNH.setLink(0, resPtrNH);
			return resNH;
		}
		
		private DSNodeHandle getElemPtrNH(DSNodeHandle ptrNH, Type ptrTy, Type idxTy,
				boolean isPlus) {
			Preconditions.checkArgument(ptrTy.isPointer());
			if (!ptrNH.isNull() && ptrNH.getNode().isNodeCompletelyFolded()) {
				return ptrNH;
			}
			
			DSNodeHandle NodeH = new DSNodeHandle();
			NodeH.mergeWith(ptrNH);
			
			if ( idxTy.hasConstant() && ptrNH.getOffset() == 0 && !ptrNH.getNode().isAllocaNode()) {
				long offset = isPlus ? idxTy.getConstant().longValue() 
						: -idxTy.getConstant().longValue();
				// Grow the DSNode size as needed.
				long requiredSize = offset + CType.getInstance().getSize(idxTy);
				if (ptrNH.getNode().getSize() <= requiredSize){
					ptrNH.getNode().growSize (requiredSize);
				}

				// Add in the offset calculated...
				NodeH.setOffset(ptrNH.getOffset()+offset);
				
				 // Check the offset
		        DSNode N = NodeH.getNode();
		        if (N != null) N.checkOffsetFoldIfNeeded(NodeH.getOffset());
		        
		        return NodeH;
			}
			
			// Unless we're advancing the pointer by zero bytes via array indexing,
			// fold the node (i.e., mark it type-unknown) and indicate that we're
			// indexing zero bytes into the object (because all fields are aliased).
			//
			// Note that we break out of the loop if we fold the node.  Once
			// something is folded, all values within it are considered to alias.
			if (!idxTy.hasConstant()) {
				// Treat the memory object (DSNode) as an array.
				NodeH.getNode().setArrayMarker();
				Type CurTy = ptrTy.toPointer().getType().resolve();
				
				// Ensure that the DSNode's size is large enough to contain one
				// element of the type to which the pointer points.
				if (!CurTy.isArray() && NodeH.getNode().getSize() <= 0){
			          NodeH.getNode().growSize(CType.getInstance().getSize(CurTy));
				} else if (CurTy.isArray() && NodeH.getNode().getSize() <= 0){
					Type ETy = CurTy.toArray().getType();
					while (ETy.isArray()) {
			            ETy = ETy.toArray().getType();
					}
					NodeH.getNode().growSize(CType.getInstance().getSize(ETy));
				}
				
		        // Fold the DSNode if we're indexing into it in a type-incompatible
		        // manner.  That can occur if:
		        //  1) The DSNode represents a pointer into the object at a non-zero
		        //     offset.
		        //  2) The offset of the pointer is already non-zero.
		        //  3) The size of the array element does not match the size into which
		        //     the pointer indexing is indexing.
				if (NodeH.getOffset() != 0 || (!CurTy.isArray() &&
						(NodeH.getNode().getSize() != CType.getInstance().getSize(CurTy)))) {
					NodeH.getNode().foldNodeCompletely();
					NodeH.getNode();
				}
			}

			// Check the offset
			DSNode N = NodeH.getNode();
			if (N != null) N.checkOffsetFoldIfNeeded(NodeH.getOffset());
			
			return NodeH;
		}
		
		private DSNodeHandle cast(Type fromTy, Type toTy, DSNodeHandle fromNH) {
			// IntToPtrCast
			if (toTy.resolve().isPointer() && fromTy.resolve().isInteger()) {
				DSNode N = createNode();
				N.setIntToPtrMarker();
				N.setUnknownMarker();
				DSNodeHandle NH = new DSNodeHandle(N, 0);
				return NH;
			}
			
			// PtrToCast
			if (toTy.resolve().isInteger() && fromTy.resolve().isPointer()) {
				DSNode N = getValueDest(fromNH, fromTy).getNode();
				if (N != null) N.setPtrToIntMarker();
				return fromNH;
			}
			
			if (toTy.resolve().isPointer()) {
				DSNodeHandle Ptr = getValueDest(fromNH, fromTy);
				if (!Ptr.isNull())	return Ptr;
			}
			
			DSNodeHandle ResNH = new DSNodeHandle();
			return ResNH;
		}
		
		private void ensureSafeIndexAccess(DSNodeHandle NodeH, Type ElemTy) {
			// Treat the memory object (DSNode) as an array.
			NodeH.getNode().setArrayMarker();
			
			// Ensure that the DSNode's size is large enough to contain one
			// element of the type to which the pointer points.
			// Ensure that the DSNode's size is large enough to contain one
			// element of the type to which the pointer points.
			if (!ElemTy.resolve().isArray() && NodeH.getNode().getSize() <= 0) {
				long ElemTySize = CType.getInstance().getSize(ElemTy);
				NodeH.getNode().growSize(ElemTySize + NodeH.getOffset());
			} else if (ElemTy.resolve().isArray() && NodeH.getNode().getSize() <= 0) {
				Type CurrElemTy = ElemTy.resolve().toArray().getType();
				while (CurrElemTy.resolve().isArray()) {
					CurrElemTy = CurrElemTy.resolve().toArray().getType();
				}
				long CurrElemTySize = CType.getInstance().getSize(CurrElemTy);
				NodeH.getNode().growSize(CurrElemTySize);
			}
			
			// Fold the DSNode if we're indexing into it in a type-incompatible 
			// manner.  That can occur if 
			// 1) the DSNode represents a pointer into the memory object at a non-zero 
			//    offset, 
			// 2) the offset of the pointer is already non-zero, 
			// 3) the size of the array element does not match the size into which the 
			//    pointer index is indexing. Indexing into an array must always at the 
			// 	  base of the memory object.
			if (NodeH.getOffset() != 0
					|| (!ElemTy.resolve().isArray()
							&& NodeH.getNode().getSize() != CType.getInstance().getSize(ElemTy))) {
				NodeH.getNode().foldNodeCompletely();
				NodeH.getNode();
			}
		}

		private class LvalVisitor extends Visitor {
			private DSNodeHandle encode(Node node) {
				if (G.getNodeMap().contains(node)) 
					return G.getNodeMap().get(node);
				
				DSNodeHandle NH = (DSNodeHandle) dispatch(node);
				G.getNodeMap().put(node, NH);
				return NH;
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
			public DSNodeHandle visitCastExpression(GNode node) {
				return encode(node.getNode(1));
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitAddressExpression(GNode node) {
				DSNodeHandle NH = new DSNodeHandle(createNode(), 0);
				NH.getNode().growSize(CType.getInstance().getSize(PointerT.TO_VOID));
				NH.setLink(0, lvalVisitor.encode(node.getNode(0)));
				return NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitIndirectionExpression(GNode node) {
				return rvalVisitor.encode(node.getNode(0));
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitSimpleDeclarator(GNode node) {
				String name = node.getString(0);
				Scope varScope = SymbolTable.getScope(node);
				IRVarInfo varInfo = (IRVarInfo) varScope.lookup(name);
				Value v = ValueManager.getOrCreate(varInfo);
				return G.getNodeForValue(v);
			}

			@SuppressWarnings("unused")
			public DSNodeHandle visitPrimaryIdentifier(GNode node) {
				String name = node.getString(0);
				Type ty = CType.getType(node);
				if (ty.isError()) return new DSNodeHandle();
				Value v = ValueManager.get(name, ty);
				return G.getNodeForValue(v);
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitIndirectComponentSelection(GNode node) {
				Node OpN = node.getNode(0);
				DSNodeHandle NodeH = rvalVisitor.encode(OpN);
				Type StructTy = CType.getType(OpN).resolve().toPointer().getType();
				String FieldName = node.getString(1);
				return fieldSelect(NodeH, StructTy, FieldName);
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitDirectComponentSelection(GNode node) {
				Node OpN = node.getNode(0);
				DSNodeHandle NodeH = encode(OpN);
				Type StructTy = CType.getType(OpN);
				String FieldName = node.getString(1);
				return fieldSelect(NodeH, StructTy, FieldName);
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitSubscriptExpression(GNode node) {
				Node Base = node.getNode(0);
				Node Idx = node.getNode(1);
				
				Type BaseTy = CType.getType(Base);
				DSNodeHandle NodeH =
						BaseTy.resolve().isArray() ? encode(Base) : rvalVisitor.encode(Base);
				DSNodeHandle IdxNH = rvalVisitor.encode(Idx);
				
				// Ensure that the indexed pointer has a DSNode.
				if (NodeH.isNull()) {
					NodeH.setTo(createNode(), 0);
				}
				
				// There are a few quick and easy cases to handle.  If  the DSNode of the
				// indexed pointer is already folded, then we know that the result of the
				// GEP will have the same offset into the same DSNode
				// as the indexed pointer.
				if (!NodeH.isNull() 
						&& NodeH.getNode().isNodeCompletelyFolded()) {
					return NodeH;
				}
				
				Type BasePtrTy = CType.getInstance().pointerize(BaseTy);
				Type ElemTy = BasePtrTy.toPointer().getType();
				
				assert BasePtrTy.isPointer() : "Error type";
				if (BaseTy.resolve().isPointer()) {
					NodeH = load(NodeH, ElemTy);
				}
				
				ensureSafeIndexAccess(NodeH, ElemTy);
				
				// Check the offset
				if (!NodeH.isNull()) {
					NodeH.getNode().checkOffsetFoldIfNeeded(NodeH.getOffset());
				}
				
				// NodeH is now the pointer we want to GEP to be...
				return NodeH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitAdditiveExpression(GNode node) {				
				Type lhsTy = CType.getType(node.getNode(0));
				lhsTy = CType.getInstance().pointerize(lhsTy);
				Type rhsTy = CType.getType(node.getNode(2));
				rhsTy = CType.getInstance().pointerize(rhsTy);
				
				if (lhsTy.isPointer()) {
					return getElemPtr(node.getNode(0), node.getNode(2), node.getString(1));
				} else {
					assert rhsTy.isPointer();
					return getElemPtr(node.getNode(2), node.getNode(0), node.getString(1));
				}
			}
		}
		
		private class RvalVisitor extends Visitor {
			private DSNodeHandle encode(Node node) {
				return (DSNodeHandle) dispatch(node);
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
			public DSNodeHandle visitShiftExpression(GNode node) {
				DSNodeHandle CurNH = new DSNodeHandle();
				Type Ty = CType.getType(node);
				if (Ty.resolve().isPointer()) {
					CurNH = getValueDest(CurNH, Ty);
				}
				
				Type lhsTy = CType.getType(node.getNode(0));
				DSNodeHandle lhsNH = encode(node.getNode(0));
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				Type rhsTy = CType.getType(node.getNode(2));
				DSNodeHandle rhsNH = encode(node.getNode(2));
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				if (CurNH.getNode() != null) {
					CurNH.getNode().setUnknownMarker();
				}
				
				return CurNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitTypeName(GNode node) {
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitSizeofExpression(GNode node) {
				encode(node.getNode(0));
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitUnaryMinusExpression(GNode node) {
				DSNodeHandle NH = encode(node.getNode(0));
				if (NH != null && NH.getNode() != null) {
					NH.getNode().setUnknownMarker();
				}
				
				return NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitUnaryPlusExpression(GNode node) {
				DSNodeHandle NH = encode(node.getNode(0));
				if (NH != null && NH.getNode() != null) {
					NH.getNode().setUnknownMarker();
				}
				
				return NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitIndirectComponentSelection(GNode node) {
				DSNodeHandle NH = lvalVisitor.encode(node);
				Type Ty = CType.getType(node);
				return Ty.resolve().isPointer() ? load(NH, Ty) : NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitDirectComponentSelection(GNode node) {
				DSNodeHandle NH = lvalVisitor.encode(node);
				Type Ty = CType.getType(node);
				return Ty.resolve().isPointer() ? load(NH, Ty) : NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitSubscriptExpression(GNode node) {
				DSNodeHandle NH = lvalVisitor.encode(node);
				Type Ty = CType.getType(node);
				return Ty.resolve().isPointer() ? load(NH, Ty) : NH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitRelationalExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(2));
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitMultiplicativeExpression(GNode node) {
				DSNodeHandle CurNH = new DSNodeHandle();
				Type Ty = CType.getType(node);
				if (Ty.resolve().isPointer()) {
					CurNH = getValueDest(CurNH, Ty);
				}
				
				Type lhsTy = CType.getType(node.getNode(0));
				DSNodeHandle lhsNH = encode(node.getNode(0));
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				Type rhsTy = CType.getType(node.getNode(2));
				DSNodeHandle rhsNH = encode(node.getNode(2));
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				if (CurNH.getNode() != null) {
					CurNH.getNode().setUnknownMarker();
				}
				
				return CurNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitLogicalNegationExpression(GNode node) {
				encode(node.getNode(0));
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitEqualityExpression(GNode node) {
				DSNodeHandle CurNH = new DSNodeHandle();
				
				Type lhsTy = CType.getType(node.getNode(0));
				lhsTy = CType.getInstance().pointerize(lhsTy);
				DSNodeHandle lhsNH = encode(node.getNode(0));
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				Type rhsTy = CType.getType(node.getNode(2));
				rhsTy = CType.getInstance().pointerize(rhsTy);
				DSNodeHandle rhsNH = encode(node.getNode(2));
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitPrimaryIdentifier(GNode node) {
				Type Ty = CType.getType(node);
				if (Ty.isEnumerator()) {
					assert Ty.hasConstant() : "EnumeratorT must have Constant";
					return null;
				}
				
				DSNodeHandle leftNH = lvalVisitor.encode(node);
				return Ty.resolve().isPointer() ? load(leftNH, Ty) : leftNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitCastExpression(GNode node) {
				Node fromNode = node.getNode(1);
				Type fromTy = CType.getType(fromNode);
				Type toTy = CType.getType(node);
				DSNodeHandle fromNH = encode(fromNode);
				return cast(fromTy, toTy, fromNH);
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitIndirectionExpression(GNode node) {
				DSNodeHandle PtrNH = lvalVisitor.encode(node);
				Type Ty = CType.getType(node);
				return Ty.resolve().isPointer() ? load(PtrNH, Ty) : PtrNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitIntegerConstant(GNode node) {
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitFloatingConstant(GNode node) { 
				return null; 
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitCharacterConstant(GNode node) {
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitStringConstant(GNode node) {
				return null;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitConditionalExpression(GNode node) {
				encode(node.getNode(0));
				
				DSNodeHandle CurNH = new DSNodeHandle();
				Type Ty = CType.getType(node);
				if (Ty.resolve().isPointer()) {
					CurNH = getValueDest(CurNH, Ty);
				}
				
				Type lhsTy = CType.getType(node.getNode(1));
				lhsTy = CType.getInstance().pointerize(lhsTy);
				DSNodeHandle lhsNH = encode(node.getNode(1));
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				Type rhsTy = CType.getType(node.getNode(2));
				rhsTy = CType.getInstance().pointerize(rhsTy);
				DSNodeHandle rhsNH = encode(node.getNode(2));
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				return CurNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitAddressExpression(GNode node) {
				return lvalVisitor.encode(node.getNode(0));
			}
			
			/**
			 * For all other instruction types, if we have any arguments
			 * that are of pointer type, make them have unknown composition bits, and merge
			 * the nodes together.
			 */
			@SuppressWarnings("unused")
			public DSNodeHandle visitAdditiveExpression(GNode node) {
				Type lhsTy = CType.getType(node.getNode(0));
				lhsTy = CType.getInstance().pointerize(lhsTy);
				Type rhsTy = CType.getType(node.getNode(2));
				rhsTy = CType.getInstance().pointerize(rhsTy);
				DSNodeHandle lhsNH = encode(node.getNode(0));
				DSNodeHandle rhsNH = encode(node.getNode(2));
				
				if (lhsTy.isPointer() && rhsTy.isInteger() ||
						rhsTy.isPointer() && lhsTy.isInteger()) {
					DSNodeHandle resNH = lvalVisitor.encode(node);
					return load(resNH, CType.getType(node));
				}
				
				DSNodeHandle CurNH = new DSNodeHandle();
				Type Ty = CType.getType(node);
				if (Ty.resolve().isPointer()) {
					CurNH = getValueDest(CurNH, Ty);
				}
				
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				if (CurNH.getNode() != null) {
					CurNH.getNode().setUnknownMarker();
				}
				
				return CurNH;
			}
			
			@SuppressWarnings("unused")
			public DSNodeHandle visitAssignmentExpression(GNode node) {
				DSNodeHandle CurNH = new DSNodeHandle();
				Type Ty = CType.getType(node);
				if (Ty.resolve().isPointer()) {
					CurNH = getValueDest(CurNH, Ty);
				}
				
				Type lhsTy = CType.getType(node.getNode(0));
				DSNodeHandle lhsNH = encode(node.getNode(0));
				if (lhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(lhsNH, lhsTy));
				}
				
				Type rhsTy = CType.getType(node.getNode(2));
				DSNodeHandle rhsNH = encode(node.getNode(2));
				if (rhsTy.resolve().isPointer()) {
					CurNH.mergeWith(getValueDest(rhsNH, rhsTy));
				}
				
				return CurNH;
			}
			
			@SuppressWarnings("unused")
		    public DSNodeHandle visitBitwiseAndExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				return null;
			}
		    
			@SuppressWarnings("unused")
		    public DSNodeHandle visitBitwiseOrExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				return null;
			}

			@SuppressWarnings("unused")
		    public DSNodeHandle visitBitwiseXorExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				return null;
			}
			
			@SuppressWarnings("unused")
		    public DSNodeHandle visitLogicAndExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				return null;
			}
		    
			@SuppressWarnings("unused")
		    public DSNodeHandle visitLogicalOrExpression(GNode node) {
				encode(node.getNode(0));
				encode(node.getNode(1));
				return null;
			}
		}
		
		GraphBuilder(IRControlFlowGraph CFG, DSGraph g) {
			G = g;
			String FuncID = CFG.getName();
			IRVarInfo FuncVarInfo = SymbolTable.lookup(FuncID);
			FB = (Function) ValueManager.get(FuncID, FuncVarInfo.getXtcType());
			VAArray = null;
		
			IOUtils.debug().pln("[local] Building graph for function: " + FB.getName());
		
			// Create scalar nodes for all pointer arguments ...
			if (FB.getArguments() != null) {
				for (Value arg : FB.getArguments()) {
					if(arg.getType().resolve().isPointer()) {
						getValueDest(arg).getNode();
					}
				}
			}
			
			// Create an entry for the return, which tracks which functions are in
			// the graph
			g.getOrCreateReturnNodeFor(FB);
			
			// Create a node to handle information about variable arguments
			g.getOrCreateVANodeFor(FB);
			
			// Single pass over the function
			visit(CFG);
			
			// If there are any constant globals referenced in this function, merge
			// their initializers into the local graph from the globals graph.
			// This resolves indirect calls in some common cases.
			// Only merge info for nodes that already exists in the local pass
			// otherwise leaf functions could contain less collapsing than the globals graph
			if (!g.getScalarMap().getGlobalSet().isEmpty()) {
				ReachabilityCloner RC = new ReachabilityCloner(g, g.getGlobalsGraph(), 0, true);
				for(GlobalValue GV : g.getScalarMap().getGlobalSet()) {
					if(GV instanceof GlobalVariable) {
						if(GV.isConstant()) {
							IOUtils.debug().pln("Merging global " + GV);
							RC.merge(g.getNodeForValue(GV), g.getGlobalsGraph().getNodeForValue(GV));
						}
					}
				}
			}
			
			g.markIncompleteNodes(DSSupport.MarkIncompleteFlags.MarkFormalArgs.value());
			
			// Compute sources of external
			int EFlags = 0 | 
					DSSupport.ComputeExternalFlags.DontMarkFormalsExternal.value() |
					DSSupport.ComputeExternalFlags.ProcessCallSites.value();
			
			g.computeExternalFlags(EFlags);
			g.computeIntPtrFlags();
			
			// Remove any nodes made dead due to merging...
			g.removeDeadNodes(DSSupport.RemoveDeadNodesFlags.KeepUnreachableGlobals.value());
		}
		
		// GraphBuilder ctor for working on the globals graph
		GraphBuilder(DSGraph g) {
			G = g;
			FB = null;
			VAArray = null;
		}
		
		private DSGraph G;
		private Function FB;	// FB is null indicates global CFG
		
		private DSNode VAArray;
		
		private LvalVisitor lvalVisitor = new LvalVisitor();
		private RvalVisitor rvalVisitor = new RvalVisitor();
		
		private void visit(IRControlFlowGraph CFG) {
			SymbolTable.enterScope(CFG);
			
			Collection<IRBasicBlock> BBs = Lists.reverse(CFG.topologicalSeq(CFG.getEntry()));
			for(IRBasicBlock BB : BBs) {
				for(IRStatement stmt : BB.getStatements())	visit(stmt);
				
				for(IREdge<?> outgoing : CFG.getOutgoingEdges(BB)) {
					if(null != outgoing.getGuard()) {
						Node op = outgoing.getGuard().getSourceNode();
						rvalVisitor.encode(op);
					}
				}
			}
		}

		private void visit(IRStatement stmt) {
			switch (stmt.getType()) {
			case DECLARE:
			case DECLARE_ARRAY: {
				Node lhs = stmt.getOperand(0).getSourceNode();
			  	DSNodeHandle lhsNH = lvalVisitor.encode(lhs);
			  	Type lhsTy = CType.getType(lhs);
			  	getValueDest(lhsNH, lhsTy);
			  	break;
			}
			case ALLOCA:
			case CALLOC:
			case MALLOC: {
				Node lhs = stmt.getOperand(0).getSourceNode();
				Node rhs = stmt.getOperand(1).getSourceNode();
			  	DSNodeHandle lhsNH = lvalVisitor.encode(lhs);
			  	rvalVisitor.encode(rhs);
			  	Type lhsTy = CType.getType(lhs);
			  	getValueDest(lhsNH, lhsTy);
			  	break;
			}
			case FREE: {
				Node op = stmt.getOperand(0).getSourceNode();
				lvalVisitor.encode(op);
				break;
			}
			case ASSUME:
			case ASSERT: {
				Node op = stmt.getOperand(0).getSourceNode();
				rvalVisitor.encode(op);
				break;
			}
			case INIT:
			case ASSIGN: {
				visitAssignStmt(stmt); break;
			}
			case RETURN: {
				if(stmt.getOperands() != null && !stmt.getOperands().isEmpty()) {
					Node ret = stmt.getOperand(0).getSourceNode();
					DSNodeHandle retNH = lvalVisitor.encode(ret);
					Type retTy = CType.getType(ret);
					if (retTy.resolve().isPointer()) {
						G.getOrCreateReturnNodeFor(FB).mergeWith(getValueDest(retNH, retTy));
					}
				}
				break;
			}
			case CALL: {
				visitCallStmt(stmt);	break;
			}
			default:
				break;
			}
		}
		
		private void visitAssignStmt(IRStatement stmt) {
			Node lhs = stmt.getOperand(0).getSourceNode();
		    Node rhs = stmt.getOperand(1).getSourceNode();
		    
		    DSNodeHandle lhsNH = lvalVisitor.encode(lhs);
		    DSNodeHandle rhsNH = rvalVisitor.encode(rhs);
		    
		    Type lhsTy = CType.getType(lhs);
		    lhsTy = CType.getInstance().pointerize(lhsTy);
		    Type rhsTy = CType.getType(rhs);
		    if (!lhsTy.equals(rhsTy)) { // Incompatible type
		    	rhsNH = cast(rhsTy, lhsTy, rhsNH);
		    }
		    
		    DSNodeHandle Dest = getValueDest(lhsNH, lhsTy);
		    
		    if(Dest.isNull()) return;
		    
		    // Mark that the node is written to ...
		    Dest.getNode().setModifiedMarker();
		    
		    // Ensure a type-record exists
		    Dest.getNode().growSizeForType(lhsTy, Dest.getOffset());
		    
		    // Avoid adding edges from null, or processing non-"pointer" stores
		    if(lhsTy.resolve().isPointer()) {
		    	Dest.addEdgeTo(0, getValueDest(rhsNH, lhsTy));
		    }
		    
		    if (CType.isStructOrUnion(lhsTy)) {
		    	Dest.mergeWith(rhsNH);
		    }
		    
		    //TODO: TypeInferenceOptimize
		    
		    Dest.getNode().mergeTypeInfo(lhsTy, Dest.getOffset());
			return;
		}
		
		private void visitCallStmt(IRStatement stmt) {
			// Set up the return value...
			DSNodeHandle RetVal = new DSNodeHandle();
			Node srcNode = stmt.getSourceNode();
			Type retTy = CType.getType(srcNode);
			
			if (!retTy.resolve().isVoid()) {
				Node retNode = stmt.getOperand(1).getSourceNode();
				DSNodeHandle retNH = lvalVisitor.encode(retNode);
				if (retTy.resolve().isPointer()) {
					RetVal = getValueDest(retNH, retTy);
				}
			}
			
			Node funcNode = stmt.getOperand(0).getSourceNode();
			String funcName = CAnalyzer.toFunctionName(funcNode);
			if(ReservedFunction.MEMCOPY.equals(funcName)) {
				Node lhs = stmt.getOperand(2).getSourceNode();
				Node rhs = stmt.getOperand(3).getSourceNode();
				DSNodeHandle lhsNH = lvalVisitor.encode(lhs);
				DSNodeHandle rhsNH = lvalVisitor.encode(rhs);
				lhsNH.mergeWith(rhsNH);
				return;
			}
			
			Type funcTy = CType.getType(funcNode);
			Node funcId = CAnalyzer.getIdentifier((GNode) funcNode);
			DSNode CalleeNode = null;
			if (funcId == null || !CType.getType(funcId).resolve().isFunction()) {
				DSNodeHandle funcNH = rvalVisitor.encode(funcNode);
				CalleeNode =  funcNH.getNode();
				if (CalleeNode == null) {
					IOUtils.err().println("WARNING: Program is calling through a null pointer");
					return;
				}
			}
			
			// Get the type of function. Normalize the function to call
			// as a function pointer via pointerizing the function type
			funcTy = CType.getInstance().pointerize(funcTy);
			funcTy = funcTy.toPointer().getType();
			
			// Get the FunctionType for the called function
			int NumFixedArgs = funcTy.resolve().toFunction().getParameters().size();
			
			// Sanity check--this really, really shouldn't happen
			int StmtArgSize = stmt.getOperands().size() - 1;
			if (!funcTy.resolve().toFunction().getResult().isVoid()) StmtArgSize -= 1;
			
			//FIXME: function __bswap_32 with no var args but has too many arguments
//			if (!funcTy.resolve().toFunction().isVarArgs()) {
//				assert StmtArgSize == NumFixedArgs : 
//					"Too many arguments/incorrect function signature!";
//			}
			
			// Calculate the arguments vector...
			// Add all fixed pointer arguments, then merge the rest together
			List<DSNodeHandle> Args = Lists.newArrayListWithCapacity(StmtArgSize);
			DSNodeHandle VarArgNH = new DSNodeHandle();
			Iterator<IRExpression> ArgItr = stmt.getOperands().iterator();
			ArgItr.next();
			if (!funcTy.resolve().toFunction().getResult().isVoid())	ArgItr.next();
			
			while (ArgItr.hasNext()) {
				Node ArgNode = ArgItr.next().getSourceNode();
				Type ArgTy = CType.getType(ArgNode);
				DSNodeHandle ArgNH = rvalVisitor.encode(ArgNode);
				if (ArgTy.resolve().isPointer()) {
					ArgNH = getValueDest(ArgNH, ArgTy);
				}
				if (NumFixedArgs > 0) {
					Args.add(ArgNH); --NumFixedArgs;
				} else {
					VarArgNH.mergeWith(ArgNH);
				}
			}
			
			// Add a new function call entry...
			DSCallSite CS;
			if (CalleeNode != null) {
				CS = new DSCallSite(srcNode, CalleeNode, RetVal, VarArgNH, Args);
			} else {
				Function FB = (Function) ValueManager.getOrCreate(
						SymbolTable.lookup(funcId.getString(0)));
				CS = new DSCallSite(srcNode, FB, RetVal, VarArgNH, Args);
			}
			G.getFunctionCalls().add(CS);
			
		}
		
		/** 
		 * createNode  - Create a new DSNode, ensuring that it is properly added to
		 * the graph.
		 */
		private DSNode createNode() {
			DSNode ret = new DSNodeImpl(G);
			assert ret.getParentGraph() != null : "No parent?";
			return ret;
		}
		
		/** getValueDest - Return the DSNode that the actual NH points to. */
		private DSNodeHandle getValueDest(Value V) {
			DSNodeHandle NH = G.getNodeForValue(V);
			// Already have a node?  Just return it...
			if (!NH.isNull())	return NH;
			
			Type Ty = V.getType();
			return getValueDest(NH, Ty);
		}
		
		private DSNodeHandle getValueDest(DSNodeHandle NH, Type Ty) {
			Preconditions.checkNotNull(NH);
			// Already have a node?  Just return it...
			if (!NH.isNull())	return NH;
			
			// We need to create a new node to point to.
			// Check first for constant expressions that must be traversed to
			// extract the actual value.
			DSNode N = null;
			if (! Ty.hasShape() || ! Ty.getShape().isStatic()) {
				N = createNode();
			} else {
				StaticReference Ref = (StaticReference) Ty.getShape();
				if (Ty.resolve().isFunction()) {
					String funcName = Ref.getName();
					Value Func = ValueManager.get(funcName, Ty);
					// Create a new global node for this function.
				    N = createNode();
				    assert(Func instanceof Function);
					N.addFunction((Function) Func);
					if (Ty.hasAttribute(Constants.ATT_STORAGE_EXTERN)) {
						N.setExternalMarker();
					}
				} else if (Ref.isVariable()) {
					String varName = Ref.getName();
					Value V = ValueManager.get(varName, Ty);
					N = createNode();
					assert(V instanceof GlobalVariable);
					N.addGlobal((GlobalVariable) V);
					if (Ty.hasAttribute(Constants.ATT_STORAGE_EXTERN)) {
						N.setExternalMarker();
					}
				}
			}
			
			
			NH.setTo(N, 0);
			return NH;
		}
		
		/**
		 * getLink - This method is used to return the specified link in the
		 * specified node if one exists.  If a link does not already exist (it's
		 * null), then we create a new node, link it, then return it.
		 */
		private DSNodeHandle getLink(final DSNodeHandle NH, int LinkNo) {
			DSNodeHandle Link = NH.getLink(LinkNo);
			if(Link.isNull()) {
				// If the link hasn't been created yet, make and return a new shadow node
				Link.setTo(createNode(), 0);
			}
			return Link;
		}
		
		private void mergeFunction(Function F) {
			getValueDest(F);
		}
	}
}
