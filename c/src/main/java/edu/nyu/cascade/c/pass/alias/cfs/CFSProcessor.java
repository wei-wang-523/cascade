package edu.nyu.cascade.c.pass.alias.cfs;

import java.util.Collection;
import java.util.Map;
import com.google.common.collect.Range;
import xtc.tree.Node;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class CFSProcessor implements IRAliasAnalyzer<Cell> {

	@Override
  public String displaySnapShot() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public void buildSnapShot() {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public Cell getPtsToRep(Cell rep) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public long getRepWidth(Cell rep) {
	  // TODO Auto-generated method stub
	  return 0;
  }

	@Override
  public String getRepId(Cell rep) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Cell getRep(Node node) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Collection<Cell> getFillInReps(Cell rep, long length) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public void addRegion(Expression region, Node ptrNode) {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public void addVar(Expression lval, Node lvalNode) {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public Map<Range<Long>, Cell> getStructMap(Cell rep, long length) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Collection<IRVar> getEquivFuncVars(Node funcNode) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public void reset() {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public boolean isAccessTypeSafe(Cell rep) {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
	public Cell getStackRep(Node node) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Cell getPtsToRep(Node node) {
		// TODO Auto-generated method stub
		return null;
	}
	
}
//public class CFSProcessor implements PreProcessor<Cell> {	
//  private final CellManager cellManager;
//  private final SymbolTable symbolTable;
//  private final CellEncoder ecrEncoder;
//  private CellChecker ecrChecker;
//  private ImmutableMap<Cell, Collection<IRVar>> snapShot;
//  private IRControlFlowGraph currentCFG;
//  
//  private static final long defaultWidth = CType.getInstance().getWidth(CType.getUnitType());
//  private static final long ptrWidth = CType.getInstance().getWidth(new PointerT(CType.getVoidType()));
//  
//  private CFSProcessor (SymbolTable symbolTable) {
//    cellManager = new CellManager();
//    ecrEncoder = CellEncoder.create(symbolTable, cellManager); 
//    this.symbolTable = symbolTable;
//  }
//  
//  public static CFSProcessor create(SymbolTable symbolTable) {
//    return new CFSProcessor(symbolTable);
//  }
//  
//	@Override
//	public void analysis(IRControlFlowGraph cfg) {
//		symbolTable.enterScope(cfg);
//		
//		currentCFG = cfg;
//		
//		if(!Identifiers.GLOBAL_CFG.equals(cfg.getName())) {
//			GNode declarator = cfg.getSourceNode().getGeneric(2);
//			GNode identifier = CAnalyzer.getDeclaredId(declarator);
//			Type funcXtcType = symbolTable.lookupType(identifier.getString(0));
//			
//			if(!funcXtcType.resolve().toFunction().getParameters().isEmpty()) {	  		
//	  		GNode parameters = CAnalyzer.getFunctionDeclarator(declarator).getGeneric(1);
//				parameters = parameters.getGeneric(0);
//				
//				List<Cell> paramCells = Lists.newArrayList();
//	      for (Object o : parameters) {
//	      	GNode paramNode = ((Node) o).getGeneric(1);
//	      	assert (null != paramNode);
//	      	Node paramIdNode = CAnalyzer.getDeclaredId(paramNode);
//	        Cell paramCell = ecrEncoder.toRval(paramIdNode);
//	        paramCells.add(paramCell);
//	      }
//	     
//				Cell funcCell = ecrEncoder.toRval(identifier);
//	  		FuncCell lamType = uf.getType(uf.getFunc(funcCell)).asFunction();
//	  		List<Cell> lamCells = lamType.getParams();
//	  		assert lamCells.size() >= paramCells.size();
//	  		
//	      for(int i = 0; i < paramCells.size(); i++) {
//	      	Cell lamCell = lamCells.get(i);
//	      	Cell paramCell = paramCells.get(i);
//	      	uf.cjoin(lamCell, paramCell);
//	      }
//			}
//		}
//		
//		final Collection<IRBasicBlock> topologicSeq = Lists.reverse(cfg.topologicalSeq(cfg.getEntry()));
//		
//		for(IRBasicBlock block : topologicSeq) {			
//			for(IRStatement stmt : block.getStatements()) analysis(stmt);
//			
//			for(IREdge<?> outgoing : cfg.getOutgoingEdges(block)) {
//				if(null != outgoing.getGuard()) 
//					ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
//			}
//		}
//	}
//	
//	private void analysis(IRStatement stmt) {
//	  	IOUtils.debug().pln("Preprocess: " + stmt.getLocation() + ": " + stmt);
//		  switch (stmt.getType()) {
//		  case DECLARE:
//		  case DECLARE_VAR_ARRAY: {
//		  	Node lhs = stmt.getOperand(0).getSourceNode();
//		  	ecrEncoder.toLval(lhs);
//		  	break;
//		  }
//		  case INIT: {
//		  	Node lhsNode = stmt.getOperand(0).getSourceNode();
//		    Node rhsNode = stmt.getOperand(1).getSourceNode();
//				
//		    Cell lhsCell = ecrEncoder.toRval(lhsNode);
//		    Cell rhsCell = ecrEncoder.toRval(rhsNode);
//		    
//		    uf.ccjoin(rhsCell, lhsCell);
//			break;
//		  }
//		  case RETURN: {
//		  	String functionName = currentCFG.getName();
//		    Cell funcCell = ecrEncoder.getFunctionCell(functionName);
//	  		FuncCell funcType = uf.getType(uf.getFunc(uf.getLoc(funcCell))).asFunction();
//		    Cell retCell = funcType.getRet();
//		    
//		  	Node srcNode = stmt.getOperand(0).getSourceNode();
//		  	Cell srcCell = ecrEncoder.toRval(srcNode);
//		  	
//		  	Type resType = symbolTable.lookupType(functionName).resolve().toFunction().getResult();
//		  	simpleAssign(resType, retCell, srcCell);
//		  	break;
//		  }
//		  case ASSIGN: {
//		    Node lhsNode = stmt.getOperand(0).getSourceNode();
//		    Node rhsNode = stmt.getOperand(1).getSourceNode();
//		    
//		    Type lhsType = CType.getType(lhsNode);
//		    Type rhsType = CType.getType(rhsNode);
//	
//		    Cell lhsCell = ecrEncoder.toRval(lhsNode);
//		    
//		    /* Resolve the syntax sugar of assign function to a function pointer */
//		    boolean isFuncType = rhsType.resolve().isFunction();
//		    Cell rhsCell = isFuncType ? ecrEncoder.toLval(rhsNode) : ecrEncoder.toRval(rhsNode);
//		    
//		    simpleAssign(lhsType, lhsCell, rhsCell);
//		    break;
//		  }
//		  case ALLOCA:
//		  case CALLOC:
//		  case MALLOC: {
//		    Node lhs = stmt.getOperand(0).getSourceNode();
//		    Type lhsType = CType.getType(lhs);
//		    long rangeSize = CType.getInstance().getSize(lhsType);
//		    Cell lhsCell = ecrEncoder.toRval(lhs);
//		    
//		    heapAssign(rangeSize, lhsCell);
//		    break;
//		  }
//		  case CALL: {			  
//		  	Node funcNode = stmt.getOperand(0).getSourceNode();
//		  	Cell funcCell = ecrEncoder.toRval(funcNode);
//		  	assert (null != funcCell);
//		  	
//		  	Type funcXtcType = CType.getType(funcNode).resolve();
//		  	if(funcXtcType.isPointer()) {
//		  		funcCell = uf.getLoc(funcCell);
//		  		funcXtcType = funcXtcType.toPointer().getType();
//		  	}
//				
//		  	/* For the function pointer parameters declared but not yet assigned */
//		  	if(uf.getType(funcCell).isBottom()) {
//					IOUtils.err().println("WARNING: get Loc of " + funcCell);
//					Size size = Size.createForType(CType.getInstance().pointerize(funcXtcType));
//					uf.expand(funcCell, size);
//				}
//		  	
//		  	Cell lamCell = uf.getFunc(funcCell);
//		  	
//		  	if(uf.getType(lamCell).isBottom()) {
//		  		Cell lamType = ecrEncoder.getLamdaType(funcXtcType);
//		  		uf.setType(lamCell, lamType);
//		  	}
//		  	
//		  	FuncCell lamType = uf.getType(lamCell).asFunction();
//		  	
//		  	if(funcXtcType.toFunction().getResult().isVoid()) {
//		  		Iterator<Cell> paramCellItr = lamType.getParams().iterator();
//		  		for(int i = 1; i < stmt.getOperands().size(); i++) {
//		  			Node srcNode = stmt.getOperand(i).getSourceNode();
//		  			
//		  			/* Resolve the syntax sugar of assign function to a function pointer */
//		  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
//		  			Cell argCell = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
//		  			
//		  			if(paramCellItr.hasNext()) {
//			  			Cell paramCell = paramCellItr.next();
//			  			Cell argType = uf.getType(argCell);
//			  			paramRetAssign(argType.getSize(), paramCell, argCell);
//		  			} else {
//		  				lamType.addParamCell(argCell);
//		  			}
//		  		}
//		  	} 
//		  	
//		  	else {
//		  		Node retNode = stmt.getOperand(1).getSourceNode();
//		  		Cell retCell = ecrEncoder.toRval(retNode);
//		  		Cell lamRetCell = lamType.getRet();
//		  		Cell lamRetType = uf.getType(lamRetCell);
//		  		paramRetAssign(lamRetType.getSize(), retCell, lamRetCell);
//		  		
//		  		Iterator<Cell> paramCellItr = lamType.getParams().iterator();
//		  		
//		  		int i;
//		  		for(i = 2; i < stmt.getOperands().size(); i++) {
//		  			Node srcNode = stmt.getOperand(i).getSourceNode();
//		  			
//		  			/* Resolve the syntax sugar of assign function to a function pointer */
//		  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
//		  			Cell argCell = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
//		  			
//		  			if(!paramCellItr.hasNext()) break;
//		  			
//		  			Cell paramCell = paramCellItr.next();
//		  			Cell argType = uf.getType(argCell);
//		  			paramRetAssign(argType.getSize(), paramCell, argCell);
//		  		}
//		  		
//		  		for(; i < stmt.getOperands().size(); i++) {
//		  			Node srcNode = stmt.getOperand(i).getSourceNode();
//		  			/* Resolve the syntax sugar of assign function to a function pointer */
//		  			Cell argCell = CType.getType(srcNode).resolve().isFunction() ?
//		  					ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
//		  			lamType.addParamCell(argCell);
//		  		}
//		  	}
//	  		break;
//		  }
//		  case ASSERT:
//		  case ASSUME: {
//		  	Node src = stmt.getOperand(0).getSourceNode();
//		  	ecrEncoder.toRval(src);
//		  	break;
//		  }
//		  default:
//		  }
//	}
//	
//	@Override
//	public void initChecker() {
//		ecrChecker = CellChecker.create(cellManager, symbolTable, ecrEncoder);
//	}
//
//	@Override
//  public void reset() {
//		cellManager.reset();
//  }
//
//	@Override
//	public Cell getPointsToLoc(Cell base) {
//    if(cellManager.isBottom(base))
//    	IOUtils.err().println("WARNING: get points-to Loc Cell of bottom " + base);
//    return uf.findRoot(cellManager.getPointsCell(base));
//	}
//	
//	@Override
//	public Map<Range<Long>, Cell> getStructMap(Cell structCell) {
//		Cell structType = uf.getType(structCell);
//		if(!structType.isStruct()) return Collections.emptyMap();
//			
//		return structType.asStruct().getFieldMap();
//	}
//
//	/**
//	 * Return <code>void</code> type is <code>rep</code> is 
//	 * with the bottom type (not yet allocated)
//	 */
//	@Override
//	public long getRepTypeWidth(Cell cell) {
//		if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) {
//			return defaultWidth;
//		}
//		
//		switch(cell.getKind()) {
//			case SCALAR: {
//				// TODO: top cell should return defaultWidth
//				return cell.getSize();
//			}
//			case STRUCT:
//				return ptrWidth;
//			default:
//				return defaultWidth;
//		}
//	}
//	
//	@Override
//	public void buildSnapShot() {
//	  snapShot = uf.snapshot();
//	}
//	
//	@Override
//	public String getRepId(Cell ecr) {
//		return String.valueOf(ecr.getId());
//	}
//	
//	@Override
//	public Cell getRep(Node node) {
//		return uf.findRoot(ecrEncoder.toRval(node));
//	}
//
//	@Override
//	public void addAllocRegion(Expression region, Node ptrNode) {
//		if(!IOUtils.debugEnabled()) return;
//		
//		/* The freshRegionVar should have the same scope and type as place holder */
//		ecrEncoder.createRegionVar(region, ptrNode);
//		IOUtils.debug().pln(displaySnapShot());
//	}
//
//	@Override
//	public void addStackVar(Expression lval, Node lvalNode) {
//		if(!IOUtils.debugEnabled()) return;
//		
//		ecrEncoder.addStackVar(lval, lvalNode);
//		IOUtils.debug().pln(displaySnapShot());
//	}
//	
//	@Override
//	public String displaySnapShot() {
//		buildSnapShot();
//		
//	  StringBuilder sb = new StringBuilder().append('\n')
//	  		.append("The result of field-sensitive Steensgaard analysis:\n");
//	  
//	  for(Entry<Cell, Collection<IRVar>> entry : snapShot.entrySet()) {
//	  	Cell ecr = entry.getKey();
//	  	
//	  	Collection<IRVar> vars = entry.getValue();
//	  	if(!vars.isEmpty()) {
//	  		sb.append("Partition ").append(ecr.getId()).append(": ");
//	  		sb.append(uf.getType(ecr)).append("\n { ");
//	  		
//	  		for(IRVar var : vars) sb.append(var.getName()).append(' ');
//	  		sb.append("}\n");
//	  	}
//	  }
//	  return sb.toString();
//	}
//
//	@Override
//	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
//		Cell rep = ecrChecker.toRval(funcNode);
//		Type funcType = CType.getType(funcNode).resolve();
//		if(funcType.isPointer()) rep = getPointsToLoc(rep);
//		Cell funcRep = uf.getFunc(rep);
//	  return uf.getEquivClass(funcRep);
//	}
//	
//	@Override
//	public Collection<Cell> getFillInReps(Cell rep) {
//		Collection<Cell> reps = Sets.newLinkedHashSet();
//		collectFieldReps(reps, rep);
//	  return reps;
//	}
//	
//	@Override
//	public boolean isAccessTypeSafe(Cell rep) {
//		Cell type = uf.getType(rep);
//		
//		switch(type.getKind()) {
//		case BOTTOM:	return false;
//		case STRUCT:	return true;
//		default: {
//			Size size = type.getSize();
//			if(!size.isNumber()) return false;
//			
//			long value = size.getValue();
//			if(value == 0)	return false; // array type without length (stdlib.h)
//			
//			return true;
//		}
//		}
//	}
//	
//	private void collectFieldReps(Collection<Cell> reps, Cell rep) {
//		if(reps.contains(rep)) return;
//		
//		reps.add(rep); 
//		Cell repType = uf.getType(rep);
//		
//		if(repType.isStruct()) {
//			for(Cell elem : repType.asStruct().getFieldMap().values()) {
//				Cell elemRep = uf.findRoot(uf.getLoc(elem));
//				collectFieldReps(reps, elemRep);
//			}
//		}
//	}
//
//	private void heapAssign(long size, Cell lhs) {
//		Size rangeSize = Size.valueOf(size);
//		
//		Cell lhsType = uf.getType(lhs);
//		Size lhsSize = lhsType.getSize();
//		if(!Size.isLessThan(rangeSize, lhsSize)) {
//			uf.expand(lhs, rangeSize);
//		}
//	  
//		Cell lhsLoc = uf.getLoc(lhs);
//		Cell lhsLocType = uf.getType(lhsLoc);
//		if(lhsLocType.isBottom()) {					
//			Cell blankType = Cell.blank(
//					Size.getBot());
//			uf.setType(lhsLoc, blankType);
//		}
//	}
//
//	private void simpleAssign(Type targetType, Cell lhs, Cell rhs) {
//	  cellManager.ccjoin(rhs, lhs);
//	}
//	
//	private void paramRetAssign(Cell lhs, Cell rhs) {
//	  cellManager.ccjoin(rhs, lhs);
//	}
//}