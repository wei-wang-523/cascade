package edu.nyu.cascade.c.preprocessor.steensfs;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Range;
import com.google.common.collect.Sets;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.PointerT;
import xtc.type.Type;
import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class SteensgaardFS implements PreProcessor<ECR> {	
  private final UnionFindECR uf;
  private final SymbolTable symbolTable;
  private final ECREncoder ecrEncoder;
  private ImmutableMap<ECR, Collection<IRVar>> snapShot;
  private IRControlFlowGraph currentCFG;
  
  private SteensgaardFS (SymbolTable symbolTable) {
    uf = UnionFindECR.create();
    ecrEncoder = ECREncoder.create(uf, symbolTable); 
    this.symbolTable = symbolTable;
  }
  
  public static SteensgaardFS create(SymbolTable symbolTable) {
    return new SteensgaardFS(symbolTable);
  }
  
	@Override
	public void analysis(IRControlFlowGraph cfg) {
		symbolTable.enterScope(cfg);
		
		currentCFG = cfg;
		
		if(!Identifiers.GLOBAL_CFG.equals(cfg.getName())) {
			GNode declarator = cfg.getSourceNode().getGeneric(2);
			GNode identifier = CAnalyzer.getDeclaredId(declarator);
			Type funcXtcType = symbolTable.lookupType(identifier.getString(0));
			
			if(!funcXtcType.resolve().toFunction().getParameters().isEmpty()) {	  		
	  		GNode parameters = CAnalyzer.getFunctionDeclarator(declarator).getGeneric(1);
				parameters = parameters.getGeneric(0);
				
				List<ECR> paramECRs = Lists.newArrayList();
	      for (Object o : parameters) {
	      	GNode paramNode = ((Node) o).getGeneric(1);
	      	assert (null != paramNode);
	      	Node paramIdNode = CAnalyzer.getDeclaredId(paramNode);
	        ECR paramECR = ecrEncoder.toRval(paramIdNode);
	        paramECRs.add(paramECR);
	      }
	     
				ECR funcECR = ecrEncoder.toRval(identifier);
	  		LambdaType lamType = uf.getType(uf.getFunc(funcECR)).asLambda();
	  		List<ECR> lamECRs = lamType.getParams();
	  		assert lamECRs.size() >= paramECRs.size();
	  		
	      for(int i = 0; i < paramECRs.size(); i++) {
	      	ECR lamECR = lamECRs.get(i);
	      	ECR paramECR = paramECRs.get(i);
	      	uf.cjoin(lamECR, paramECR);
	      }
			}
		}
		
		final Collection<IRBasicBlock> topologicSeq = Lists.reverse(cfg.topologicalSeq(cfg.getEntry()));
		
		for(IRBasicBlock block : topologicSeq) {			
			for(IRStatement stmt : block.getStatements()) analysis(stmt);
			
			for(IREdge<?> outgoing : cfg.getOutgoingEdges(block)) {
				if(null != outgoing.getGuard()) 
					ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
			}
		}
	}

  private void analysis(IRStatement stmt) {
  	IOUtils.debug().pln("Preprocess: " + stmt.getLocation() + ": " + stmt);
	  switch (stmt.getType()) {
	  case DECLARE:
	  case DECLARE_VAR_ARRAY: {
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.toLval(lhs);
	  	break;
	  }
	  case INIT: {
	  	Node lhsNode = stmt.getOperand(0).getSourceNode();
	    Node rhsNode = stmt.getOperand(1).getSourceNode();
	    
	    ECR lhsECR = ecrEncoder.toRval(lhsNode);
	    ECR rhsECR = ecrEncoder.toRval(rhsNode);
	    
			Type lhsType = CType.getType(lhsNode);
	    simpleAssign(lhsType, lhsECR, rhsECR);
			break;
	  }
	  case RETURN: {
	  	String functionName = currentCFG.getName();
	    ECR funcECR = ecrEncoder.getFunctionECR(functionName);
  		LambdaType funcType = uf.getType(uf.getFunc(uf.getLoc(funcECR))).asLambda();
	    ECR retECR = funcType.getRet();
	    
	  	Node srcNode = stmt.getOperand(0).getSourceNode();
	  	ECR srcECR = ecrEncoder.toRval(srcNode);
	  	
	  	Type resType = symbolTable.lookupType(functionName).resolve().toFunction().getResult();
	  	simpleAssign(resType, retECR, srcECR);
	  	break;
	  }
	  case ASSIGN: {
	    Node lhsNode = stmt.getOperand(0).getSourceNode();
	    Node rhsNode = stmt.getOperand(1).getSourceNode();
	    
	    Type lhsType = CType.getType(lhsNode);
	    Type rhsType = CType.getType(rhsNode);

	    ECR lhsECR = ecrEncoder.toRval(lhsNode);
	    
	    /* Resolve the syntax sugar of assign function to a function pointer */
	    boolean isFuncType = rhsType.resolve().isFunction();
	    ECR rhsECR = isFuncType ? ecrEncoder.toLval(rhsNode) : ecrEncoder.toRval(rhsNode);
	    
	    simpleAssign(lhsType, lhsECR, rhsECR);
	    break;
	  }
	  case ALLOCA:
	  case CALLOC:
	  case MALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Type lhsType = CType.getType(lhs);
	    long rangeSize = CType.getInstance().getSize(lhsType);
	    ECR lhsECR = ecrEncoder.toRval(lhs);
	    
	    heapAssign(rangeSize, lhsECR);
	    break;
	  }
	  case CALL: {
//	  	Node funcNode = stmt.getOperand(0).getSourceNode();
//		  String funcName = funcNode.getString(0);
//		  if(funcName.equals(ReservedFunction.MEMSET)) {
//		  	Node src = stmt.getOperand(1).getSourceNode();
//		  	ECR srcECR = ecrEncoder.encodeECR(src);
//		  	ECR locECR = uf.getLoc(srcECR);
//				uf.collapse(locECR);
//		  	break;
//		  }
//		  
//		  if(funcName.equals(ReservedFunction.MEMCOPY)) {
//		  	Node dest = stmt.getOperand(1).getSourceNode();
//		  	Node src = stmt.getOperand(2).getSourceNode();
//		  	ECR srcECR = ecrEncoder.encodeECR(src);
//		  	ECR destECR = ecrEncoder.encodeECR(dest);
//		  	ECR locSrcECR = uf.getLoc(srcECR);
//		  	ECR locDestECR = uf.getLoc(destECR);
//		  	uf.collapse(locSrcECR);
//		  	uf.collapse(locDestECR);
//		  	break;
//		  }
		  
	  	Node funcNode = stmt.getOperand(0).getSourceNode();
	  	ECR funcECR = ecrEncoder.toRval(funcNode);
	  	assert (null != funcECR);
	  	
	  	Type funcXtcType = CType.getType(funcNode).resolve();
	  	if(funcXtcType.isPointer()) {
	  		funcECR = uf.getLoc(funcECR);
	  		funcXtcType = funcXtcType.toPointer().getType();
	  	}
			
	  	/* For the function pointer parameters declared but not yet assigned */
	  	if(uf.getType(funcECR).isBottom()) {
				IOUtils.err().println("WARNING: get Loc of " + funcECR);
				Size size = Size.createForType(CType.getInstance().pointerize(funcXtcType));
				uf.promote(funcECR, size);
			}
	  	
	  	ECR lamECR = uf.getFunc(funcECR);
	  	
	  	if(uf.getType(lamECR).isBottom()) {
	  		ValueType lamType = ecrEncoder.getLamdaType(funcXtcType);
	  		uf.setType(lamECR, lamType);
	  	}
	  	
	  	LambdaType lamType = uf.getType(lamECR).asLambda();
	  	
	  	if(funcXtcType.toFunction().getResult().isVoid()) {
	  		Iterator<ECR> paramECRItr = lamType.getParams().iterator();
	  		for(int i = 1; i < stmt.getOperands().size(); i++) {
	  			Node srcNode = stmt.getOperand(i).getSourceNode();
	  			
	  			/* Resolve the syntax sugar of assign function to a function pointer */
	  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
	  			ECR argECR = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
	  			
	  			if(paramECRItr.hasNext()) {
		  			ECR paramECR = paramECRItr.next();
		  			ValueType argType = uf.getType(argECR);
		  			paramRetAssign(argType.getSize(), paramECR, argECR);
	  			} else {
	  				lamType.addParamECR(argECR);
	  			}
	  		}
	  	} 
	  	
	  	else {
	  		Node retNode = stmt.getOperand(1).getSourceNode();
	  		ECR retECR = ecrEncoder.toRval(retNode);
	  		ECR lamRetECR = lamType.getRet();
	  		ValueType lamRetType = uf.getType(lamRetECR);
	  		paramRetAssign(lamRetType.getSize(), retECR, lamRetECR);
	  		
	  		Iterator<ECR> paramECRItr = lamType.getParams().iterator();
	  		
	  		int i;
	  		for(i = 2; i < stmt.getOperands().size(); i++) {
	  			Node srcNode = stmt.getOperand(i).getSourceNode();
	  			
	  			/* Resolve the syntax sugar of assign function to a function pointer */
	  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
	  			ECR argECR = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
	  			
	  			if(!paramECRItr.hasNext()) break;
	  			
	  			ECR paramECR = paramECRItr.next();
	  			ValueType argType = uf.getType(argECR);
	  			paramRetAssign(argType.getSize(), paramECR, argECR);
	  		}
	  		
	  		for(; i < stmt.getOperands().size(); i++) {
	  			Node srcNode = stmt.getOperand(i).getSourceNode();
	  			/* Resolve the syntax sugar of assign function to a function pointer */
	  			ECR argECR = CType.getType(srcNode).resolve().isFunction() ?
	  					ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
	  			lamType.addParamECR(argECR);
	  		}
	  	}
  		break;
	  }
	  case ASSERT:
	  case ASSUME: {
	  	Node src = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.toRval(src);
	  	break;
	  }
	  default:
	  }
	}
  
  @Override
	public void initChecker() {
		// TODO Auto-generated method stub
		
	}

	@Override
  public void reset() {
  	uf.reset();
  }

	@Override
	public ECR getPointsToLoc(ECR base) {
    if(base.getType().isBottom())
    	IOUtils.err().println("WARNING: get points-to Loc ECR of bottom " + base);
    return uf.findRoot(uf.getLoc(base));
	}
	
	@Override
	public Map<Range<Long>, ECR> getStructMap(ECR structECR) {
		ValueType structType = uf.getType(structECR);
		if(!structType.isStruct()) return Collections.emptyMap();
			
		return structType.asStruct().getFieldMap().asMapOfRanges();
	}

	/**
	 * Return <code>void</code> type is <code>rep</code> is 
	 * with the bottom type (not yet allocated)
	 */
	@Override
	public long getRepTypeWidth(ECR ecr) {
		long defaultWidth = CType.getInstance().getWidth(CType.getUnitType());
		if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) return defaultWidth;

		long ptrWidth = CType.getInstance().getWidth(new PointerT(CType.getVoidType()));
		
		switch(ecr.getType().getKind()) {
		// structure's cell type is pointer (not the size of structure)
		case STRUCT:	return ptrWidth;
		case BOTTOM:
		case OBJECT:	return defaultWidth;
		default: {
			Size size = ecr.getType().getSize();
			if(!size.isNumber()) return defaultWidth;
			
			long value = size.getValue();
			if(value == 0)	return defaultWidth; // array type without length (stdlib.h)
			
			return CType.getInstance().toWidth(value);
		}
		}
	}
	
	@Override
	public void buildSnapShot() {
	  snapShot = uf.snapshot();
	}
	
	@Override
	public String getRepId(ECR ecr) {
		return String.valueOf(ecr.getId());
	}
	
	@Override
	public ECR getRep(Node node) {
		return uf.findRoot(ecrEncoder.toRval(node));
	}

	@Override
	public void addAllocRegion(Expression region, Node ptrNode) {
		if(!IOUtils.debugEnabled()) return;
		
		/* The freshRegionVar should have the same scope and type as place holder */
		ecrEncoder.createRegionVar(region, ptrNode);
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public void addStackVar(Expression lval, Node lvalNode) {
		if(!IOUtils.debugEnabled()) return;
		
		ecrEncoder.addStackVar(lval, lvalNode);
		IOUtils.debug().pln(displaySnapShot());
	}
	
	@Override
	public String displaySnapShot() {
		buildSnapShot();
		
	  StringBuilder sb = new StringBuilder().append('\n')
	  		.append("The result of field-sensitive Steensgaard analysis:\n");
	  
	  for(Entry<ECR, Collection<IRVar>> entry : snapShot.entrySet()) {
	  	ECR ecr = entry.getKey();
	  	if(uf.getType(ecr).isLambda()) continue;
	  	Collection<IRVar> vars = entry.getValue();
	  	if(!vars.isEmpty()) {
	  		sb.append("Partition ").append(ecr.getId()).append(": ");
	  		sb.append(uf.getType(ecr)).append("\n { ");
	  		
	  		for(IRVar var : vars) sb.append(var.getName()).append(' ');
	  		sb.append("}\n");
	  	}
	  }
	  return sb.toString();
	}

	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		ECR rep = ecrEncoder.toRval(funcNode);
		Type funcType = CType.getType(funcNode).resolve();
		if(funcType.isPointer()) rep = getPointsToLoc(rep);
		ECR funcRep = uf.getFunc(rep);
	  return uf.getEquivClass(funcRep);
	}
	
	@Override
	public Collection<ECR> getFillInReps(ECR rep) {
		Collection<ECR> reps = Sets.newLinkedHashSet();
		collectFieldReps(reps, rep);
	  return reps;
	}
	
	@Override
	public boolean isAccessTypeSafe(ECR rep) {
		switch(rep.getType().getKind()) {
		// structure's cell type is pointer (not the size of structure)
		case STRUCT:	return true;
		case BOTTOM:
		case OBJECT:	return false;
		default: {
			Size size = rep.getType().getSize();
			if(!size.isNumber()) return false;
			
			long value = size.getValue();
			if(value == 0)	return false; // array type without length (stdlib.h)
			
			return true;
		}
		}
	}

	private void collectFieldReps(Collection<ECR> reps, ECR rep) {
		if(reps.contains(rep)) return;
		
		reps.add(rep); 
		ValueType repType = uf.getType(rep);
		
		if(repType.isStruct()) {
			for(ECR elem : repType.asStruct().getFieldMap().asMapOfRanges().values()) {
				ECR elemRep = uf.findRoot(uf.getLoc(elem));
				collectFieldReps(reps, elemRep);
			}
		}
	}

	private void heapAssign(long size, ECR lhs) {
		Size rangeSize = Size.create(size);
		
		ValueType lhsType = uf.getType(lhs);
		Size lhsSize = lhsType.getSize();
		if(!Size.isLessThan(rangeSize, lhsSize)) {
			uf.expand(lhs);
		}
	  
		ECR lhsLoc = uf.getLoc(lhs);
		if(uf.getType(lhsLoc).isBottom()) {					
			ValueType blankType = ValueType.blank(
					Size.getTop(),
					Parent.getBottom());
			uf.setType(lhsLoc, blankType);
		}
	}

	private void simpleAssign(Type targetType, ECR lhs, ECR rhs) {
		targetType = targetType.resolve();
		// structure assign, treat like structure pointer assign to unify
		// the structures involved
		if(targetType.isStruct())  targetType = new PointerT(targetType);
		Size rangeSize = CType.isArithmetic(targetType) ? 
				Size.getBot() : Size.createForType(targetType);
	  uf.ccjoin(rangeSize, rhs, lhs);
	}
	
	private void paramRetAssign(Size rangeSize, ECR lhs, ECR rhs) {
	  ValueType lhs_type = uf.getType(lhs);
	  ValueType rhs_type = uf.getType(rhs);
	  
		Size lhs_size = lhs_type.getSize();
		Size rhs_size = rhs_type.getSize();
		
		if(!Size.isLessThan(rangeSize, lhs_size)) uf.expand(lhs);
		if(!Size.isLessThan(rangeSize, rhs_size)) uf.expand(rhs);
		
		ECR lhsLoc = uf.getLoc(lhs), rhsLoc = uf.getLoc(rhs);
		ECR lhsFunc = uf.getFunc(lhs), rhsFunc = uf.getFunc(rhs);
		
		uf.join(rhsLoc, lhsLoc);
		uf.join(rhsFunc, lhsFunc);
	}
}