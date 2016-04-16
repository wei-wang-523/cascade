package edu.nyu.cascade.c.pass.alias.steens;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Range;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.FunctionT;
import xtc.type.Type;
import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.steens.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.pass.IRVar;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;

/**
 * Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements IRAliasAnalyzer<ECR> {	
  private final UnionFindECR uf;
  private final ECREncoder ecrEncoder;
  private final SymbolTable symbolTable;
  private ImmutableMap<ECR, Collection<IRVar>> snapShot;
  private IRControlFlowGraph currentCFG;
  
  private Steensgaard (SymbolTable symbolTable) { 
    uf = UnionFindECR.create();
    ecrEncoder = ECREncoder.create(uf, symbolTable); 
    this.symbolTable = symbolTable;
  }
  
  public static Steensgaard create(SymbolTable symbolTable) {
    return new Steensgaard(symbolTable);
  }
  
	@Override
	public void analysis(IRControlFlowGraph globalCFG, Collection<IRControlFlowGraph> CFGs) {
		
		// Analyze global CFG
		{
			symbolTable.enterScope(globalCFG);
			currentCFG = globalCFG;
			
			final Collection<IRBasicBlock> topologicSeq = Lists.reverse(globalCFG.topologicalSeq(globalCFG.getEntry()));
			
			for(IRBasicBlock block : topologicSeq) {			
				for(IRStatement stmt : block.getStatements()) analysis(stmt);
				
				for(IREdge<?> outgoing : globalCFG.getOutgoingEdges(block)) {
					if(null != outgoing.getGuard()) 
						ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
				}
			}
		}
		
		// Analyze non-global CFG
		for(IRControlFlowGraph CFG : CFGs) {
			symbolTable.enterScope(CFG);
			currentCFG = CFG;
			
			GNode declarator = CFG.getSourceNode().getGeneric(2);
			GNode identifier = CAnalyzer.getDeclaredId(declarator);
			FunctionT funcXtcType = symbolTable.lookupType(identifier.getString(0)).resolve().toFunction();
			
			if(!funcXtcType.getParameters().isEmpty()) {		
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
					paramRetAssign(lamECRs.get(i), paramECRs.get(i));
				}
			}
		
			final Collection<IRBasicBlock> topologicSeq = Lists.reverse(CFG.topologicalSeq(CFG.getEntry()));
			
			for(IRBasicBlock block : topologicSeq) {			
				for(IRStatement stmt : block.getStatements()) analysis(stmt);
				
				for(IREdge<?> outgoing : CFG.getOutgoingEdges(block)) {
					if(null != outgoing.getGuard()) 
						ecrEncoder.toRval(outgoing.getGuard().getSourceNode());
				}
			}
		}
	}

	@Override
	public void reset() {
		uf.reset();
	}

  private void analysis(IRStatement stmt) {
  	IOUtils.debug().pln("Preprocess: " + stmt.getLocation() + ": " + stmt);
	  switch (stmt.getType()) {
	  case DECLARE:
	  case DECLARE_ARRAY: {    	
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.toLval(lhs);
	  	break;
	  }
	  case INIT: {
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	    Node rhs = stmt.getOperand(1).getSourceNode();
			
			ECR lhsECR = ecrEncoder.toRval(lhs);
	    ECR rhsECR = ecrEncoder.toRval(rhs);
	    uf.assign(lhsECR, rhsECR);
	    break;
	  }
	  case ASSIGN: {
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	  	Node rhs = stmt.getOperand(1).getSourceNode();
	    ECR lhsECR = ecrEncoder.toRval(lhs);
	    
	    /* Resolve the syntax sugar of assign function to a function pointer */
	    boolean isFuncType = CType.getType(rhs).resolve().isFunction();
	    ECR rhsECR = isFuncType ? ecrEncoder.toLval(rhs) : ecrEncoder.toRval(rhs);
	  	
	  	uf.assign(lhsECR, rhsECR);
	    break;
	  }
	  case ALLOCA:
	  case CALLOC:
	  case MALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    ECR lhsECR = ecrEncoder.toRval(lhs);
	    heapAssign(lhsECR);
	    break;
	  }
	  case RETURN: {
	  	String functionName = currentCFG.getName();
	    ECR funcECR = ecrEncoder.getFunctionECR(functionName);
  		LambdaType funcType = uf.getType(uf.getFunc(uf.getLoc(funcECR))).asLambda();
	    ECR retECR = funcType.getRet();
	    
	  	Node srcNode = stmt.getOperand(0).getSourceNode();
	  	ECR srcECR = ecrEncoder.toRval(srcNode);
	  	uf.cjoin(retECR, srcECR);
	  	break;
	  }
	  case CALL: {
	  	Node funcNode = stmt.getOperand(0).getSourceNode();
	  	ECR funcECR = ecrEncoder.toRval(funcNode);
	  	assert (null != funcECR);
	  	
	  	Type funcXtcType = CType.getType(funcNode).resolve();
	  	if(funcXtcType.isPointer()) {
	  		funcXtcType = funcXtcType.toPointer().getType();
	  		funcECR = uf.getLoc(funcECR);
	  	}
			
	  	/* For the function pointer parameters declared but not yet assigned */
	  	if(uf.getType(funcECR).isBot()) {
				IOUtils.err().println("WARNING: get Loc of " + funcECR);
				ValueType refType = ValueType.ref(ECR.createBottom(), ECR.createBottom());
				uf.setType(funcECR, refType);
			}
	  	
	  	ECR lamECR = uf.getType(funcECR).asRef().getFunction();
	  	
	  	if(uf.getType(lamECR).isBot()) {
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
		  			paramRetAssign(paramECR, argECR);
	  			} else {
	  				lamType.addParamECR(argECR);
	  			}
	  		}
	  	} 
	  	
	  	else {
	  		Node retNode = stmt.getOperand(1).getSourceNode();
	  		ECR retECR = ecrEncoder.toRval(retNode);
	  		paramRetAssign(retECR, lamType.getRet());
	  		
	  		Iterator<ECR> paramECRItr = lamType.getParams().iterator();
	  		
	  		int i;
	  		for(i = 2; i < stmt.getOperands().size(); i++) {
	  			Node srcNode = stmt.getOperand(i).getSourceNode();
	  			/* Resolve the syntax sugar of assign function to a function pointer */
	  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
	  			ECR argECR = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
	  			
	  			if(!paramECRItr.hasNext()) break;
	  			
	  			ECR paramECR = paramECRItr.next();
	  			paramRetAssign(paramECR, argECR);
	  		}
	  		
	  		for(; i < stmt.getOperands().size(); i++) {
	  			Node srcNode = stmt.getOperand(i).getSourceNode();
	  			/* Resolve the syntax sugar of assign function to a function pointer */
	  			boolean isFuncType = CType.getType(srcNode).resolve().isFunction();
	  			ECR argECR = isFuncType ? ecrEncoder.toLval(srcNode) : ecrEncoder.toRval(srcNode);
	  			lamType.addParamECR(argECR);
	  		}
	  	}
	  	
  		break;
	  }
	  case ASSUME:
	  case ASSERT: {
	  	for(IRExpression operand : stmt.getOperands())
	  		ecrEncoder.toRval(operand.getSourceNode());
	  	break;
	  }
	  default: return;
	  }
	}

	@Override
	public String displaySnapShot() {
		buildSnapShot();
	  StringBuilder sb = new StringBuilder();
	  sb.append('\n').append("The result of Steensgaard analysis:\n");
	  for(Entry<ECR, Collection<IRVar>> entry : snapShot.entrySet()) {
	  	ECR ecr = entry.getKey();
	  	if(uf.getType(ecr).isLambda()) continue;
	  	Collection<IRVar> vars = entry.getValue();
	  	if(!vars.isEmpty()) {
	  		sb.append("Partition ").append(ecr.getId());
	  		if(ecr.getType().isRef()) {
	  			RefType refType = ecr.getType().asRef();
	  			sb.append(" : Ref(")
	  				.append(uf.findRoot(refType.getLocation()).getId())
	  				.append(",")
	  				.append(uf.findRoot(refType.getFunction()).getId())
	  				.append(")");
	  		}
	  		
	  		sb.append("\n{ ");
	  		for(IRVar var : vars) {
	  			sb.append(var.getName()).append(' ');
	  		}
	  		sb.append("}\n");
	  	}
	  }
	  return sb.toString();
	}
	
	@Override
	public ECR getPtsToFieldRep(ECR base) {
		if(base.getType().isBot())
			IOUtils.err().println("WARNING: get points-to Loc ECR of bottom " + base);
		return uf.findRoot(uf.getLoc(base));
	}
	
	@Override
	public ECR getPtsToRep(Node node) {
	    return getPtsToFieldRep(getRep(node));
	}

	/**
	 * Return unit type: steensgaard doesn't hold any type info
	 */
	@Override
	public long getRepWidth(ECR rep) {
		return CType.getInstance().getWidth(CType.getUnitType());
	}
	
	@Override
	public Collection<IRVar> getEquivFuncVars(Node funcNode) {
		Type funcType = CType.getType(funcNode).resolve();		
		ECR rep = getRep(funcNode);
		if(funcType.isPointer()) rep = getPtsToFieldRep(rep);
		ValueType refType = uf.getType(rep);
		ECR funcRep = refType.asRef().getFunction();
	  return uf.getEquivClass(funcRep);
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
	public ECR getStackRep(Node node) {
		ECR rep = getRep(node);
		xtc.type.Type lvalType = CType.getType(node);
		
		/* The address should belongs to the group it points-to, where to reason
		 * about disjointness */
		return CType.isScalar(lvalType) ? rep : getPtsToFieldRep(rep);
	}

	@Override
	public void addVar(Expression lval, Node lvalNode) {
		if(!IOUtils.debugEnabled()) return;
		ecrEncoder.addStackVar(lval, lvalNode);
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public void addRegion(Expression region, Node ptrNode) {
		if(!IOUtils.debugEnabled()) return;
		ecrEncoder.createRegionVar(region, ptrNode);
		IOUtils.debug().pln(displaySnapShot());
	}
	
	@Override
	public Map<Range<Long>, ECR> getStructMap(ECR structECR, long length) {
		return Collections.emptyMap();
	}

	@Override
	public Collection<ECR> getFieldReps(ECR rep, Type Ty) {
	  return Collections.singleton(rep);
	}
	
	@Override
	public boolean isAccessTypeSafe(ECR rep) {
		return false;
	}

	private void heapAssign(ECR lhs) {
	  ECR lhsLoc = uf.getLoc(lhs);
	  
	  // Attach the fresh region directly the first operand of target var of malloc
	  if(uf.getType(lhsLoc).isBot()) {
	  	ValueType region_type = ValueType.ref(ECR.createBottom(), ECR.createBottom());
	  	uf.setType(lhsLoc, region_type);
	  }
	}
	
	private void paramRetAssign(ECR lhs, ECR rhs) {
	  ValueType lhs_type = uf.getType(lhs);
	  ValueType rhs_type = uf.getType(rhs);
	  
	  ValueTypeKind lKind = lhs_type.getKind();
	  ValueTypeKind rKind = rhs_type.getKind();
	  
	  switch(lKind) {
		case BOTTOM: {
			switch(rKind) {
			case REF: {
				uf.setType(lhs, rhs_type);
				break;
			}
			default:
				break;
			}
			break;
		}
		case REF: {
			switch(rKind) {
			case BOTTOM: {
				uf.setType(rhs, lhs_type);
				break;
			}
			case REF: {
			  ECR lhsLoc = lhs_type.asRef().getLocation();
			  ECR rhsLoc = rhs_type.asRef().getLocation();
			  uf.join(lhsLoc, rhsLoc);
			  
			  ECR lhsFunc = lhs_type.asRef().getFunction();
			  ECR rhsFunc = rhs_type.asRef().getFunction();			  
			  uf.join(lhsFunc, rhsFunc);
				break;
			}
			default:
				break;
			}
			break;
		}
		default:
			break;
	  }
	}

	@Override
	public void analyzeVarArg(String func, Type funcTy, Node varArgN) {
		// TODO Auto-generated method stub
		
	}
}