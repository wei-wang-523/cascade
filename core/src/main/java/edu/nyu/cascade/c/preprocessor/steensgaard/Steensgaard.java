package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Collection;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;

import xtc.tree.Node;
import xtc.type.Type;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements PreProcessor<ECR> {	
  private final UnionFindECR uf;
  private final ECREncoder ecrEncoder;
  private final Collection<IRStatement> staticStmt = Sets.newHashSet();
  private ImmutableMap<ECR, Collection<IRVar>> snapShot;
  
  private Steensgaard (SymbolTable symbolTable) { 
    uf = UnionFindECR.create();
    ecrEncoder = ECREncoder.create(uf, symbolTable); 
  }
  
  public static Steensgaard create(SymbolTable symbolTable) {
    return new Steensgaard(symbolTable);
  }
  
  @Override
  public void reset() {
  	staticStmt.clear();
  	ecrEncoder.reset();
  }

  @Override
	public void analysis(IRStatement stmt) {
//  	IOUtils.out().println("Preprocess: " + stmt.getLocation() + ": " + stmt);
	  switch (stmt.getType()) {
	  case DECLARE: {
    	if(stmt.hasPreLabel(Identifiers.STATIC)) {
    		if(staticStmt.contains(stmt)) break;
    		staticStmt.add(stmt);
    	}
    	
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.encodeECR(lhs);
	  	break;
	  }
	  case ASSUME:
	  case ASSERT: {
	  	Node src = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.encodeECR(src);
	  	break;
	  }
	  case INIT: {
	  	if(stmt.hasPreLabel(Identifiers.STATIC)) {
  			if(staticStmt.contains(stmt)) break;
  			staticStmt.add(stmt);
  		}
  		
  		if(stmt.getOperands().size() == 1) break; 
  		
	  	Node lhs = stmt.getOperand(0).getSourceNode();		   
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);
			Type lhsType = lhsECR.getXtcType().resolve();
			if(lhsType.isArray() || lhsType.isStruct() || lhsType.isUnion()) {
				ValueType lhs_type = uf.getType(lhsECR);
			  assert(ValueTypeKind.REF.equals(lhs_type.getKind()));
			  ECR lhsLoc = lhs_type.asRef().getLocation();
			  for(int i = 1; i < stmt.getOperands().size(); i++) {
			  	ECR rhsECR = ecrEncoder.encodeECR(stmt.getOperand(i).getSourceNode());
			  	uf.join(lhsLoc, rhsECR);
			  }
			} else {
		    Node rhs = stmt.getOperand(1).getSourceNode();
		    ECR rhsECR = ecrEncoder.encodeECR(rhs);
		    simpleAssign(lhsECR, rhsECR);
			}
			
			break;
	  }
	  case ASSIGN: {
	  	Node lhs = stmt.getOperand(0).getSourceNode();		   
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);	   
	  	Node rhs = stmt.getOperand(1).getSourceNode();
	  	ECR rhsECR = ecrEncoder.encodeECR(rhs);
	  	simpleAssign(lhsECR, rhsECR);
	    break;
	  }
	  case ALLOCA:
	  case CALLOC:
	  case MALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);
	    heapAssign(lhsECR);
	    break;
	  }
	  default:
	  }
	}

	@Override
	public String displaySnapShot() {
		buildSnapShot();
	  StringBuilder sb = new StringBuilder();
	  sb.append('\n').append("The result of Steensgaard analysis:\n");
	  for(Entry<ECR, Collection<IRVar>> entry : snapShot.entrySet()) {
	  	ECR ecr = entry.getKey();
	  	Collection<IRVar> vars = entry.getValue();
	  	if(!vars.isEmpty()) {
	  		sb.append("Partition ").append(ecr.getId());
	  		if(ecr.getType().isRef()) {
	  			RefType refType = ecr.getType().asRef();
	  			sb.append(" : Ref(")
	  				.append(uf.findRoot(refType.getLocation()).getId())
	  				.append(")");
	  			sb.append(" ").append(refType.getXtcType());
	  		}
	  		
	  		sb.append("\n{ ");
	  		for(IRVar var : vars) {
	  			sb.append(var.toStringShort()).append(' ');
	  		}
	  		sb.append("}\n");
	  	}
	  }
	  return sb.toString();
	}
	
	@Override
	public ECR getPointsToRep(Node node) {
  	ECR base = getRep(node);
  	ValueType baseType = base.getType();
  	
  	if(!baseType.isRef()) {
  		IOUtils.err().println("WARNING: get points-to ECR of " + base.toStringShort());
  		return ecrEncoder.getNullPtrECR();
  	}
  	
  	return uf.findRoot(uf.getType(base).asRef().getLocation());
	}

	/**
	 * Return <code>void</code> type is <code>rep</code> is 
	 * with the bottom type (not yet allocated)
	 */
	@Override
	public Type getRepType(ECR rep) {
		if(rep.getType().isBot()) {
			IOUtils.err().println("WARNING: access " + rep.toStringShort());
			return CType.getVoidType();
		}
		return rep.getXtcType();
	}

	@Override
	public ImmutableMap<ECR, Collection<IRVar>> getSnapShot() {
		buildSnapShot(); // update snapShot
		return snapShot;
	}
	
	@Override
	public void buildSnapShot() {
	  snapShot = uf.snapshot();
	}
	
	@Override
	public String getRepId(ECR ecr) {
		return ecr.getId();
	}
	
	@Override
	public ECR getRep(Node node) {
    return uf.findRoot(ecrEncoder.encodeECR(node));
	}
	
	@Override
	public ECR getSrcRep(ECR rep) {
	  return rep;
	}

	@Override
	public IRVar addStackVar(Expression lval, Node lvalNode) {		
		ECR repECR = ecrEncoder.encodeECR(lvalNode);
		VarImpl var = ecrEncoder.createForStackVar(lval, lvalNode);
		uf.join(var.getECR(), repECR);
//		IOUtils.err().println(displaySnapShot());
		return var;
	}

	@Override
	public void addAllocRegion(ECR placeHolder, Expression region, Node ptrNode) {
		Preconditions.checkArgument(placeHolder.getType().isRef());
		ECR rep = placeHolder.getType().asRef().getAddress();
		assert(rep != null);
		
		/* The freshRegionVar should have the same scope and type as place holder */
		ECR freshRegionECR = ecrEncoder.createForRegion(region, ptrNode);
		freshRegionECR.getType().setAddress(rep);
		uf.join(freshRegionECR, placeHolder);
//		IOUtils.err().println(displaySnapShot());
	}

	private void heapAssign(ECR lhs) {
	  ValueType lhs_type = uf.getType(lhs);
	  ECR lhsLoc;
	  if(!ValueTypeKind.REF.equals(lhs_type.getKind())) {
	  	IOUtils.err().println("WARNING: heap assign to " + lhs.toStringShort());
	  	ECR nullPtr = ecrEncoder.getNullPtrECR();
	  	uf.join(lhs, nullPtr);
	  	lhsLoc = uf.getType(lhs).asRef().getLocation();
	  } else {
	  	lhsLoc = lhs_type.asRef().getLocation();
	  }
	  
	  // Attach the fresh region directly the first operand of target var of malloc
	  if(ValueTypeKind.BOTTOM.equals(uf.getType(lhsLoc).getKind())) {
		  String rootName = CScopeAnalyzer.getRootScopeName();
		  ECR loc = ECR.createBottom();
		  ECR func = ECR.createBottom();
	  	loc.getType().setAddress(lhsLoc);
		  func.getType().setAddress(lhsLoc);
	  	ValueType region_type = ValueType.ref(loc, func, VoidT.TYPE, rootName);
	  	region_type.setAddress(lhs);
	  	uf.setType(lhsLoc, region_type);
	  }
	}

	private void simpleAssign(ECR lhs, ECR rhs) {
	  ValueType lhs_type = uf.getType(lhs);
	  ValueType rhs_type = uf.getType(rhs);
	  
	  ValueTypeKind lKind = lhs_type.getKind();
	  ValueTypeKind rKind = rhs_type.getKind();
	  
	  switch(lKind) {
		case BOTTOM: {
			switch(rKind) {
			case REF: {
				uf.setType(lhs, lhs_type);
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
			  uf.cjoin(lhsLoc, rhsLoc);
			  
			  ECR lhsFunc = lhs_type.asRef().getFunction();
			  ECR rhsFunc = rhs_type.asRef().getFunction();			  
			  uf.cjoin(lhsFunc, rhsFunc);
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
}