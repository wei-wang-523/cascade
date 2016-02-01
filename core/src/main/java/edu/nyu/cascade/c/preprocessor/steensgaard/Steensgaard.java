package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Collection;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;

import xtc.tree.Node;
import xtc.type.Type;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.steensgaard.ValueType.ValueTypeKind;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class Steensgaard implements PreProcessor<ECR> {	
  private final UnionFindECR uf;
  private final ECREncoder ecrEncoder;
  private ImmutableMap<ECR, Collection<IRVar>> snapShot;
  
  private Steensgaard (SymbolTable symbolTable) { 
    uf = UnionFindECR.create();
    ecrEncoder = ECREncoder.create(uf, symbolTable); 
  }
  
  public static Steensgaard create(SymbolTable symbolTable) {
    return new Steensgaard(symbolTable);
  }

  @Override
	public void analysis(IRStatement stmt) {
//  	IOUtils.out().println("Preprocessing: " + stmt);
	  switch (stmt.getType()) {
	  case DECLARE: {
	  	Node lhs = stmt.getOperand(0).getSourceNode();
	  	ecrEncoder.encodeECR(lhs);
	  	break;
	  }
	  case ENUM: {
	  	ecrEncoder.createEnumECR(Iterables.transform(
	  			stmt.getOperands(), new Function<IRExpression, Node>() {
						@Override
            public Node apply(IRExpression iExpr) {
	            return iExpr.getSourceNode();
            }
	  	}));
	  	break;
	  }
	  case ASSIGN: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Node rhs = stmt.getOperand(1).getSourceNode();
	    
//	    if(rhs.hasName("AddressExpression")) {
//	    	Node rbase = rhs.getNode(0);
//		    ECR lhsECR = ecrEncoder.encodeECR(lhs);
//		    ECR rhsECR = ecrEncoder.encodeECR(rbase);
//		    Type rhsXtcType = CType.getType(rbase).resolve();
//		    
//			  if(rhsXtcType.isArray()) { 
//			  	// int *p = &B; B is an array, p = B, leave it to simple assign
//			  	rhsECR = uf.getType(rhsECR).asRef().getLocation();
//			  } else {
//			  	addrAssign(lhsECR, rhsECR); break;
//			  }
//	    }
		   
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);
	    ECR rhsECR = ecrEncoder.encodeECR(rhs);
	    simpleAssign(lhsECR, rhsECR);
	    break;
	  }
	  case ALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);
	    Type lhsType = CType.getType(lhs);
	    heapAssign(lhsECR, lhsType);
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
		if(node.hasName("AddressExpression")) {
			Node baseNode = node.getNode(0);
			Type baseType = CType.getType(baseNode).resolve();
			if(!baseType.isArray()) return getRep(baseNode);
			
			node = baseNode; // &array = array
		}
		
    Type type = CType.getType(node).resolve();
    assert(type.isArray() || type.isPointer() || type.isStruct() || type.isUnion());
		
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
	public IRVar addStackVar(Expression lval) {		
		ECR repECR = ecrEncoder.encodeECR(lval.getNode());
		VarImpl var = ecrEncoder.createForStackVar(lval);
		uf.join(var.getECR(), repECR);
//		IOUtils.debug().pln(displaySnapShot());
		return var;
	}

	@Override
	public void addAllocRegion(ECR placeHolder, Expression region) {
		Preconditions.checkArgument(placeHolder.getType().isRef());
		ECR rep = placeHolder.getType().asRef().getAddress();
		assert(rep != null);
		
		/* The freshRegionVar should have the same scope and type as place holder */
		ECR freshRegionECR = ecrEncoder.createForRegion(region);
		freshRegionECR.getType().setAddress(rep);
		uf.join(freshRegionECR, placeHolder);
//		IOUtils.debug().pln(displaySnapShot());
	}
	
//	private void addrAssign(ECR lhs, ECR rhs) {
//	  ValueType lhs_type = uf.getType(lhs);
//	  assert(ValueTypeKind.REF.equals(lhs_type.getKind()));
//	  ECR lhsLoc = lhs_type.asRef().getLocation();
//	  uf.join(lhsLoc, rhs);
//	}

	private void heapAssign(ECR lhs, Type lhsType) {
	  ValueType lhs_type = uf.getType(lhs);
	  assert(ValueTypeKind.REF.equals(lhs_type.getKind()));
	  ECR lhsLoc = lhs_type.asRef().getLocation();
	  // Attach the fresh region directly the first operand of target var of malloc
	  if(ValueTypeKind.BOTTOM.equals(uf.getType(lhsLoc).getKind())) {
	  	Type ptrToType = lhsType.resolve().toPointer().getType();
		  Type regionType = CType.getCellType(ptrToType);
		  String rootName = CScopeAnalyzer.getRootScopeName();
		  ECR loc = ECR.createBottom();
		  ECR func = ECR.createBottom();
	  	loc.getType().setAddress(lhsLoc);
		  func.getType().setAddress(lhsLoc);
	  	ValueType region_type = ValueType.ref(loc, func, regionType, rootName);
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