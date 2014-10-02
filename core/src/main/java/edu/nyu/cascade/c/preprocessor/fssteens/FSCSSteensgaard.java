package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Collection;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;

import xtc.tree.Node;
import xtc.type.Type;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

/**
 * A class which implements Bjarne Steensgaard's alias analysis algorithm.
 * 
 * @author Wei
 *
 */
public class FSCSSteensgaard implements PreProcessor<ECR> {	
  private final UnionFindECR uf;
  private final ECREncoder ecrEncoder;
  private ImmutableMap<ECR, Collection<IRVar>> snapShot;
  
  private FSCSSteensgaard (SymbolTable symbolTable) {
    uf = UnionFindECR.create();
    ecrEncoder = ECREncoder.create(uf, symbolTable); 
  }
  
  public static FSCSSteensgaard create(SymbolTable symbolTable) {
    return new FSCSSteensgaard(symbolTable);
  }

  @Override
	public void analysis(IRStatement stmt) {
	  switch (stmt.getType()) {
	  case LIFT_BEGIN:
	  	CScopeAnalyzer.liftStatementsBegin();
	  	break;
	  case LIFT_END:
	  	CScopeAnalyzer.liftStatementsEnd();
	  	break;
	  case FUNC_ENT: {
	  	Node defNode = stmt.getSourceNode();
	  	assert(defNode.hasName("FunctionDefinition"));
	  	String funcName = CType.getScopeName(defNode);
	  	CScopeAnalyzer.pushScope(funcName);
	  	break;
	  }
	  case FUNC_EXIT: {
	  	CScopeAnalyzer.popScope();
	  	break;
	  }
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
	    long rangeSize = CType.getSizeofType(CType.getType(lhs).resolve());
	    
//	    if(rhs.hasName("AddressExpression")) {
//	    	Node rhsBaseNode = rhs.getNode(0);
//	    	if(CType.isCompound(CType.getType(rhsBaseNode).resolve())) {
//	    		/* int *p = &B; when B is an array or structure, 
//	    		 * the statement is equivalent to p = B, delegated it
//	    		 * to following analysis
//	    		 */
//	    		rhs = rhsBaseNode;
//	    	} else {
//			    ECR lhsECR = ecrEncoder.encodeECR(lhs);
//			    ECR rhsECR = ecrEncoder.encodeECR(rhsBaseNode);
//	        addrAssign(rangeSize, lhsECR, rhsECR);
//	        break;
//	    	}
//	    }
	    
//	    if(rhs.hasName("IndirectComponentSelection") ||
//	    		rhs.hasName("DirectComponentSelection")) {
//	    	ECR lhsECR = ecrEncoder.encodeECR(lhs);
//	    	ECR baseECR = ecrEncoder.encodeECR(rhs.getNode(0));
//	    	ECR rhsECR = ecrEncoder.encodeECR(rhs);
//	    	fieldAssign(rangeSize, lhsECR, rhsECR, baseECR);
//	    	break;
//	    } 
//	    
//	    else {
		    ECR lhsECR = ecrEncoder.encodeECR(lhs);
		    ECR rhsECR = ecrEncoder.encodeECR(rhs);
	    	simpleAssign(rangeSize, lhsECR, rhsECR);
	    	break;
//	    }
	  }
	  case ALLOC: {
	    Node lhs = stmt.getOperand(0).getSourceNode();
	    Type lhsType = CType.getType(lhs);
	    long rangeSize = CType.getSizeofType(lhsType.resolve());
	    
	    ECR lhsECR = ecrEncoder.encodeECR(lhs);
	    heapAssign(rangeSize, lhsECR, lhsType);
	    break;
	  }
	  default:
	  }
	}

	@Override
	public String displaySnapShot() {
		buildSnapShot();
		
	  StringBuilder sb = new StringBuilder().append('\n')
	  		.append("The result of field-sensitive context-sensitive Steensgaard analysis:\n");
	  
	  for(Entry<ECR, Collection<IRVar>> entry : snapShot.entrySet()) {
	  	ECR ecr = entry.getKey();
	  	
	  	Collection<IRVar> vars = entry.getValue();
	  	if(!vars.isEmpty()) {
	  		sb.append("Partition ").append(ecr.getId());
	  		
	  		ValueType ecrType = uf.getType(ecr);
	  		
	  		switch(ecrType.getKind()) {
				case BLANK:
					sb.append("\t: Blank(");
					
		  		if(ecrType.hasAddress()) {
		  			sb.append("p(")
		  				.append(uf.findRoot(ecrType.getAddress()).getId())
		  				.append(')');
		  		}
					break;
					
				case OBJECT: 
					sb.append("\t: Object(").append(uf.findRoot(ecrType.asObject().getLoc().fst()).getId());
					
		  		if(ecrType.hasAddress()) {
		  			sb.append(", p(")
		  				.append(uf.findRoot(ecrType.getAddress()).getId())
		  				.append(')');
		  		}
					break;
				
				case SIMPLE:
					sb.append("\t: Simple(").append(uf.findRoot(ecrType.asSimple().getLoc().fst()).getId());
					
		  		if(ecrType.hasAddress()) {
		  			sb.append(", p(")
		  				.append(uf.findRoot(ecrType.getAddress()).getId())
		  				.append(')');
		  		}					
		  		break;
		  		
				case STRUCT:
					sb.append("\t: Struct({ ");
					for(Entry<Long, ECR> pair : ecrType.asStruct().getMapping().entrySet()) {
						long key = pair.getKey();
						ECR value = uf.findRoot(pair.getValue());
						sb.append('<').append(key).append(">=").append(value.getId()).append(' ');
					}
					sb.append('}');
					
		  		if(ecrType.hasAddress()) {
		  			sb.append(", p(")
		  				.append(uf.findRoot(ecrType.getAddress()).getId())
		  				.append(')');
		  		}
					break;
					
				default:
					sb.append("\t: Bottom(");
		  		if(ecrType.hasAddress()) {
		  			sb.append("p(")
		  				.append(uf.findRoot(ecrType.getAddress()).getId())
		  				.append(')');
		  		}
					break;
	  		}
	  		
	  		sb.append(") ").append(ecrType.getSize()).append("\n { ");
	  		for(IRVar var : vars) {
	  			sb.append(var.toStringShort()).append(' ');
	  		}
	  		sb.append("}\n");
	  	}
	  }
	  return sb.toString();
	}
	
	@Override
	public ECR getSrcRep(ECR ecr) {
		Parent parent = uf.getType(ecr).getParent();
		while(!(parent.isEmpty() || parent.isTop())) {
			ecr = parent.getECR();
			parent = uf.getType(ecr).getParent();
		}
		return uf.findRoot(ecr);
	}

	@Override
	public ECR getPointsToRep(Node node) {
		if(node.hasName("AddressExpression")) {
			Node baseNode = node.getNode(0);
			Type baseType = CType.getType(baseNode).resolve();
			if(!baseType.isArray()) return getRep(baseNode);
			
			node = baseNode;
		}
		
    Type type = CType.getType(node).resolve();
    assert(type.isArray() || type.isPointer() || type.isStruct() || type.isUnion());
    
    ECR base = getRep(node);
    
    if(base.getType().isBottom())
    	IOUtils.err().println("WARNING: get points-to ECR of bottom " + base);
    
    Size size = uf.getType(base).getSize();
		uf.ensureSimObj(base, size);
    ValueType baseType = uf.getType(base);
		Pair<ECR, Offset> pair;
		if(baseType.isSimple()) {
			pair = baseType.asSimple().getLoc();
		} else {
			pair = baseType.asObject().getLoc();
		}
		
		uf.unlessZero(pair.snd(), pair.fst());
		return uf.findRoot(pair.fst());
	}

	/**
	 * Return <code>void</code> type is <code>rep</code> is 
	 * with the bottom type (not yet allocated)
	 */
	@Override
	public Type getRepType(ECR rep) {
		if(rep.getType().isBottom()) {
			IOUtils.err().println("WARNING: " + rep + " is with bottom type");
			return CType.getVoidType();
		}
		
		if(rep.getType().isObject()) { // object type ECR has unit type
			return CType.getUnitType();
		}
		
		if(rep.getType().getSize().isTop()) { // top cell size ECR has unit type
			return CType.getUnitType();
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
	public void addAllocRegion(ECR placeHolder, Expression region) {
		ECR rep = uf.getType(placeHolder).getAddress();
		assert(rep != null);
		
		/* The freshRegionVar should have the same scope and type as place holder */
		ECR freshRegionECR = ecrEncoder.createForRegion(region);
		uf.getType(freshRegionECR).setAddress(rep);
		uf.join(freshRegionECR, placeHolder);
		
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public IRVar addStackVar(Expression lval) {
		ECR repECR = ecrEncoder.encodeECR(lval.getNode());
		VarImpl var = ecrEncoder.createForStackVar(lval);
		uf.join(var.getECR(), repECR);
		IOUtils.debug().pln(displaySnapShot()); 
		return var;
	}
	
//	private void fieldAssign(long size, ECR lhs, ECR rhs, ECR base) {
//		Size rangeSize = Size.create(size);
//		uf.ensureSimObj(lhs, rangeSize);
//		
//		ValueType lhsType = uf.getType(lhs);
//
//		Size lhsSize = lhsType.getSize();
//		if(!Size.isLessThan(rangeSize, lhsSize)) {
//			uf.expand(lhs);
//		}
//		
//		Pair<ECR, Offset> lhsLoc;
//		if(lhsType.isObject()) {
//			lhsLoc = lhsType.asObject().getLoc();
//		} else {
//			lhsLoc = lhsType.asSimple().getLoc();
//		}
//		
//		Size baseSize = uf.getType(base).getSize();
//		uf.ensureSimObj(base, baseSize);
//		
//		ValueType baseType = uf.getType(base);
//		Pair<ECR, Offset> baseLoc;
//		if(baseType.isObject()) {
//			baseLoc = baseType.asObject().getLoc();
//		} else {
//			baseLoc = baseType.asSimple().getLoc();
//		}
//		
//		if(baseLoc.equals(rhs)) { // no field-selection is happened
//			uf.join(baseLoc, lhsLoc);
//		} else { // rhs is the field ECR contained in the mapping of baseLoc (with Struct type)
//			uf.join(Pair.of(rhs, Offset.createZero()), lhsLoc);
//		}
//	}
	
//	private void addrAssign(long size, ECR lhs, ECR rhs) {
//		Size rangeSize = Size.create(size);
//		uf.ensureSimObj(lhs, rangeSize);
//		
//		ValueType lhsType = uf.getType(lhs);
//
//		Size lhsSize = lhsType.getSize();
//		if(!Size.isLessThan(rangeSize, lhsSize)) {
//			uf.expand(lhs);
//		}
//		
//		Pair<ECR, Offset> lhsLoc;
//		if(lhsType.isObject()) {
//			lhsLoc = lhsType.asObject().getLoc();
//		} else {
//			lhsLoc = lhsType.asSimple().getLoc();
//		}
//
//		uf.join(Pair.of(rhs, Offset.createZero()), lhsLoc);
//	}

	private void heapAssign(long size, ECR lhs, Type lhsXtcType) {
		Size rangeSize = Size.create(size);
		uf.ensureSimObj(lhs, rangeSize);
		
		ValueType lhsType = uf.getType(lhs);

		Size lhsSize = lhsType.getSize();
		if(!Size.isLessThan(rangeSize, lhsSize)) {
			uf.expand(lhs);
		}
	  
		Pair<ECR, Offset> lhsLoc;
		if(lhsType.isObject()) {
			lhsLoc = lhsType.asObject().getLoc();
		} else {
			lhsLoc = lhsType.asSimple().getLoc();
		}
		
		ECR lhsLocBase = lhsLoc.fst();
		if(uf.getType(lhsLocBase).isBottom()) {
			assert(lhsXtcType.resolve().isPointer());
			Type ptrType = lhsXtcType.resolve().toPointer().getType().resolve();
			Type cellType = ptrType.isArray() ? ptrType.toArray().getType() : ptrType;
					
			ValueType blankType = ValueType.blank(
					Size.createForType(cellType), 
					Parent.getEmpty(), 
					cellType, 
					CScopeAnalyzer.getRootScopeName());
			blankType.setAddress(lhs);
			uf.setType(lhsLocBase, blankType);
		}
	}

	private void simpleAssign(long size, ECR lhs, ECR rhs) {
		Size rangeSize = Size.create(size);
	  uf.cjoin(rangeSize, rhs, lhs);
	}
}