/**
 * 
 */
package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.List;
import java.util.Map;

import xtc.tree.*;
import xtc.type.EnumeratorT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

class ECREncoder extends Visitor {
  	
  private final UnionFindECR uf;
  private final SymbolTable symbolTable;
  /**
   * Store all the ECRs created for declared variables with
   * their references names (variable names) and scope names
   */
  private final Map<Pair<String, String>, ECR> ecrMap = Maps.newHashMap();
  private final Map<EnumeratorT, ECR> enumECRs = Maps.newHashMap();
  
  private ECREncoder(UnionFindECR uf, SymbolTable symbolTable) {
  	this.uf = uf;
  	this.symbolTable = symbolTable;
  }
  
  public static ECREncoder create(UnionFindECR uf, SymbolTable symbolTable) {
  	return new ECREncoder(uf, symbolTable);
  }
    
  public ECR encodeECR(Node node) {
    ECR res = (ECR) dispatch(node);
    assert(res != null);
    return res;
  }
  
  @Override
  public ECR unableToVisit(Node node) throws VisitingException {
    IOUtils.err()
        .println(
            "APPROX: Treating unexpected node type as NULL: "
                + node.getName());
    return ECR.createBottom();
  }
  
  public ECR visitConditionalExpression(GNode node) {
  	return getOpECR(node, node.getNode(1), node.getNode(2));
  }

  public ECR visitAdditiveExpression(GNode node) {
  	Node lhsNode = node.getNode(0);
  	Node rhsNode = node.getNode(2);  	
  	return getOpECR(node, lhsNode, rhsNode);
  }
  
  public ECR visitShiftExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(2));
  }
  
  public ECR visitSubscriptExpression(GNode node) {
  	Node baseNode = node.getNode(0);
  	ECR baseECR = encodeECR(baseNode);
  	return getLocECR(baseECR, CType.getType(node));
  }
  
  public ECR visitFunctionCall(GNode node) {
  	Node funcNode = node.getNode(0);
  	String funcName = funcNode.getString(0);
  	String rootScope = CScopeAnalyzer.getRootScopeName();

  	Type returnType;
  	if(ReservedFunction.isReserved(funcName)) {
  		Sig signature = ReservedFunction.getSignature(funcName);
  		returnType = signature.getReturnType();
  	} else {
  		returnType = CType.getType(node);
  	}
  	
  	Size size = Size.createForType(returnType);
  	BlankType type = ValueType.blank(
  			size, Parent.getEmpty(), returnType, rootScope);
  	return ECR.create(type);
  }
  
  public ECR visitAddressExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    return getAddrECR(base);
  }

  public ECR visitAssignmentExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(2));
  }

  public ECR visitBitwiseAndExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(1));
  }
  
  public ECR visitBitwiseOrExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(1));
  }
  
  public ECR visitBitwiseXorExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(1));
  }
  
  public ECR visitBitwiseNegationExpression(GNode node) {
  	return encodeECR(node.getNode(0));
  }

  public ECR visitCastExpression(GNode node) {
  	ECR baseECR = encodeECR(node.getNode(1));
  	Size size = Size.createForType(CType.getType(node));
  	uf.ensureSimObj(baseECR, size);
  	return baseECR;
  }
  
  public ECR visitCharacterConstant(GNode node) {
  	Type xtcType = CType.getType(node);
		return createConstant(xtcType);
  }

  public ECR visitEqualityExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(2));
  }

  public List<ECR> visitExpressionList(GNode node) {
    List<ECR> subECRList = Lists.newArrayListWithCapacity(node.size());
    for (Object elem : node) {
      ECR subECR = encodeECR(GNode.cast(elem));
      subECRList.add(subECR);
    }
    return subECRList;
  }

  public ECR visitIndirectionExpression(GNode node) {
    ECR baseECR = encodeECR(node.getNode(0));
  	return getLocECR(baseECR, CType.getType(node));
  }

  public ECR visitIntegerConstant(GNode node) {
		xtc.type.Type xtcType = CType.getType(node);
		return createConstant(xtcType);
  }

  public ECR visitLogicalAndExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(1));
  }

  public ECR visitLogicalNegationExpression(GNode node) {
    return encodeECR(node.getNode(0));
  }

  public ECR visitLogicalOrExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(1));
  }

  public ECR visitPreincrementExpression(GNode node) {
  	long size = CType.getSizeofType(CType.getType(node));
    ECR base = encodeECR(node.getNode(0));
    ECR intConstant = createConstant(CType.getType(node));
    uf.cjoin(size, base, intConstant);
    return base;
  }

  public ECR visitPredecrementExpression(GNode node) {
  	long size = CType.getSizeofType(CType.getType(node));
    ECR base = encodeECR(node.getNode(0));
    ECR intConstant = createConstant(CType.getType(node));
    uf.cjoin(size, base, intConstant);
    return base;
  }
  
  public ECR visitPostincrementExpression(GNode node) {
  	long size = CType.getSizeofType(CType.getType(node));
    ECR base = encodeECR(node.getNode(0));
    ECR intConstant = createConstant(CType.getType(node));
    uf.cjoin(size, base, intConstant);
    return base;
  }

  public ECR visitPostdecrementExpression(GNode node) {
  	long size = CType.getSizeofType(CType.getType(node));
    ECR base = encodeECR(node.getNode(0));
    ECR intConstant = createConstant(CType.getType(node));
    uf.cjoin(size, base, intConstant);
    return base;
  }
  
  public ECR visitPrimaryIdentifier(GNode node) {
  	String id = node.getString(0);
  	String scopeName = CType.getScopeName(node);
  	Scope currScope = symbolTable.getScope(scopeName);
  	
  	Scope scope = currScope.isDefined(id) ? // region is not defined under scope
  			currScope.lookupScope(id) : currScope;
  	
    String scopeKey = peekScopeKey(scope);
  	Pair<String, String> key = Pair.of(id, scopeKey);
  	if(ecrMap.containsKey(key)) return ecrMap.get(key);
  	
  	IRVarInfo info = (IRVarInfo) scope.lookup(id);
  	Type type = info.getXtcType();
  	
  	if(type.isEnumerator()) return enumECRs.get(type.toEnumerator());
  	
  	assert(info.hasProperty(Identifiers.CTRLVAR));
  	
  	VarImpl freshVar = VarImpl.createForCtrlSymbol(info);
    ECR freshECR = freshVar.getECR();
    uf.add(freshVar);
    ecrMap.put(key, freshECR);
  	return freshECR;
  }

  public ECR visitRelationalExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(2));
  }

  public ECR visitSimpleDeclarator(GNode node) {
  	String id = node.getString(0);
  	String scopeName = CType.getScopeName(node);
  	Scope currScope = symbolTable.getScope(scopeName);
  	
  	Scope scope = currScope.isDefined(id) ? // region is not defined under scope
  			currScope.lookupScope(id) : currScope;
  	
    String scopeKey = peekScopeKey(scope);
  	Pair<String, String> key = Pair.of(id, scopeKey);
  	if(ecrMap.containsKey(key)) return ecrMap.get(key);
  	
  	IRVarInfo info = (IRVarInfo) scope.lookup(id);
  	ECR varECR = createForSymbol(info);
  	ecrMap.put(key, varECR);
  	
  	return varECR;
  }
  
	public ECR visitStringConstant(GNode node) {
		Type xtcType = CType.getType(node);
  	return createConstant(xtcType);
  }
  
  public ECR visitSizeofExpression(GNode node) {
		xtc.type.Type xtcType = CType.getType(node);
		return createConstant(xtcType);
  }
  
  public ECR visitUnaryMinusExpression(GNode node) 
      throws VisitingException {
    return encodeECR(node.getNode(0));
  }
  
  public ECR visitMultiplicativeExpression(GNode node) {
  	return getOpECR(node, node.getNode(0), node.getNode(2));
  }
  
  public ECR visitDirectComponentSelection(GNode node) {
  	Node baseNode = node.getNode(0);
    String fieldName = node.getString(1);
    
    ECR baseECR = encodeECR(baseNode);
    ECR addrECR = getAddrECR(baseECR);
    Type baseXtcType = CType.getType(baseNode);
    return getComponent(addrECR, baseXtcType, fieldName);
  }
  
  public ECR visitIndirectComponentSelection(GNode node) {
  	Node baseNode = node.getNode(0);
    String fieldName = node.getString(1);
    
    ECR baseECR = encodeECR(baseNode);
    Type baseXtcType = CType.getType(baseNode).resolve().toPointer().getType();
    return getComponent(baseECR, baseXtcType, fieldName);
  }
	
	void createEnumECR(Iterable<Node> enumNodes) {
		for(Node enumNode : enumNodes) {
			String id = enumNode.getString(0);
			IRVarInfo info = symbolTable.lookup(id);
			String scopeName = info.getScopeName();
			EnumeratorT enumType = info.getXtcType().toEnumerator();
			
	    Parent parent = Parent.getEmpty();
	    BlankType type = ValueType.blank(
	    		Size.createForType(enumType), parent, enumType, scopeName);
	    
	  	ECR enumECR = ECR.create(type);
	  	enumECRs.put(enumType, enumECR);
		}
	}
	
	/**
	 * Create region ECR for the expression <code>region</code>
	 * @param region
	 * @return
	 */
	ECR createForRegion(Expression region) {		
		Preconditions.checkNotNull(region.getNode());
		Node node = region.getNode();
		String name = node.getString(0);
		String scopeName = CType.getScopeName(node);
		Type type = CType.getType(node);
		
		VarImpl regionVar = VarImpl.createRegionVar(name, type, scopeName, region);
		uf.add(regionVar);
		ECR regionECR = regionVar.getECR();
		Pair<String, String> key = Pair.of(name, scopeName);
		assert(!ecrMap.containsKey(key));
		ecrMap.put(key, regionECR);
		return regionECR;
	}
	
	VarImpl createForStackVar(Expression lval) {
		Preconditions.checkNotNull(lval.getNode());
		Node node = lval.getNode();
		String name = node.getString(0);
		String scopeName = CType.getScopeName(node);
		Type type = CType.getType(node);
		
		if(type.resolve().isArray()) {
			Pair<VarImpl, VarImpl> pair = VarImpl.createForArraySymbol(name, type, scopeName, lval);
			uf.add(pair.fst());
			uf.add(pair.snd());
			return pair.fst();
		}
		
		if(type.resolve().isStruct() || type.resolve().isUnion()) {
			Pair<VarImpl, VarImpl> pair = VarImpl.createForStructOrUnionSymbol(name, type, scopeName, lval);
			uf.add(pair.fst());
			uf.add(pair.snd());
			return pair.fst();
		}
		
		VarImpl var = VarImpl.createForScalarSymbol(name, type, scopeName, lval);
		uf.add(var);
		return var;
	}
	
	private ECR createConstant(Type xtcType) {
		String scopeName = CScopeAnalyzer.getRootScopeName();
		ECR loc = ECR.createBottom();
		Function func = Function.getBottom();
    SimpleType type = ValueType.simple(
    		Pair.of(loc, Offset.createZero()), 
    		func, 
    		Size.createForType(xtcType), 
    		Parent.getEmpty(), 
    		xtcType,
    		scopeName);
    
  	ECR resECR = ECR.create(type);
  	loc.getType().setAddress(resECR);
		return resECR;
	}
	
	private String peekScopeKey(Scope scope) {
		if(Preferences.isSet(Preferences.OPTION_CONTEXT_SENSITIVE))
			return CScopeAnalyzer.peekScopeName(scope);
		else
			return scope.getQualifiedName();
	}

	private ECR createForSymbol(IRVarInfo info) {
		Type type = info.getXtcType().resolve();
		String scopeName = info.getScopeName();
		
		if(type.isArray()) 
			return createForArraySymbol(type, scopeName);
		
		if(type.isStruct() || type.isUnion())
			return createForStructOrUnionSymbol(type, scopeName);
		
		return createForScalarSymbol(type, scopeName);
	}

	/**
	 * Create an ECR with <code>xtcType</code>, <code>scopeName</code>.
	 * This method actually creates two ECRs: the ECR for the variable 
	 * and its address. If <code>xtcType</code> is compound, return 
	 * the address ECR, otherwise return the variable ECR.
	 * 
	 * @param xtcType
	 * @param scopeName
	 * @return
	 */
	private ECR createForScalarSymbol(Type xtcType, String scopeName) {		
	  BlankType varType = ValueType.blank(
	  		Size.createForType(xtcType), 
	  		Parent.getEmpty(), 
	  		xtcType, 
	  		scopeName);
	  
		ECR varECR = ECR.create(varType);
		
		Type addrXtcType = new PointerT(xtcType);
		SimpleType addrType = ValueType.simple(
				Pair.of(varECR, Offset.createZero()), 
				Function.getBottom(), 
				Size.createForType(addrXtcType), 
				Parent.getEmpty(), 
				addrXtcType, 
				scopeName);
		
		ECR addrECR = ECR.create(addrType);
		varType.setAddress(addrECR);
		return varECR;
	}
	
	private ECR createForArraySymbol(Type xtcType, String scopeName) {
		Preconditions.checkArgument(xtcType.resolve().isArray());
		
		Type cellType = CType.getArrayCellType(xtcType);
				
	  BlankType regionType = ValueType.blank(
	  		Size.createForType(cellType), 
	  		Parent.getEmpty(), 
	  		cellType, 
	  		scopeName);
	  
		ECR regECR = ECR.create(regionType);
		
		SimpleType varType = ValueType.simple(
				Pair.of(regECR, Offset.createZero()), 
				Function.getBottom(), 
				Size.createForType(xtcType), 
				Parent.getEmpty(), 
				xtcType, 
				scopeName);
		
		ECR varECR = ECR.create(varType);
		regionType.setAddress(varECR);
		varType.setAddress(varECR);
		return varECR;
	}
	
	private ECR createForStructOrUnionSymbol(Type xtcType, String scopeName) {
		Preconditions.checkArgument(xtcType.resolve().isStruct() ||
				xtcType.resolve().isUnion());
				
	  BlankType regionType = ValueType.blank(
	  		Size.createForType(xtcType), 
	  		Parent.getEmpty(), 
	  		xtcType, 
	  		scopeName);
	  
		ECR regECR = ECR.create(regionType);
		
		SimpleType varType = ValueType.simple(
				Pair.of(regECR, Offset.createZero()), 
				Function.getBottom(), 
				Size.createForType(xtcType), 
				Parent.getEmpty(), 
				xtcType, 
				scopeName);
		
		ECR varECR = ECR.create(varType);
		regionType.setAddress(varECR);
		varType.setAddress(varECR);
		
		return varECR;
	}

	/**
	 * For *a, if its <code>xtcType</code> is an array type,
	 * return the <code>ECR(a) = ecr</code>, otherwise return the 
	 * location of <code>ecr</code>
	 * @param ecr
	 * @param xtcType
	 * @return
	 */
	private ECR getLocECR(ECR ecr, Type xtcType) {
		if(xtcType.resolve().isArray()) return ecr;
		
		uf.ensureSimObj(ecr, uf.getType(ecr).getSize());
		ValueType type = uf.getType(ecr);
		assert(type.isSimple() || type.isObject());
		
		Pair<ECR, Offset> loc;
		if(type.isSimple()) {
			loc = type.asSimple().getLoc();
		} else {
			loc = type.asObject().getLoc();
		}
		
		ECR base = loc.fst();
		Offset off = loc.snd();
		uf.unlessZero(off, base);
		return base;
	}
	
	private ECR getAddrECR(ECR ecr) {
		Preconditions.checkArgument(uf.getType(ecr).hasAddress());
		return uf.getType(ecr).getAddress();
	}
	
	/**
	 * Get the ECR of <code>opNode</code> in the format as <code>op(a1, ..., an)</code>
	 * @param opNode
	 * @return
	 */
	private ECR getOpECR(Node node, Node lhsNode, Node rhsNode) {
  	long size = CType.getSizeofType(CType.getType(node));
		Size rangeSize = Size.create(size);
		
  	ECR leftECR = encodeECR(lhsNode);
  	ECR rightECR = encodeECR(rhsNode);
  	uf.cjoin(rangeSize, rightECR, leftECR);
  	
  	uf.ensureSimObj(leftECR, rangeSize);
  	ValueType type = uf.getType(leftECR);
  	
  	Pair<ECR, Offset> loc;
  	if(type.isSimple()) {
  		loc = type.asSimple().getLoc();
  	} else {
  		loc = type.asObject().getLoc();
  	}
  	
  	Offset off = loc.snd();
  	if(off.isZero()) uf.makeUnknown(off);
  	
  	return leftECR;
	}
	
	private ECR getComponent(ECR srcECR, Type baseXtcType, String fieldName) {
		uf.ensureSimObj(srcECR, uf.getType(srcECR).getSize());
		ValueType srcType = uf.getType(srcECR);
		
		Pair<ECR, Offset> pair;
		if(srcType.isSimple()) {
			pair = srcType.asSimple().getLoc();
		} else {
			pair = srcType.asObject().getLoc();
		}
		
		ECR base = pair.fst();
		Offset off = pair.snd();
		
		if(off.isUnknown()) {
			uf.collapse(base);
			return base;
		} 

		uf.unlessZero(off, base);
		ValueType baseType = uf.getType(base);
		
		switch(baseType.getKind()) {
		case BLANK: {
			Size size = Size.createForType(baseXtcType);
			if(!size.equals(baseType.getSize()))
				IOUtils.err().println("Incompatible blank size");
			
			String scopeName = baseType.getScopeName();
			StructType freshType = ValueType.struct(
					baseType.getSize(), 
					baseType.getParent(), 
					baseXtcType, 
					scopeName);
			freshType.setAddress(baseType.getAddress());
			uf.setType(base, freshType);
			Map<Long, ECR> mapping = freshType.getMapping();
			boolean compatible = uf.makeCompatible(base, baseXtcType, fieldName, mapping);
			assert compatible;
			long offset = CType.getOffset(baseXtcType, fieldName);
			return uf.getComponent(mapping, offset);
		}
		case STRUCT: {
			Map<Long, ECR> mapping = baseType.asStruct().getMapping();
			boolean compatible = uf.makeCompatible(base, baseXtcType, fieldName, mapping);
			if(!compatible) IOUtils.err().println("Not compatible");
			long offset = CType.getOffset(baseXtcType, fieldName);
			return uf.getComponent(mapping, offset);
		}
		case BOTTOM: {
			IOUtils.err().println("WARNING: component selection on bottom " + base);
			Pair<Pair<ECR, Offset>, Function> freshPair = uf.createBottomLocFunc(base);
			String scopeName = uf.getType(srcECR).getScopeName();
			Size size = Size.getLUB(baseType.getSize(), Size.createForType(baseXtcType));
			
			// Reset the xtcType, scope name, parent to the fresh type
			ValueType freshType = ValueType.object(
					freshPair.fst() ,
					freshPair.snd(),
					size,
					Parent.createParent(base),
					baseXtcType, 
					scopeName);
			freshType.setAddress(baseType.getAddress());
			uf.setType(base, freshType);
			return base;
		}
		case SIMPLE: {
			Size size = Size.createForType(baseXtcType);
			if(!Size.isLessThan(size, baseType.getSize()))
				IOUtils.err().println("Incompatible size");
			uf.promote(base, size);
			baseType = uf.getType(base); // refresh base type
			ObjectType promoteType = baseType.asObject();
			// Reset the parent, to the promoted type
			ValueType freshType = ValueType.object(
					promoteType.getLoc(), 
					promoteType.getFunc(), 
					promoteType.getSize(), 
					Parent.createParent(base), 
					promoteType.getXtcType(), 
					promoteType.getScopeName());
			freshType.setAddress(promoteType.getAddress());
			uf.setType(base, freshType);
			return base;
		}
		default: {
			Size size = Size.createForType(baseXtcType);
			if(!Size.isLessThan(size, baseType.getSize())) {
				IOUtils.err().println("Incompatible size");
				uf.promote(base, size);
			}
			baseType = uf.getType(base); // refresh base type
			ObjectType objType = baseType.asObject();
			// Reset the parent, to the promoted type
			ValueType freshType = ValueType.object(
					objType.getLoc(), 
					objType.getFunc(), 
					objType.getSize(), 
					Parent.createParent(base), 
					objType.getXtcType(), 
					objType.getScopeName());
			freshType.setAddress(objType.getAddress());
			uf.setType(base, freshType);
			return base;
		}
		}
	}
}
