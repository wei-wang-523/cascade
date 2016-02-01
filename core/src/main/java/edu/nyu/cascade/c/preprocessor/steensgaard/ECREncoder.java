/**
 * 
 */
package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.List;
import java.util.Map;

import xtc.tree.*;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.type.VoidT;
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
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

/**
 * The ECR encoder for Node. Return the ECR contained the left-value of the 
 * value of the node. 
 * 
 * Declare a variable: int a = 1;
 * ECR(Node(a)): contains the value addr_of_a;
 * ECR(Node(&a)): contains the value of addr_of_(addr_of_a);
 * 
 * Declare an array variable: int *p = malloc(5); // *p = region
 * ECR(Node(p)): contains the value addr_of_p;
 * ECR(Node(*p)): contains the value region;
 * ECR(Node(&p)): contains the value of addr_of_(addr_of_p);
 * 
 * @author weiwang
 *
 */

class ECREncoder extends Visitor {
	private static final Pair<String, String> CONST_ECR_KEY = Pair.of("ECR.constant", "");
  	
  private final UnionFindECR uf;
  private final SymbolTable symbolTable;
  
  /**
   * Store all the ECRs created for declared variables with
   * their references names (variable names) and scope names
   */
  private final Map<Pair<String, String>, ECR> ecrMap = Maps.newHashMap();
  
  private ECREncoder(UnionFindECR uf, SymbolTable symbolTable) {
  	this.uf = uf;
  	this.symbolTable = symbolTable;
  	ecrMap.put(CONST_ECR_KEY, newConstantECR());
  }
  
  static ECREncoder create(UnionFindECR uf, SymbolTable symbolTable) {
  	return new ECREncoder(uf, symbolTable);
  }
  
  void reset() {
  	ecrMap.clear();
  	ecrMap.put(CONST_ECR_KEY, newConstantECR());
  }
  
  ECR encodeECR(Node node) {
    ECR res = (ECR) dispatch(node);
    assert(res != null);
    return res;
  }
  
  @Override
  public ECR unableToVisit(Node node) throws VisitingException {
    IOUtils.err()
        .println(
            "APPROX: Treating unexpected node type as BOT: "
                + node.getName());
    return ECR.createBottom();
  }
  
  /* Do-nothing implementation to make errors from header files go away. */
  public ECR visitFunctionDeclarator(GNode node) {
    IOUtils.err()
    .println(
        "APPROX: Treating function declarator node type as BOT: "
            + node.getName());
    // TODO: Something
  	return ECR.createBottom();
  }
  
  public ECR visitConditionalExpression(GNode node) {
  	ECR bot = ECR.createBottom();
    ECR trueCase = encodeECR(node.getNode(1));
    ECR falseCase = encodeECR(node.getNode(2));
    uf.cjoin(bot, trueCase);
    uf.cjoin(bot, falseCase);
    return bot;
  }

  public ECR visitAdditiveExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
  }
  
  public ECR visitShiftExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
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
  	Type returnType = null;
  	
  	if(ReservedFunction.isReserved(funcName)) {
  		Sig signature = ReservedFunction.getSignature(funcName);
  		returnType = signature.getReturnType();
  	} else {
  		returnType = CType.getType(node);
  	}
  	
		return ECR.create(
				ValueType.ref(ECR.createBottom(), ECR.createBottom(), returnType, rootScope));
  }
  
  public ECR visitAddressExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    return getAddrECR(base);
  }

  public ECR visitAssignmentExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
  }

  public ECR visitBitwiseAndExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(1));
  }
  
  public ECR visitBitwiseNegationExpression(GNode node) {
  	return encodeECR(node.getNode(0));
  }
  
  public ECR visitBitwiseOrExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(1));
  }
  
  public ECR visitBitwiseXorExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(1));
  }

  public ECR visitCastExpression(GNode node) {
  	return encodeECR(node.getNode(1));
  }
  
  public ECR visitCharacterConstant(GNode node) {
    return getIntConstantECR();
  }

  public ECR visitEqualityExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
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
    Type type = CType.getType(node);
  	return getLocECR(baseECR, type);
  }

  public ECR visitIntegerConstant(GNode node) {
  	return getIntConstantECR();
  }
  
  public ECR visitFloatingConstant(GNode node) {
  	return getFloatConstantECR();
  }

  public ECR visitLogicalAndExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(1));
  }

  public ECR visitLogicalNegationExpression(GNode node) {
    return encodeECR(node.getNode(0));
  }

  public ECR visitLogicalOrExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(1));
  }

  public ECR visitPreincrementExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    uf.cjoin(base, getIntConstantECR());
    return base;
  }

  public ECR visitPredecrementExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    uf.cjoin(base, getIntConstantECR());
    return base;
  }
  
  public ECR visitPostincrementExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    uf.cjoin(base, getIntConstantECR());
    return base;
  }

  public ECR visitPostdecrementExpression(GNode node) {
    ECR base = encodeECR(node.getNode(0));
    uf.cjoin(base, getIntConstantECR());
    return base;
  }
  
  public ECR visitPrimaryIdentifier(GNode node) {
  	String id = node.getString(0);
  	String scopeName = CType.getScopeName(node);
  	Scope currScope = symbolTable.getScope(scopeName);
  	
  	Scope scope = currScope.isDefined(id) ? // region is not defined under scope
  			currScope.lookupScope(id) : currScope;
  	
  	Pair<String, String> key = Pair.of(id, scope.getQualifiedName());
  	if(ecrMap.containsKey(key)) return ecrMap.get(key);
  	
  	IRVarInfo info = (IRVarInfo) scope.lookup(id);
  	Type type = info.getXtcType();
  	
  	if(type.isEnumerator()) return getIntConstantECR();
    
		assert(info.hasProperty(Identifiers.CTRLVAR));
  	VarImpl freshVar = VarImpl.createCtrlSymbol(info);
    ECR freshECR = freshVar.getECR();
    uf.add(freshVar);
    ecrMap.put(key, freshECR);
  	return freshECR;
  }

  public ECR visitRelationalExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
  }

  public ECR visitSimpleDeclarator(GNode node) {
  	String id = node.getString(0);
  	String scopeName = CType.getScopeName(node);
  	Scope currScope = symbolTable.getScope(scopeName);
  	
  	Scope scope = currScope.isDefined(id) ? // region is not defined under scope
  			currScope.lookupScope(id) : currScope;
  	
  	Pair<String, String> key = Pair.of(id, scope.getQualifiedName());
  	if(ecrMap.containsKey(key)) return ecrMap.get(key);
  	
  	IRVarInfo info = (IRVarInfo) scope.lookup(id);  	
  	ECR varECR = createForSymbol(info);
		ecrMap.put(key, varECR);
  	return varECR;
  }
  
  public ECR visitEnumerator(GNode node) {
  	String id = node.getString(0);
  	String scopeName = CType.getScopeName(node);
  	Scope scope = symbolTable.getScope(scopeName);
  	
  	Pair<String, String> key = Pair.of(id, scope.getQualifiedName());
  	if(ecrMap.containsKey(key)) return ecrMap.get(key);
  	
  	IRVarInfo info = (IRVarInfo) scope.lookup(id);
  	ECR varECR = createForSymbol(info);
  	ecrMap.put(key, varECR);
  	
  	return varECR;
  }

  public ECR visitStringConstant(GNode node) {
  	return getIntConstantECR();
  }
  
  public ECR visitSizeofExpression(GNode node) {
  	return getIntConstantECR();
  }
  
  public ECR visitUnaryMinusExpression(GNode node) 
      throws VisitingException {
    return encodeECR(node.getNode(0));
  }
  
  public ECR visitUnaryPlusExpression(GNode node) 
      throws VisitingException {
    return encodeECR(node.getNode(0));
  }
  
  public ECR visitMultiplicativeExpression(GNode node) {
  	return getOpECR(node.getNode(0), node.getNode(2));
  }
  
  public ECR visitDirectComponentSelection(GNode node) {
    ECR baseECR = getAddrECR(encodeECR(node.getNode(0)));
    Type type = CType.getType(node);
  	return getLocECR(baseECR, type);
  }
  
  public ECR visitIndirectComponentSelection(GNode node) {
    ECR baseECR = encodeECR(node.getNode(0));
    Type type = CType.getType(node);
  	return getLocECR(baseECR, type);
  }
	
	VarImpl createForStackVar(Expression lval, Node lvalNode) {
		String name = lvalNode.getString(0);
		String scopeName = CType.getScopeName(lvalNode);
		Type type = CType.getType(lvalNode);
		Type cleanType = type.resolve();
		
		if(cleanType.isStruct() || cleanType.isUnion()) {
			Pair<VarImpl, VarImpl> pair = VarImpl.createForStructOrUnionSymbol(name, type, scopeName, lval);
			VarImpl stackVar = pair.fst();
			VarImpl regVar = pair.snd();
			uf.add(stackVar);
			uf.add(regVar);
			return stackVar;
		}
		
		if(cleanType.isArray()) {
			Pair<VarImpl, VarImpl> pair = VarImpl.createForArraySymbol(name, type, scopeName, lval);
			VarImpl stackVar = pair.fst();
			VarImpl regVar = pair.snd();
			uf.add(stackVar);
			uf.add(regVar);
			return stackVar;
		}
		
		VarImpl stackVar = VarImpl.createForScalarSymbol(name, type, scopeName, lval);
		uf.add(stackVar);
		return stackVar;
	}

	/**
	 * Create region ECR for <code>region</code>
	 * @param region
	 * @param ptrNode
	 * @return
	 */
	ECR createForRegion(Expression region, Node ptrNode) {
		String name = region.asVariable().getName();
		String scopeName = CType.getScopeName(ptrNode);
		
		VarImpl regionVar = VarImpl.createRegionVar(name, VoidT.TYPE, scopeName, region);
		uf.add(regionVar);
		ECR regionECR = regionVar.getECR();
		Pair<String, String> key = Pair.of(name, scopeName);
		assert(!ecrMap.containsKey(key));
		ecrMap.put(key, regionECR);
		return regionECR;
	}

	ECR getNullPtrECR() {
		return ecrMap.get(CONST_ECR_KEY);
	}

	/**
	 * For *a, if <code>typeof(*a)</code> is an array type. The array
	 * element defined in the array or structure, when we access it 
	 * via <code>f.a</code> or <code>f[0]</coe>, we are in the same 
	 * alias group as <code>f</code>.
	 * @param ecr
	 * @param srcType
	 * @return
	 */
	ECR getLocECR(ECR ecr, Type srcType) {
		if(srcType.resolve().isArray()) return ecr;
		
		ValueType valueType = uf.getType(ecr);
		if(valueType.isBot()) {
			IOUtils.err().println("WARNING: get Loc of " + ecr.toStringShort());
			return getNullPtrECR();
		}
		
	  return uf.getType(ecr).asRef().getLocation();
	}

	private ECR createForSymbol(IRVarInfo info) {
		Type type = info.getXtcType();
		String scopeName = info.getScopeName();
		
		ECR resECR;
		if(type.resolve().isArray()) {
			resECR = createForArraySymbol(type, scopeName);
		} else if(type.resolve().isStruct() || type.resolve().isUnion()) {
			resECR = createForStructOrUnionSymbol(type, scopeName);
		} else {
			resECR = createForScalarSymbol(type, scopeName);
		}
		return resECR;
	}
	
	/**
	 * Create ECRs for array symbol: region ECR and variable ECR
	 * 
	 * @param type
	 * @param scopeName
	 * @return variable ECR
	 */
	private ECR createForArraySymbol(Type type, String scopeName) {
		Preconditions.checkArgument(type.resolve().isArray());
		
		ECR regLoc = ECR.createBottom();
		ECR regFunc = ECR.createBottom();
		
		ValueType regType = ValueType.ref(
				regLoc, regFunc, CType.getCellType(type), scopeName);
		ECR regECR = ECR.create(regType);
		
		regLoc.getType().setAddress(regECR);
		regFunc.getType().setAddress(regECR);
		
		ECR loc = regECR;
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, type, scopeName);
  	ECR varECR = ECR.create(refType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
  	refType.setAddress(varECR);
  	
    return varECR;
	}
	
	/**
	 * Create ECRs for struct or union symbol: region ECR, variable ECR
	 * 
	 * @param type
	 * @param scopeName
	 * @return variable ECR
	 */
	private ECR createForStructOrUnionSymbol(Type type, String scopeName) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
		
		ECR regLoc = ECR.createBottom();
		ECR regFunc = ECR.createBottom();
		
		ValueType regType = ValueType.ref(
				regLoc, regFunc, CType.getCellType(type), scopeName);
		ECR regECR = ECR.create(regType);
		
		regLoc.getType().setAddress(regECR);
		regFunc.getType().setAddress(regECR);
		
		ECR loc = regECR;
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, type, scopeName);
  	ECR varECR = ECR.create(refType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
  	
  	refType.setAddress(varECR);
  	
    return varECR;
	}
	
	/**
	 * Create ECRs for scalar symbol: variable ECR and addr ECR
	 * @param xtcType
	 * @param scopeName
	 * @return variable ECR
	 */
	private ECR createForScalarSymbol(Type xtcType, String scopeName) {
		ECR loc = ECR.createBottom();
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, xtcType, scopeName);
  	ECR varECR = ECR.create(refType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
    
  	Type addrXtcType = new PointerT(xtcType);
    // For scalar type variable, set the address
  	ECR addrECR = ECR.create(ValueType.ref( varECR, ECR.createBottom(), 
  			addrXtcType, scopeName));
  	varECR.getType().setAddress(addrECR);
  	
  	return varECR;
	}
	
	/**
	 * Create constant ECR with root scope
	 * @return
	 */
	private ECR newConstantECR() {
		String scopeName = CScopeAnalyzer.getRootScopeName();		
    ECR loc = ECR.createBottom(); 
    ECR func = ECR.createBottom();
    
    ValueType type = ValueType.ref(loc, func, VoidT.TYPE, scopeName);
  	ECR constECR = ECR.create(type);
  	
  	loc.getType().setAddress(constECR);
  	func.getType().setAddress(constECR);
		return constECR;
	}

	/**
	 * Get the ECR in the format as <code>op(lhsNode, rhsNode)</code>
	 * @param lhsNode
	 * @param rhsNode
	 * @return
	 */
	private ECR getOpECR(Node lhsNode, Node rhsNode) {
		ECR leftECR = encodeECR(lhsNode);
		ECR rightECR = encodeECR(rhsNode);
		ValueType leftType = uf.getType(leftECR);
		ValueType rightType = uf.getType(rightECR);
		
		if(leftType.isBot() || rightType.isBot()) {
			IOUtils.err().println("WARNING: get Op of " + leftECR + ", " + rightECR);
			return leftECR;
		}
		
		ECR leftLoc = leftType.asRef().getLocation();
		ECR leftFunc = leftType.asRef().getFunction();
		ECR rightLoc = rightType.asRef().getLocation();
		ECR rightFunc = rightType.asRef().getFunction();
		
		uf.cjoin(leftLoc, rightLoc);
		uf.cjoin(leftFunc, rightFunc);
		return leftECR;
	}
	
	private ECR getIntConstantECR() {
		return ecrMap.get(CONST_ECR_KEY);
	}
	
	private ECR getFloatConstantECR() {
		return ecrMap.get(CONST_ECR_KEY);
	}

	/**
	 * For &a, if the type of node a -- <code>baseType</code> is an array
	 * type, return the <code>ECR(a) = ecr</code>, otherwise return the 
	 * address ECR of <code>ecr</code>
	 * @param ecr
	 * @param baseType
	 * @return
	 */
	private ECR getAddrECR(ECR ecr) {
	  return uf.getType(ecr).getAddress();
	}
}