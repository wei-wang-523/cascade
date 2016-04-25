/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steenscfscs;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.FunctionT;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.type.Type.Tag;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.PreProcessorException;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;
import edu.nyu.cascade.util.Triple;

public class ECREncoder extends Visitor {
  	
  private final UnionFindECR uf;
  private final SymbolTable symbolTable;
  private final CType cTypeAnalyzer = CType.getInstance();
  private final LvalVisitor lvalVisitor = new LvalVisitor();
  private final RvalVisitor rvalVisitor = new RvalVisitor();
  
	/**
   * Store all the ECRs created for declared variables with
   * their references names (variable names) and scope names
   */
  private final Map<Triple<String, String, String>, ECR> ecrMap = Maps.newHashMap();
  private final Map<Triple<GNode, String, String>, ECR> opECRMap = Maps.newHashMap();
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
  	
    private ECR encodeECR(Node node) {
      return (ECR) dispatch(node);
    }
    
    @Override
    public ECR unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as NULL: "
                  + node.getName());
      return ECR.createBottom();
    }
    
    public ECR visitAdditiveExpression(GNode node) {
    	return rvalVisitor.encodeECR(node);
    }
    
    public ECR visitSimpleDeclarator(GNode node) {
    	Preconditions.checkArgument(CType.hasScope(node));
    	String id = node.getString(0);
    	IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
    	String scopeName = varInfo.getScopeName();
    	Type type = varInfo.getXtcType();
    	
    	String currScope = CScopeAnalyzer.getCurrentScope();
    	Triple<String, String, String> key = Triple.of(id, scopeName, currScope);
    	if(ecrMap.containsKey(key)) return ecrMap.get(key);    	
    	
    	ECR addrECR = createECR(type);
  		ecrMap.put(key, addrECR);
  		
    	if(type.resolve().isFunction()) {
    		ECR varECR = deref(addrECR, type);
    		ECR lamECR = uf.getFunc(varECR);
    		VarImpl funcVar = new VarImpl(id, type, scopeName, lamECR);
    		uf.add(funcVar);
    	}
    	
    	return addrECR;
    }
    
    public ECR visitEnumerator(GNode node) {
    	String id = node.getString(0);
    	IRVarInfo info = symbolTable.lookup(id);
    	String scopeName = info.getScopeName();
    	
    	Triple<String, String, String> key =
    			Triple.of(id, scopeName, CScopeAnalyzer.getCurrentScope());
    	if(ecrMap.containsKey(key)) return ecrMap.get(key);
    	
    	ECR varECR = createECR(info.getXtcType());
    	ecrMap.put(key, varECR);
    	
    	return varECR;
    }
    
    public ECR visitIndirectionExpression(GNode node) {
    	return rvalVisitor.encodeECR(node.getNode(0));
    }
    
    public ECR visitIndirectComponentSelection(GNode node) {
    	Node baseNode = node.getNode(0);
      ECR baseECR = rvalVisitor.encodeECR(baseNode);
      Type baseType = CType.getType(baseNode).resolve().toPointer().getType();
      String fieldName = node.getString(1);
      return getComponent(baseECR, baseType, fieldName);
    }
    
    public ECR visitDirectComponentSelection(GNode node) {
    	Node baseNode = node.getNode(0);
      ECR baseECR = encodeECR(baseNode);
      Type baseType = CType.getType(baseNode);
      String fieldName = node.getString(1);
      return getComponent(baseECR, baseType, fieldName);
    }
    
    public ECR visitPrimaryIdentifier(GNode node) throws PreProcessorException {
    	Preconditions.checkArgument(CType.hasScope(node));
    	String id = node.getString(0);
    	IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
    	String scopeName = varInfo.getScopeName();
    	
    	Iterator<String> scopeItr = CScopeAnalyzer.getScopes().iterator();
    	while(scopeItr.hasNext()) {
    		String parentScope = scopeItr.next();
    		Triple<String, String, String> parentKey = Triple.of(id, scopeName, parentScope);
      	if(ecrMap.containsKey(parentKey))	return ecrMap.get(parentKey);
    	}
    	
    	// The return assign statement (lhs := rhs), while rhs belongs to the last scope
    	String lastScope = CScopeAnalyzer.getLastScope();
    	Triple<String, String, String> lastKey = Triple.of(id, scopeName, lastScope);
    	if(ecrMap.containsKey(lastKey))	return ecrMap.get(lastKey);
    	
    	throw new PreProcessorException("Invalid ECR");
    }
    
    public ECR visitSubscriptExpression(GNode node) {
    	ECR baseECR = rvalVisitor.encodeECR(node.getNode(0));
    	ECR idxECR = rvalVisitor.encodeECR(node.getNode(1));
    	return getOpECR(node, baseECR, idxECR);
    }
    
    public ECR visitIntegerConstant(GNode node) {
  		return getConstant();
    }
  }
  
  @SuppressWarnings("unused")
  private class RvalVisitor extends Visitor {
  	
    private ECR encodeECR(Node node) {
      return (ECR) dispatch(node);
    }
    
    @Override
    public ECR unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as NULL: "
                  + node.getName());
      return ECR.createBottom();
    }
    
    public ECR visitSimpleDeclarator(GNode node) {
    	ECR addrECR = lvalVisitor.encodeECR(node);
    	return deref(addrECR, CType.getType(node));
    }
    
    public ECR visitConditionalExpression(GNode node) {
    	Node lhsNode = node.getNode(1);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	uf.ccjoin(Size.getBot(), rhsECR, lhsECR);
    	return lhsECR;
    }

    public ECR visitAdditiveExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);

    	if(Preferences.isSet(Preferences.OPTION_CFS_POINTER_ARITH)) {
    		Type type = CType.getType(node);
      	if(type.resolve().isPointer()) {
      		//TODO: swap lhs and rhs if lhs is constant and rhs is pointer
      		Type lhsType = CType.getType(lhsNode);
      		Type rhsType = CType.getType(rhsNode);
      		if(lhsType.resolve().isPointer() && rhsType.hasConstant()) {
      			ECR resECR = createPointerECR(type);
      			Triple<GNode, String, String> key =
      					Triple.of(node, CType.getScopeName(node), CScopeAnalyzer.getCurrentScope());
      			opECRMap.put(key, resECR);
      			
      			long targetSize = cTypeAnalyzer.getSize(type.resolve().toPointer().getType());
      			long srcSize = cTypeAnalyzer.getSize(lhsType.resolve().toPointer().getType());
      			
      			long val = rhsType.getConstant().longValue();
      			boolean positive = "+".equals(node.getString(1));
      			long shift = (positive ? val : -val) * srcSize;
      			uf.ptrAri(resECR, targetSize, lhsECR, srcSize, shift);
      			return resECR;
      		}
      	}
    	}
    	
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    
    public ECR visitShiftExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    public ECR visitSubscriptExpression(GNode node) {
    	ECR addrECR = lvalVisitor.encodeECR(node);
    	return deref(addrECR, CType.getType(node));
    }
    
    public ECR visitFunctionCall(GNode node) {
    	Node funcNode = node.getNode(0);
    	String funcName = funcNode.getString(0);

    	Type returnType;
    	if(ReservedFunction.isReserved(funcName)) {
    		Sig signature = ReservedFunction.getSignature(funcName);
    		returnType = signature.getReturnType();
    	} else {
    		returnType = CType.getType(node);
    	}
    	
    	Size size = Size.createForType(returnType);
    	BlankType type = ValueType.blank(size, Parent.getBottom());
    	return ECR.create(type);
    }
    
    public ECR visitAddressExpression(GNode node) {
      return lvalVisitor.encodeECR(node.getNode(0));
    }

    public ECR visitAssignmentExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }

    public ECR visitBitwiseAndExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    public ECR visitBitwiseOrExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    public ECR visitBitwiseXorExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    public ECR visitBitwiseNegationExpression(GNode node) {
    	return encodeECR(node.getNode(0));
    }

    public ECR visitCastExpression(GNode node) {
    	Triple<GNode, String, String> key =
    			Triple.of(node, CType.getScopeName(node), CScopeAnalyzer.getCurrentScope());
    	if(opECRMap.containsKey(key)) return opECRMap.get(key);
    	
    	ECR srcECR = encodeECR(node.getNode(1));
    	Type srcType = CType.getType(node.getNode(1));
    	Type targetType = CType.getType(node);
    	ECR castECR = pointerCast(srcECR, srcType, targetType);
    	opECRMap.put(key, castECR);
    	return castECR;
    }
    
    public ECR visitCharacterConstant(GNode node) {
  		return getConstant();
    }

    public ECR visitEqualityExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);		
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	uf.ccjoin(Size.getBot(), rhsECR, lhsECR);
    	return getConstant();
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
      ECR addrECR = encodeECR(node.getNode(0));
      return deref(addrECR, CType.getType(node));
    }

    public ECR visitIntegerConstant(GNode node) {
  		return getConstant();
    }
    
    public ECR visitFloatingConstant(GNode node) {
  		return getConstant();
    }
    
    public ECR visitEnumerator(GNode node) {
    	return lvalVisitor.visitEnumerator(node);
    }

    public ECR visitLogicalAndExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return createECR(NumberT.INT);
    }

    public ECR visitLogicalNegationExpression(GNode node) {
      return encodeECR(node.getNode(0));
    }

    public ECR visitLogicalOrExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return createECR(NumberT.INT);
    }
    
    public ECR visitPreincrementExpression(GNode node) {
      ECR base = encodeECR(node.getNode(0));
      ECR intConstant = getConstant();
    	return getOpECR(node, base, intConstant);
    }

    public ECR visitPredecrementExpression(GNode node) {
      ECR base = encodeECR(node.getNode(0));
      ECR intConstant = getConstant();
    	return getOpECR(node, base, intConstant);
    }
    
    public ECR visitPostincrementExpression(GNode node) {
      ECR base = encodeECR(node.getNode(0));
      ECR intConstant = getConstant();
      return getOpECR(node, base, intConstant);
    }

    public ECR visitPostdecrementExpression(GNode node) {
      ECR base = encodeECR(node.getNode(0));
      ECR intConstant = getConstant();
      return getOpECR(node, base, intConstant);
    }
    
    public ECR visitPrimaryIdentifier(GNode node) {
    	String id = node.getString(0);
    	Scope scope = symbolTable.getScope(node);
			if(!scope.isDefined(id)) return getConstant();
			
    	IRVarInfo info = (IRVarInfo) scope.lookup(id);	
    	Type type = info.getXtcType();
    	if(type.isEnumerator()) return getConstant();
    	
    	ECR varECR = lvalVisitor.encodeECR(node);
    	return deref(varECR, type);
    }

    public ECR visitRelationalExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getConstant();
    }
    
  	public ECR visitStringConstant(GNode node) {
    	return getConstant();
    }
    
    public ECR visitSizeofExpression(GNode node) {
  		return getConstant();
    }
    
    public ECR visitUnaryMinusExpression(GNode node) {
      return encodeECR(node.getNode(0));
    }
    
    public ECR visitUnaryPlusExpression(GNode node) {
      return encodeECR(node.getNode(0));
    }
    
    public ECR visitMultiplicativeExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	ECR lhsECR = encodeECR(lhsNode);
    	ECR rhsECR = encodeECR(rhsNode);
    	return getOpECR(node, lhsECR, rhsECR);
    }
    
    public ECR visitDirectComponentSelection(GNode node) {
    	ECR addrECR = lvalVisitor.encodeECR(node);
    	return deref(addrECR, CType.getType(node));
    }
    
    public ECR visitIndirectComponentSelection(GNode node) {
    	ECR addrECR = lvalVisitor.encodeECR(node);
    	return deref(addrECR, CType.getType(node));
    }
  }
  
  private ECREncoder(UnionFindECR uf, SymbolTable symbolTable) {
  	this.uf = uf;
  	this.symbolTable = symbolTable;
  }
  
  static ECREncoder create(UnionFindECR uf, SymbolTable symbolTable) {
  	return new ECREncoder(uf, symbolTable);
  }
  
  ECR toRval(Node node) {
  	ECR ecr = rvalVisitor.encodeECR(node);
  	uf.addSourceECR(ecr);
  	return ecr;
  }

  ECR toLval(Node node) {
  	ECR ecr = lvalVisitor.encodeECR(node);
  	uf.addSourceECR(ecr);
  	return ecr;
  }
	
  Map<Triple<String, String, String>, ECR> getECRMap() {
  	return ecrMap;
  }
  
  Map<Triple<GNode, String, String>, ECR> getOpECRMap() {
  	return opECRMap;
  }
  
  /**
   * Get the lambda ECR created for <code>functionName</code>
   * @param functionName
   * @return
   */
  ECR getFunctionECR(String functionName) {
  	String rootScope = CScopeAnalyzer.getRootScopeName();
  	return ecrMap.get(Triple.of(functionName, rootScope, rootScope));
  }
	
	ValueType getLamdaType(Type type) {
		Preconditions.checkArgument(type.resolve().isFunction());
		FunctionT funcType = type.resolve().toFunction();
		List<ECR> paramECRs;
		if(!funcType.getParameters().isEmpty()) {
			int paramSize = funcType.getParameters().size();
			paramECRs = Lists.newArrayListWithCapacity(paramSize);
			for(int i = 0; i < paramSize; i++) {
				Type paramType = funcType.getParameters().get(i);
				ECR paramECR = deref(createECR(paramType), paramType);
				paramECRs.add(paramECR);
			}
		} else {
			paramECRs = Collections.<ECR>emptyList();
		}
		
		ECR retECR = ECR.createBottom();
		ValueType lambdaType = ValueType.lam(retECR, paramECRs, Parent.getBottom());
		return lambdaType;
	}
	
	private ECR deref(ECR ecr, Type type) {
		if(!(CType.isScalar(type) || type.resolve().isFunction())) return ecr;
		
		ECR locECR = uf.getLoc(ecr);
		if(type.resolve().isFunction()) return locECR;
		
		Size rangeSize = Size.createForType(type);
		Size locSize = uf.getType(locECR).getSize();
		if(locSize.isBottom()) uf.expand(locECR, rangeSize);
		return locECR;
	}

	private ECR getComponent(ECR srcECR, Type baseType, String fieldName) {	
		Preconditions.checkArgument(baseType.hasTag(Tag.STRUCT) || baseType.hasTag(Tag.UNION));
		long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
    Type fieldType = baseType.toStructOrUnion().lookup(fieldName);
		
		ECR loc = uf.getLoc(srcECR);
		ValueType locType = uf.getType(loc);
		
		if(fieldType.resolve().isArray())
			fieldType = CType.getArrayCellType(fieldType);
		
		if(locType.getSize().isTop()) {
			uf.ensureSimple(loc);
			locType = uf.getType(loc);
		}
		
		if(locType.isSimple()) {
			uf.expand(loc, Size.createForType(fieldType));
			return srcECR;
		}
		
		Size structSize = Size.createForType(baseType);
		ValueType structType = ValueType.struct(structSize, locType.getParent());
		
		locType = uf.unify(locType, structType); // Ensure locType is struct type
		// The type set to loc might not be locType. Since loc could be with bottom type
		// and associated with ccjoin or cjoin pending, the type change could trigger the
		// pending resolving process and would change the type set to loc (could be ref)
		uf.setType(loc, locType); 
		
		if(uf.getType(loc).isSimple()) {
			uf.expand(loc, Size.createForType(fieldType));
			return srcECR;
		}
		
		RangeMap<Long, ECR> fieldMap = locType.asStruct().getFieldMap();
		long size = cTypeAnalyzer.getSize(fieldType);
		Range<Long> range = Range.closedOpen(offset, offset + size);
		uf.normalize(loc, fieldType, range, fieldMap);
		return fieldMap.get(offset);
	}

	private ECR getConstant() {
		return ECR.createBottom();
	}
	
	private ECR createPointerECR(Type type) {
		Preconditions.checkArgument(type.resolve().isPointer());
		Type ptr2Type = type.resolve().toPointer().getType();
		BlankType blankType = ValueType.blank(Size.createForType(ptr2Type), Parent.getBottom());
		ECR blankECR = ECR.create(blankType);
		SimpleType refType = ValueType.simple(blankECR, ECR.createBottom(),
				Size.createForType(type), Parent.getBottom());
		ECR ptrECR = ECR.create(refType);
		return ptrECR;
	}
	
	private ECR createECR(Type type) {
		type = type.resolve();
		
		if(type.isFunction())	
			return createForFunction(type);
		
		Size size;
		if(type.isInternal()) {
			size = Size.getTop();
		} else if(CType.isScalar(type))	{
			size = Size.createForType(type);
		} else { // Composite type
			size = Size.getBot();
		}
		
		ValueType varType = ValueType.blank(size, Parent.getBottom());
		ECR varECR = ECR.create(varType);
		if(type.isInternal())	return varECR;
		
		SimpleType addrType = ValueType.simple(
				varECR, 
				ECR.createBottom(), 
				Size.createForType(new PointerT(type)), 
				Parent.getBottom());
		
		return ECR.create(addrType);
	}

	/**
	 * Create ECRs for function symbol: lambda ECR
	 */
	private ECR createForFunction(Type type) {		
		ValueType lambdaType = getLamdaType(type);
		ECR func = ECR.create(lambdaType);
		
		Size size = Size.createForType(new PointerT(type));
		
		ValueType varType = ValueType.simple(
				ECR.createBottom(), func, size, Parent.getBottom());
		ECR varECR = ECR.create(varType);
		
		SimpleType addrType = ValueType.simple(
				varECR, ECR.createBottom(), size, Parent.getBottom());
		return ECR.create(addrType);
	}

	/**
	 * Get the ECR of <code>op(leftECR, rightECR)</code>
	 * @param node
	 * @param leftECR
	 * @param rightECR
	 * @return
	 */
	private ECR getOpECR(GNode node, ECR leftECR, ECR rightECR) {
		String scopeName = CType.getScopeName(node);
  	Iterator<String> scopeItr = CScopeAnalyzer.getScopes().iterator();
  	while(scopeItr.hasNext()) {
  		String parentScope = scopeItr.next();
  		Triple<GNode, String, String> parentKey = Triple.of(node, scopeName, parentScope);
    	if(opECRMap.containsKey(parentKey))	return opECRMap.get(parentKey);
  	}
  	
  	// The return assign statement (lhs := rhs), while rhs belongs to the last scope
  	String lastScope = CScopeAnalyzer.getLastScope();
  	Triple<GNode, String, String> lastKey = Triple.of(node, scopeName, lastScope);
  	if(opECRMap.containsKey(lastKey))	return opECRMap.get(lastKey);
		
  	Triple<GNode, String, String> key = Triple.of(node, scopeName,
  			CScopeAnalyzer.getCurrentScope());
		ECR resECR = ECR.createBottom();
		opECRMap.put(key, resECR);
		
		uf.ccjoin(Size.getBot(), leftECR, resECR);
  	uf.ccjoin(Size.getBot(), rightECR, resECR);
  	
  	// Parent is stored at the points-to loc of 
  	if(Preferences.isSet(Preferences.OPTION_CFS_POINTER_ARITH)) return resECR;
  	
  	Parent parent = uf.getType(uf.getLoc(resECR)).getParent();
  	Collection<ECR> parentECRs = ImmutableList.copyOf(parent.getECRs());
  	
		for(ECR ecr : parentECRs) {
			ValueType ecrType = uf.getType(ecr);
			if(ecrType.isStruct())	
				uf.collapseStruct(ecr, ecrType.asStruct());
		}
  	
		uf.enableOp(uf.getLoc(resECR));
  	return resECR;
	}
	
  private ECR pointerCast(ECR srcECR, Type srcType, Type targetType) {
		if(!targetType.resolve().isPointer()) return srcECR;
		if(uf.getType(srcECR).isBottom()) return srcECR;
		
		ECR targetECR = createPointerECR(targetType);
		Type targetPtr2Type = targetType.resolve().toPointer().getType().resolve();
		long targetPtr2Size = targetPtr2Type.isVoid() ?
				0 : cTypeAnalyzer.getSize(targetPtr2Type);
		
		if(!Preferences.isSet(Preferences.OPTION_CFS_POINTER_ARITH)) {
			uf.smash(srcECR, targetECR, targetPtr2Size);
			return srcECR;
		}
		
		long srcPtr2Size = 0;
		if(srcType.resolve().isPointer()) {
			Type srcPtr2Type = srcType.resolve().toPointer().getType();
			if(!srcPtr2Type.isVoid()) {
				srcPtr2Size = cTypeAnalyzer.getSize(srcPtr2Type);
			}
		}

		if(uf.containsPtrAritJoin(srcECR, srcPtr2Size)) {
			/* Replace the one created for pointer arithmetic operations.
			 * Sample code: (typeof(*msg) *)((char *)__mptr - (size_t)&((typeof(*msg) *)0)->list)
			 */
			uf.replacePtrAriJoin(targetECR, targetPtr2Size, srcECR, srcPtr2Size);
		} else {
			uf.ptrCast(targetECR, targetPtr2Size, srcECR, srcPtr2Size);
		}
		return targetECR;
	}
}
