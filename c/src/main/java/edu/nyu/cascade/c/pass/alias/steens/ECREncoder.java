/**
 * 
 */
package edu.nyu.cascade.c.pass.alias.steens;

import java.util.List;
import java.util.Map;

import xtc.tree.*;
import xtc.type.FunctionT;
import xtc.type.Type;
import xtc.type.Type.Tag;
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
import edu.nyu.cascade.util.Pair;

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
  	
  private final UnionFindECR uf;
  private final SymbolTable symbolTable;
  private final CType cTypeAnalyzer = CType.getInstance();
  private final LvalVisitor lvalVisitor = new LvalVisitor();
  private final RvalVisitor rvalVisitor = new RvalVisitor();
  
  /**
   * Store all the ECRs created for declared variables with
   * their references names (variable names) and scope names
   */
  private final Map<Pair<String, String>, ECR> ecrMap = Maps.newHashMap();
  
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
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(ecrMap.containsKey(key)) return ecrMap.get(key);
    	
    	Type type = varInfo.getXtcType();
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
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(ecrMap.containsKey(key)) return ecrMap.get(key);
    	
    	ECR varECR = createECR(info.getXtcType());
    	ecrMap.put(key, varECR);
    	
    	return varECR;
    }
		
    public ECR visitIndirectionExpression(GNode node) {
    	return rvalVisitor.encodeECR(node.getNode(0));
    }
    
    public ECR visitPrimaryIdentifier(GNode node) {
    	Preconditions.checkArgument(CType.hasScope(node));
    	String id = node.getString(0);
    	IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
    	String scopeName = varInfo.getScopeName();
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(ecrMap.containsKey(key)) return ecrMap.get(key);
    	
    	Type type = varInfo.getXtcType();
    	ECR addrECR = createECR(type);
  		ecrMap.put(key, addrECR);
  		return addrECR;
    }
    
    public ECR visitSubscriptExpression(GNode node) {
    	ECR baseECR = rvalVisitor.encodeECR(node.getNode(0));
    	ECR idxECR = rvalVisitor.encodeECR(node.getNode(1));
    	long size = cTypeAnalyzer.getSize((CType.getType(node)));
    	return baseECR;
    }
    
    public ECR visitIntegerConstant(GNode node) {
			return getConstant();
    }
    
    public ECR visitIndirectComponentSelection(GNode node) {
      return rvalVisitor.encodeECR(node.getNode(0));
    }
    
    public ECR visitDirectComponentSelection(GNode node) {
    	Node baseNode = node.getNode(0);      
      ECR baseECR = encodeECR(baseNode);
      return baseECR;
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

		public ECR visitLabeledStatement(GNode node) {
			return ECR.createBottom();
		}

		public ECR visitConditionalExpression(GNode node) {
    	ECR lhsECR = encodeECR(node.getNode(1));
    	ECR rhsECR = encodeECR(node.getNode(2));
		  return getOpECR(lhsECR, rhsECR);
		}

		public ECR visitAdditiveExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(2));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitShiftExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(2));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitSubscriptExpression(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
			return deref(addrECR, CType.getType(node));
		}

		public ECR visitFunctionCall(GNode node) {
    	Type returnType = CType.getType(node);
    	return createECR(returnType);
		}

		public ECR visitAddressExpression(GNode node) {
		  return lvalVisitor.encodeECR(node.getNode(0));
		}

		public ECR visitAssignmentExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(2));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitBitwiseAndExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(1));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitBitwiseNegationExpression(GNode node) {
			return encodeECR(node.getNode(0));
		}

		public ECR visitBitwiseOrExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(1));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitBitwiseXorExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(1));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitCastExpression(GNode node) {
			return encodeECR(node.getNode(1));
		}

		public ECR visitCharacterConstant(GNode node) {
			return getConstant();
		}

		public ECR visitEqualityExpression(GNode node) {
    	ECR lhsECR = encodeECR(node.getNode(0));
    	ECR rhsECR = encodeECR(node.getNode(2));
    	getOpECR(lhsECR, rhsECR);
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

		public ECR visitLogicalAndExpression(GNode node) {
    	ECR lhsECR = encodeECR(node.getNode(0));
    	ECR rhsECR = encodeECR(node.getNode(2));
		  return getConstant();
		}

		public ECR visitLogicalNegationExpression(GNode node) {
		  return encodeECR(node.getNode(0));
		}

		public ECR visitLogicalOrExpression(GNode node) {
    	ECR lhsECR = encodeECR(node.getNode(0));
    	ECR rhsECR = encodeECR(node.getNode(2));
    	return getConstant();
		}

		public ECR visitPreincrementExpression(GNode node) {
		  ECR base = encodeECR(node.getNode(0));
		  return getOpECR(base, getConstant());
		}

		public ECR visitPredecrementExpression(GNode node) {
		  ECR base = encodeECR(node.getNode(0));
		  return getOpECR(base, getConstant());
		}

		public ECR visitPostincrementExpression(GNode node) {
		  ECR base = encodeECR(node.getNode(0));
		  return getOpECR(base, getConstant());
		}

		public ECR visitPostdecrementExpression(GNode node) {
		  ECR base = encodeECR(node.getNode(0));
		  return getOpECR(base, getConstant());
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
    	ECR lhsECR = encodeECR(node.getNode(0));
    	ECR rhsECR = encodeECR(node.getNode(2));
		  return getConstant();
		}

		public ECR visitStringConstant(GNode node) {
    	return getConstant();
		}

		public ECR visitSimpleDeclarator(GNode node) {
			ECR addrECR = lvalVisitor.encodeECR(node);
    	return deref(addrECR, CType.getType(node));
		}

		public ECR visitEnumerator(GNode node) {
			return lvalVisitor.visitEnumerator(node);
		}

		public ECR visitSizeofExpression(GNode node) {
			encodeECR(node.getNode(0));
			return getConstant();
		}

		public ECR visitUnaryMinusExpression(GNode node) {
		  return encodeECR(node.getNode(0));
		}

		public ECR visitUnaryPlusExpression(GNode node) {
		  return encodeECR(node.getNode(0));
		}

		public ECR visitMultiplicativeExpression(GNode node) {
			ECR leftECR = encodeECR(node.getNode(0));
			ECR rightECR = encodeECR(node.getNode(2));
			return getOpECR(leftECR, rightECR);
		}

		public ECR visitDirectComponentSelection(GNode node) {
		  ECR addrECR = lvalVisitor.encodeECR(node);
		  Type type = CType.getType(node);
			return deref(addrECR, type);
		}

		public ECR visitIndirectComponentSelection(GNode node) {
		  ECR addrECR = lvalVisitor.encodeECR(node);
		  Type type = CType.getType(node);
			return deref(addrECR, type);
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
  	return rvalVisitor.encodeECR(node);
  }

  ECR toLval(Node node) {
  	return lvalVisitor.encodeECR(node);
  }
  
  /**
   * Get the lambda ECR created for <code>functionName</code>
   * @param functionName
   * @return
   */
  ECR getFunctionECR(String functionName) {
  	return ecrMap.get(Pair.of(functionName, CScopeAnalyzer.getRootScopeName()));
  }
	
	void addStackVar(Expression lval, Node lvalNode) {
		Type type = CType.getType(lvalNode);
		switch(type.resolve().tag()) {
		case FUNCTION: createFuncVar(lval, lvalNode); break;
		case UNION:
		case INTEGER:
		case BOOLEAN:
		case POINTER:
		case FLOAT: createVar(lval, lvalNode); break;
		case ARRAY:
		case STRUCT: {
			createVar(lval, lvalNode);
			createRegionVar(lval, lvalNode);
			break;
		}
		default:
			throw new IllegalArgumentException("Unknown type " + type);
		}
	}

	/**
	 * Create region ECR for <code>region</code>
	 * @param region
	 * @param ptrNode
	 * @return
	 */
	void createRegionVar(Expression region, Node ptrNode) {
		String name = region.asVariable().getName();
		String scopeName = CType.getScopeName(ptrNode);
		ECR ptrECR = rvalVisitor.encodeECR(ptrNode);
		ECR regionECR = uf.findRoot(uf.getLoc(ptrECR));
		
		VarImpl regionVar = new VarImpl(name, VoidT.TYPE, scopeName, regionECR);
		uf.add(regionVar);
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
	ECR deref(ECR ecr, Type type) {
		Preconditions.checkNotNull(ecr);
		if(CType.isScalar(type) || type.resolve().isFunction()) return uf.getLoc(ecr);
	  return ecr;
	}

	ValueType getLamdaType(Type type) {
		Preconditions.checkArgument(type.resolve().isFunction());
		FunctionT funcType = type.resolve().toFunction();
		ECR retECR;
		if(Tag.VOID.equals(funcType.getResult().tag())) {
			retECR = ECR.createBottom();
		} else {
			retECR = createECR(funcType.getResult());
		}
		
		ValueType lambdaType;
		if(!funcType.getParameters().isEmpty()) {
			List<Type> params = funcType.getParameters();
			ECR[] paramECRs = new ECR[params.size()];
			for(int i = 0; i < params.size(); i++) {
				Type param = params.get(i);
				ECR paramECR = deref(createECR(param), param);
				paramECRs[i] = paramECR;
			}
			lambdaType = ValueType.lam(retECR, paramECRs);
		} else {
			lambdaType = ValueType.lam(retECR);
		}
		
		return lambdaType;
	}

	private void createVar(Expression lval, Node lvalNode) {
		String name = lval.asVariable().getName();
		String scopeName = CType.getScopeName(lvalNode);
		Type type = CType.getType(lvalNode);
		ECR lvalECR = rvalVisitor.encodeECR(lvalNode);
		VarImpl var = new VarImpl(name, type, scopeName, lvalECR);
		uf.add(var);
	}
	
	private void createFuncVar(Expression lval, Node lvalNode) {
		String name = lval.asVariable().getName();
		String scopeName = CType.getScopeName(lvalNode);
		Type type = CType.getType(lvalNode);
		Type ptrType = CType.getInstance().pointerize(type);
		ECR lvalECR = rvalVisitor.encodeECR(lvalNode);
		VarImpl var = new VarImpl(name, ptrType, scopeName, lvalECR);
		uf.add(var);
	}

	private ECR createECR(Type type) {
		if(type.resolve().isFunction())
			return createForFunction(type);
		
		ValueType refType = ValueType.ref(
				ECR.createBottom(), ECR.createBottom());
  	ECR varECR = ECR.create(refType);
		
		if(type.resolve().isInternal())	return varECR;
		
		ValueType addrType = ValueType.ref(varECR, 
  			ECR.createBottom());
		ECR addrECR = ECR.create(addrType);
		return addrECR;
	}
	
	private ECR getConstant() {
  	return ECR.createBottom();
	}
	
	/**
	 * Create ECRs for function symbol: lambda ECR
	 */
	private ECR createForFunction(Type type) {		
		ValueType lambdaType = getLamdaType(type);
		ECR func = ECR.create(lambdaType);		
		ECR loc = ECR.createBottom();
		ECR varECR = ECR.create(ValueType.ref(loc, func));
  	ECR addrECR = ECR.create(ValueType.ref(varECR, ECR.createBottom()));
		return addrECR;
	}

	/**
	 * Get the ECR in the format as <code>op(leftECR, rightECR)</code>
	 * @param leftECR
	 * @param rightECR
	 * @return
	 */
	private ECR getOpECR(ECR leftECR, ECR rightECR) {
		ECR resECR = ECR.createBottom();
		uf.assign(resECR, leftECR);
		uf.assign(resECR, rightECR);
		return resECR;
	}
}