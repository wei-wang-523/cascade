/**
 * 
 */
package edu.nyu.cascade.c.preprocessor.cfs;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.VisitingException;
import xtc.tree.Visitor;
import xtc.type.FunctionT;
import xtc.type.PointerT;
import xtc.type.Type;
import xtc.type.Type.Tag;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessorException;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.ReservedFunction;
import edu.nyu.cascade.util.ReservedFunction.Sig;

class CellEncoder extends Visitor {
  
  private final SymbolTable symbolTable;
  private final CType cTypeAnalyzer = CType.getInstance();
  private final CellManager cellManager;
  private final CFPGraphManager graphManager;
  
  private final LvalVisitor lvalVisitor = new LvalVisitor();
  private final RvalVisitor rvalVisitor = new RvalVisitor();
	private final long ptrSize = cTypeAnalyzer.getSize(PointerT.TO_VOID);
  
  /**
   * Store cells created for declared variables, functions and enumerators
   * with their references names (variable names) and scope names.
   */
  private final Map<Pair<String, String>, Cell> leftCellMap = 
  		Maps.newHashMap();
  /**
   * Cache all the cell created for operation node.
   */
  private final Map<Pair<GNode, String>, Cell> opCellMap =
  		Maps.newHashMap();
  
  @SuppressWarnings("unused")
  private class LvalVisitor extends Visitor {
  	
    private Cell encodeCell(Node node) {
      Cell resCell = (Cell) dispatch(node);
      return resCell;
    }
    
    @Override
    public Cell unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as NULL: "
                  + node.getName());
      return cellManager.bottom();
    }
    
    public Cell visitAdditiveExpression(GNode node) {
    	return rvalVisitor.encodeCell(node);
    }
    
    /**
     * Both l-cell and r-cell of declared variable are created.
     * Store (r-cell, l-cell) into the addrCellMap.
     * Store r-cell and the variable's identifier and scopeName into the varCellMap.
     * Return the l-cell of the declared variable. 
     * @param node
     * @return
     */
    public Cell visitSimpleDeclarator(GNode node) {
    	Preconditions.checkArgument(CType.hasScope(node));
    	String id = node.getString(0);
    	IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
    	String scopeName = varInfo.getScopeName();
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(leftCellMap.containsKey(key)) {
    		return leftCellMap.get(key);
    	} else {
    		Type type = varInfo.getXtcType();
    		Cell cell = cellManager.createCell(type);
    		Cell addrCell = cellManager.scalar(ptrSize);
    		graphManager.addPointsEdge(addrCell, cell);
  		
    		leftCellMap.put(key, addrCell);
    		return addrCell;
    	}
    }
    
    /**
     * For enumerator, just create a r-cell (no l-cell).
     * Store r-cell and the enumerator's identifier and scopeName into varCellMap.
     * Note that no l-cell is created in this case since enumerator is a constant
     * value not variable.
     * @param node
     * @return
     */
    public Cell visitEnumerator(GNode node) {
    	String id = node.getString(0);
    	IRVarInfo info = symbolTable.lookup(id);
    	String scopeName = info.getScopeName();
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(leftCellMap.containsKey(key)) {
    		return leftCellMap.get(key);
    	} else {
      	Cell cell = cellManager.createCell(info.getXtcType());
      	leftCellMap.put(key, cell);
      	return cell;
    	}
    }
    
    public Cell visitIndirectionExpression(GNode node) {
    	return rvalVisitor.encodeCell(node.getNode(0));
    }
    
    public Cell visitIndirectComponentSelection(GNode node) {
    	Pair<GNode, String> key = Pair.of(node, CType.getScopeName(node));
    	if(opCellMap.containsKey(key)) {
    		return opCellMap.get(key);
    	} else {
      	Node baseNode = node.getNode(0);
      	// basePtrCell is a cell that points to the struct/union cell 
      	Cell basePtrCell = rvalVisitor.encodeCell(baseNode);
      	Cell baseCell = graphManager.getPointsCell(basePtrCell);
      	Type baseType = CType.getType(baseNode).resolve().toPointer().getType();
      	String fieldName = node.getString(1);
      	Type fieldType = CType.getType(node);
      	long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
      	Cell fieldAddrCell = getFieldAddrCell(baseCell, fieldType, offset);
      	opCellMap.put(key, fieldAddrCell);
      	return fieldAddrCell;
    	}
    }
      
    public Cell visitDirectComponentSelection(GNode node) {
    	Pair<GNode, String> key = Pair.of(node, CType.getScopeName(node));
    	if(opCellMap.containsKey(key)) {
    		return opCellMap.get(key);
    	} else {
      	Node baseNode = node.getNode(0);
      	// basePtrCell is a cell that points to the struct/union cell 
      	Cell basePtrCell = encodeCell(baseNode);  
      	Cell baseCell = graphManager.getPointsCell(basePtrCell);
      	Type baseType = CType.getType(baseNode).resolve();
      	String fieldName = node.getString(1);
      	long offset = cTypeAnalyzer.getOffset(baseType, fieldName);
      	Type fieldType = CType.getType(node);
      	Cell fieldAddrCell = getFieldAddrCell(baseCell, fieldType, offset);
      	opCellMap.put(key, fieldAddrCell);
      	return fieldAddrCell;
    	}
    }
    
    public Cell visitPrimaryIdentifier(GNode node) {
    	Preconditions.checkArgument(CType.hasScope(node));
    	String id = node.getString(0);
    	IRVarInfo varInfo = (IRVarInfo) symbolTable.getScope(node).lookup(id);
    	String scopeName = varInfo.getScopeName();
    	
    	Pair<String, String> key = Pair.of(id, scopeName);
    	if(leftCellMap.containsKey(key)) {
    		return leftCellMap.get(key);
    	} else {
    		Type type = varInfo.getXtcType();
    		Cell cell = cellManager.createCell(type);
    		Cell addrCell = cellManager.scalar(ptrSize);
    		graphManager.addPointsEdge(addrCell, cell);
  		
    		leftCellMap.put(key, addrCell);
    		return addrCell;
    	}
    }
    
    public Cell visitSubscriptExpression(GNode node) {
    	Node baseNode = node.getNode(0);
    	Node idxNode = node.getNode(1);
    	Type baseType = CType.getType(baseNode);
    	Type idxType = CType.getType(idxNode);
    	
    	Cell baseCell = rvalVisitor.encodeCell(baseNode);
    	
    	// If the subscript expression is a valid array access, then return
    	// the baseCell and avoid collapsing the container of the array.
    	if(isValidArrayAccess(baseType, idxType)) {
    		return baseCell;
    	}
    	
    	Pair<GNode, String> key = Pair.of(node, CType.getScopeName(node));
    	if(opCellMap.containsKey(key)) return opCellMap.get(key);
    	
    	// Pointerize array type and convert the subscript operator as
    	// pointer arithmetic: a[i] = &a + i. The l-type of a[i] is a 
    	// pointerized type of the array type of a.
    	Type baseTypePrime = cTypeAnalyzer.pointerize(baseType);
    	Type idxTypePrime = cTypeAnalyzer.pointerize(idxType);
    	Type opType = cTypeAnalyzer.convert(baseTypePrime, idxTypePrime);
    	
    	Cell idxCell = rvalVisitor.encodeCell(idxNode);
    	Cell opCell = cellManager.createCell(opType);
    	ccjoin(idxCell, opCell);
    	ccjoin(baseCell, opCell);
    	
  		// Pointer arithmetic operations
  		pointerOperation(opCell);
  		opCellMap.put(key, opCell);
  		return opCell;
    }

		/**
		 * Valid array access if baseType is an array type, idxType is with
		 * constant and the constant value is within the size of the array type.
		 */
		private boolean isValidArrayAccess(Type baseType, Type idxType) {
			if(!baseType.resolve().isArray()) return false;
			if(!idxType.hasConstant()) return false;
			long bound = baseType.resolve().toArray().getLength();
			long idx = idxType.getConstant().longValue();
			return bound > idx && idx >= 0;
		}
  }
  
  @SuppressWarnings("unused")
  private class RvalVisitor extends Visitor {
  	
    private Cell encodeCell(Node node) {
        Cell resCell = (Cell) dispatch(node);
        return resCell;
    }
    
    @Override
    public Cell unableToVisit(Node node) throws VisitingException {
      IOUtils.err()
          .println(
              "APPROX: Treating unexpected node type as NULL: "
                  + node.getName());
      return cellManager.bottom();
    }
    
    public Cell visitSimpleDeclarator(GNode node) {
    	Cell addrCell = lvalVisitor.encodeCell(node);
    	Type type = CType.getType(node);
    	return deref(addrCell, type);
    }
    
    public Cell visitConditionalExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(1);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	
    	Pair<GNode, String> key = Pair.of(node, CType.getScopeName(node));
    	if(opCellMap.containsKey(key))  return opCellMap.get(key);
    	
    	Type type = CType.getType(node).resolve();
    	Cell condCell = cellManager.createCell(type);
    	ccjoin(rhsCell, condCell);
    	ccjoin(lhsCell, condCell);
    	opCellMap.put(key, condCell);
    	return condCell;
    }

    public Cell visitAdditiveExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitShiftExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitSubscriptExpression(GNode node) {
    	Cell addrCell = lvalVisitor.encodeCell(node);
    	Type type = CType.getType(node);
    	return deref(addrCell, type);
    }
    
    public Cell visitFunctionCall(GNode node) {
    	Node funcNode = node.getNode(0);
    	String funcName = funcNode.getString(0);

    	Type returnType;
    	if(ReservedFunction.isReserved(funcName)) {
    		Sig signature = ReservedFunction.getSignature(funcName);
    		returnType = signature.getReturnType();
    	} else {
    		returnType = CType.getType(node);
    	}
    	
    	// TODO: find the return cell of the function cell of funcName
    	return cellManager.createCell(returnType);
    }
    
    public Cell visitAddressExpression(GNode node) {
      return lvalVisitor.encodeCell(node.getNode(0));
    }

    public Cell visitAssignmentExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	ccjoin(rhsCell, lhsCell);
    	return rhsCell;
    }

    public Cell visitBitwiseAndExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitBitwiseOrExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitBitwiseXorExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitBitwiseNegationExpression(GNode node) {
    	return encodeCell(node.getNode(0));
    }

    public Cell visitCastExpression(GNode node) {
    	Pair<GNode, String> key = Pair.of(node, CType.getScopeName(node));
    	if(opCellMap.containsKey(key)) return opCellMap.get(key);
    	
    	Cell srcCell = encodeCell(node.getNode(1));
    	Type targetType = CType.getType(node);
    	Cell resCell = cast(srcCell, targetType);
			opCellMap.put(key, resCell);
    	return resCell;
    }
    
    public Cell visitCharacterConstant(GNode node) {
  		return getConstant();
    }

    public Cell visitEqualityExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);		
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	ccjoin(rhsCell, lhsCell);
    	return getConstant();
    }

    public List<Cell> visitExpressionList(GNode node) {
      List<Cell> subCellList = Lists.newArrayListWithCapacity(node.size());
      for (Object elem : node) {
        Cell subCell = encodeCell(GNode.cast(elem));
        subCellList.add(subCell);
      }
      return subCellList;
    }

    public Cell visitIndirectionExpression(GNode node) {
    	Cell addrCell = encodeCell(node.getNode(0));
    	return graphManager.getPointsCell(addrCell);
    }

    public Cell visitIntegerConstant(GNode node) {
    	return getConstant();
    }
    
    public Cell visitFloatingConstant(GNode node) {
  		return getConstant();
    }
    
    public Cell visitEnumerator(GNode node) {
    	return lvalVisitor.encodeCell(node);
    }

    public Cell visitLogicalAndExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return cellManager.bottom();
    }

    public Cell visitLogicalNegationExpression(GNode node) {
      return encodeCell(node.getNode(0));
    }

    public Cell visitLogicalOrExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(1);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return cellManager.bottom();
    }
    
    public Cell visitPreincrementExpression(GNode node)
    		{
      Cell base = encodeCell(node.getNode(0));
      Cell intConstant = getConstant();
    	return getOpCell(node, base, intConstant);
    }

    public Cell visitPredecrementExpression(GNode node)
    		{
      Cell base = encodeCell(node.getNode(0));
      Cell intConstant = getConstant();
    	return getOpCell(node, base, intConstant);
    }
    
    public Cell visitPostincrementExpression(GNode node)
    		{
      Cell base = encodeCell(node.getNode(0));
      Cell intConstant = getConstant();
      return getOpCell(node, base, intConstant);
    }

    public Cell visitPostdecrementExpression(GNode node)
    		{
      Cell base = encodeCell(node.getNode(0));
      Cell intConstant = getConstant();
      return getOpCell(node, base, intConstant);
    }
    
    public Cell visitPrimaryIdentifier(GNode node) {
    	String id = node.getString(0);
    	Scope scope = symbolTable.getScope(node);
    	if(!scope.isDefined(id)) {
    		IOUtils.errPrinter().pln("ECREncoder: undefined id " + id);
    		return getConstant();
    	}
    	
    	IRVarInfo info = (IRVarInfo) scope.lookup(id);	
    	Type type = info.getXtcType();
    	if(type.isEnumerator()) {
    		return getConstant();
    	}
    	
    	Cell addrCell = lvalVisitor.encodeCell(node);
    	return deref(addrCell, type);
    }

    public Cell visitRelationalExpression(GNode node) {
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getConstant();
    }
    
  	public Cell visitStringConstant(GNode node) {
    	return getConstant();
    }
    
    public Cell visitSizeofExpression(GNode node) {
  		return getConstant();
    }
    
    public Cell visitUnaryMinusExpression(GNode node) {
      return encodeCell(node.getNode(0));
    }
    
    public Cell visitUnaryPlusExpression(GNode node) {
      return encodeCell(node.getNode(0));
    }
    
    public Cell visitMultiplicativeExpression(GNode node)
    		{
    	Node lhsNode = node.getNode(0);
    	Node rhsNode = node.getNode(2);
    	Cell lhsCell = encodeCell(lhsNode);
    	Cell rhsCell = encodeCell(rhsNode);
    	return getOpCell(node, lhsCell, rhsCell);
    }
    
    public Cell visitDirectComponentSelection(GNode node) {
    	Cell addrCell = lvalVisitor.encodeCell(node);
    	Type type = CType.getType(node);
    	return deref(addrCell, type);
    }
    
    public Cell visitIndirectComponentSelection(GNode node) {
    	Cell addrCell = lvalVisitor.encodeCell(node);
    	Type type = CType.getType(node);
    	return deref(addrCell, type);
    }
  }
  
  private CellEncoder(SymbolTable symbolTable, CellManager cellManager,
  		CFPGraphManager graphManager) {
	  this.symbolTable = symbolTable;
	  this.cellManager = cellManager;
	  this.graphManager = graphManager;
  }
  
  public static CellEncoder create(SymbolTable symbolTable,
  		CellManager cellManager, CFPGraphManager graphManager) {
	  return new CellEncoder(symbolTable, cellManager, graphManager);
  }
  
  Cell toRval(Node node) {
	  return rvalVisitor.encodeCell(node);
  }

  public Cell toLval(Node node) {
	  return lvalVisitor.encodeCell(node);
  }
	
  Map<Pair<String, String>, Cell> getLeftCellMap() {
	  return leftCellMap;
  }
  
  Map<Pair<GNode, String>, Cell> getOpCellMap() {
  	return opCellMap;
  }
  
  /**
   * Get the lambda Cell created for <code>functionName</code>
   * @param functionName
   * @return
   */
  Cell getFunctionCell(String functionName) {
  	return leftCellMap.get(Pair.of(functionName, CScopeAnalyzer.getRootScopeName()));
  }
	
	Cell getLamdaType(Type type) {
		Preconditions.checkArgument(type.resolve().isFunction());
		FunctionT funcType = type.resolve().toFunction();
		List<Cell> paramCells;
		if(!funcType.getParameters().isEmpty()) {
			int paramSize = funcType.getParameters().size();
			paramCells = Lists.newArrayListWithCapacity(paramSize);
			for(int i = 0; i < paramSize; i++) {
				Type paramType = funcType.getParameters().get(i);
				Cell paramCell = cellManager.createCell(paramType);
				paramCells.add(paramCell);
			}
		} else {
			paramCells = Collections.<Cell>emptyList();
		}
		
		Cell retCell = cellManager.createCell(funcType.getResult());
		paramCells.add(0, retCell);
		
		Cell lambdaCell = cellManager.function();
		graphManager.addFunctionEdge(lambdaCell, paramCells);
		return lambdaCell;
	}
	
	private Cell deref(Cell cell, Type type) {
		Preconditions.checkArgument(!Tag.VOID.equals(type.tag()));
		type = type.resolve();
		
		if(CType.isScalar(type)) {
			Cell pointsToCell = graphManager.getPointsCell(cell);
			return pointsToCell;
		} else {
			return cell;
		}
	}

	private Cell getConstant() {
		return cellManager.bottom();
	}
	
	/**
	 * If the contains edge (container, offset, offset + size(fieldType), field)
	 * exists in the CFPG, return the field. Otherwise, create a field cell
	 * and update CFPG with a new contains edge.
	 * Return the cell points-to the field cell.
	 * 
	 * @throws PreProcessorException
	 */
	private Cell getFieldAddrCell(Cell baseCell, Type fieldType, long offset)
			{
		Preconditions.checkNotNull(baseCell);
		Preconditions.checkArgument(!fieldType.resolve().isArray());
		fieldType = fieldType.resolve();
		long size = CType.getInstance().getSize(fieldType);
		long low = offset, high = offset + size;
		
		Cell fieldCell;
		if(graphManager.hasContainsCell(baseCell, low, high)) {
			fieldCell = graphManager.getContainsCell(baseCell, low, high);
		} else {
	  	fieldCell = cellManager.createCell(fieldType);
	  	graphManager.addContainsEdge(baseCell, low, high, fieldCell);
		}	
		
		Cell addrCell = cellManager.scalar(ptrSize);
		graphManager.addPointsEdge(addrCell, fieldCell);
		return addrCell;
	}

	/**
	 * Get the Cell of <code>op(leftCell, rightCell)</code>
	 * @param node
	 * @param leftCell
	 * @param rightCell
	 * @return
	 * @throws PreProcessorException 
	 */
	private Cell getOpCell(GNode node, Cell leftCell, Cell rightCell)
			{
		Type type = CType.getType(node);
		Cell opCell = cellManager.createCell(type);
		ccjoin(leftCell, opCell);
		ccjoin(rightCell, opCell);
		
		// Pointer arithmetic operations
		pointerOperation(opCell);
		opCellMap.put(Pair.of(node, CType.getScopeName(node)), opCell);
		return opCell;
	}
  
	private void pointerOperation(Cell opCell) {
	  // TODO Auto-generated method stub
	  
  }

	private Cell cast(Cell oldCell, Type newType) {
		Preconditions.checkArgument(!cellManager.isBottom(oldCell));
		newType = newType.resolve();
		
		// Pointer casting.
		if(newType.isPointer()) {
			// The points-to content of cell
			Cell oldPointsToCell = graphManager.getPointsCell(oldCell);
			// The points-to type of cast-to type
			Type newPointsToType = newType.toPointer().getType();
			// The size of the points-to type
			long newPointsToSize = cTypeAnalyzer.getSize(newPointsToType);
			
			if(oldPointsToCell.getSize() == newPointsToSize) {
				// If the old points-to size and the new points-to size consistent,
				// return the old cell and ignore the type cast edge.
				return oldCell;
			} else {
				Cell newPointerCell = cellManager.createCell(newType);
				Cell newPointsToCell = cellManager.createCell(newPointsToType);
				graphManager.addPointsEdge(newPointerCell, newPointsToCell);
				graphManager.addTypeCastEdge(newPointsToCell, oldPointsToCell);
				return newPointerCell;
			}
		}
		
		// Non-pointer type casting.
		else {
			long newSize = cTypeAnalyzer.getSize(newType);
			if(oldCell.getSize() == newSize) {
				return oldCell;
			} else {
				// Only perform type casting if the newSize does not equals to the size
				// of the old cell.
				Cell newCell = cellManager.createCell(newType);
				graphManager.addTypeCastEdge(newCell, oldCell);
				return newCell;
			}
		}
	}
	
	private void ccjoin(Cell rhsCell, Cell lhsCell) {		
	  if(graphManager.hasPointsCell(rhsCell)) {
	  	Cell pointsToCell = graphManager.getPointsCell(rhsCell);
	  	graphManager.addPointsEdge(lhsCell, pointsToCell);
	  } else {
			graphManager.addCCjoinEdge(rhsCell, lhsCell);
	  }
  }
}
