package edu.nyu.cascade.c.pass.alias.cfs;

import xtc.type.Type;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;

class CellManager {
	
  Cell bottom() {
  	Cell bottom = new Cell(Cell.CellKind.BOTTOM, 0);
  	return bottom;
  }
  
	Cell struct(long size) {
		Preconditions.checkArgument(size >= 0);
		Cell struct = new Cell(Cell.CellKind.STRUCT, size);
		return struct;
	}
	
	Cell scalar(long size) {
		Preconditions.checkArgument(size >= 0);
		Cell scalar = new Cell(Cell.CellKind.SCALAR, size);
		return scalar;
	}

	/**
	 * Function cell with no size information
	 * @return
	 */
	Cell function() {
		Cell func = new Cell(Cell.CellKind.FUNC, 0);
		return func;
	}
	
	boolean isBottom(Cell cell) {
		return cell.getKind().equals(Cell.CellKind.BOTTOM);
	}
	
	boolean isScalar(Cell cell) {
		return cell.getKind().equals(Cell.CellKind.SCALAR);
	}
	
	boolean isStruct(Cell cell) {
		return cell.getKind().equals(Cell.CellKind.STRUCT);
	}
	
	boolean isFunction(Cell cell) {
		return cell.getKind().equals(Cell.CellKind.FUNC);
	}
	
	/**
	 * Create cell based on type. 
	 * Return a function cell if type is function.
	 * Return a structure cell if type is structure or union.
	 * Return a scalar cell otherwise.
	 * @param type
	 * @return
	 */
	Cell createCell(Type type) {
		type = type.resolve();
		
		if(type.isFunction()) return function();

		Type cellType;
		if(type.isArray()) {
			cellType = CType.getArrayCellType(type);
		} else {
			cellType = type;
		}
		
		long cellSize = CType.getInstance().getSize(cellType);
		
		Cell resultCell;
		if(type.isStruct() || type.isUnion()) {
			resultCell = struct(cellSize);
		} else {
			resultCell = scalar(cellSize);
		}
		
		if(type.isArray()) {
			resultCell.addProperty(Cell.IsArray, true);
			if(!CType.isVarLengthArray(type)) {
				long arraySize = CType.getInstance().getSize(type);
				resultCell.addProperty(Cell.ArrayLength, arraySize);
			}
		}
		
		return resultCell;
	}
}
