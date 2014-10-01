package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Collection;

import xtc.tree.Node;
import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;

/**
 * Preprocessor: type analyzer for Burstall memory model
 * 
 * @author Wei
 *
 */

public class TypeAnalyzer implements PreProcessor<FSType> {
  
  private final Multimap<FSType, IRVar> varTypeMap = HashMultimap.create();
  private final FSTypeEncoder typeEncoder = new FSTypeEncoder();
	
	public static TypeAnalyzer create() {
		return new TypeAnalyzer();
	}

	@Override
	public void analysis(IRStatement stmt) {
		switch(stmt.getType()) {
		case ASSIGN : {
			IRExpression lhs = stmt.getOperand(0);
			IRExpression rhs = stmt.getOperand(1);
			
			Type lhsType = CType.getType(lhs.getSourceNode());
			Type rhsType = CType.getType(rhs.getSourceNode());
			
			if(!CType.isIncompatible(lhsType, rhsType))
				IOUtils.err().println("WARNING: inconsistent type " + stmt);
			
			break;
		}
		default : break;
		}
	}

	/**
	 * Get the points-to type of <code>type</code>. AddressOf reference 
	 * <code>&((*a).z)</code> should be taken care in order to pick
	 * out the structure selection feature as <code>(*a).z</code>
	 * 
	 * @param type
	 * @return
	 */
	@Override
	public FSType getPointsToRep(Node node) {
		if(node.hasName("AddressExpression"))
			return typeEncoder.encodeFSType(node.getNode(0));
		
		Type type = CType.getType(node);
		Type cellType = type;
		
		Type cleanType = type.resolve();
		assert(cleanType.isPointer() || cleanType.isArray() || cleanType.isStruct() || cleanType.isUnion());
		
		if(cleanType.isPointer()) {
			cellType = cleanType.toPointer().getType();
		} else if(cellType.isArray()) {
			cleanType = CType.getArrayCellType(cellType);
		}
		
		String cellTypeName = CType.parseTypeName(cellType);
		FSType res = FSType.of(cellType, cellTypeName);
		IOUtils.debug().pln("The points-to rep is " + res);
		return res;
	}
	
	@Override
	public Type getRepType(FSType rep) {
	  return rep.getType();
	}

	@Override
	public ImmutableMap<FSType, Collection<IRVar>> getSnapShot() {
	  ImmutableMap.Builder<FSType, Collection<IRVar>> builder = 
	  		new ImmutableMap.Builder<FSType, Collection<IRVar>>()
	  		.putAll(varTypeMap.asMap());
	  return builder.build();
	}
	
	/** Don't bother to build snap shot for Burstall memory model */
	@Override
	public void buildSnapShot() {}
	
	@Override
	public FSType getRep(Node node) {
		return typeEncoder.encodeFSType(node);
	}

	/**
	 * Get the name of <code>type</code>
	 */
	@Override
	public String getRepId(FSType fsType) {
		return fsType.getId();
	}
	
	@Override
	public FSType getSrcRep(FSType fsType) {
		while(fsType.hasParent()) {
			fsType = fsType.getParent();
		}
	  return fsType;
	}
	
	@Override
	public void addAllocRegion(FSType fsType, Expression region) {
	  Preconditions.checkNotNull(region.getNode());
	  Node lvalNode = region.getNode();
	  
	  String name = lvalNode.getString(0);
	  Type type = CType.getType(lvalNode);
	  String scopeName = CType.getScopeName(lvalNode);
	  
	  IRVar var = VarImpl.createForRegion(name, type, scopeName, region);
		
		varTypeMap.put(fsType, var);
		
		IOUtils.debug().pln(displaySnapShot());
	}

	@Override
	public IRVar addStackVar(Expression lval) {
	  Preconditions.checkNotNull(lval.getNode());
	  Node lvalNode = lval.getNode();
	  String name = lvalNode.getString(0);
	  Type type = CType.getType(lvalNode);
	  String scopeName = CType.getScopeName(lvalNode);
	  
	  IRVar var = VarImpl.createForSymbol(name, type, scopeName, lval);
	  FSType fsType = typeEncoder.encodeFSType(lvalNode);
		
	  varTypeMap.put(fsType, var);
	  IOUtils.debug().pln(displaySnapShot());
	  
	  return var;
	}

	@Override
	public String displaySnapShot() {
		StringBuilder sb = new StringBuilder();
		sb.append('\n').append("The result of type analysis: \n");
		for(FSType fsType : varTypeMap.keySet()) {
			sb.append('\t').append(getRepId(fsType)).append(": ");
			sb.append("Partition ")
			.append(fsType.getTypeName())
			.append(" { ");
			
			for(IRVar var : varTypeMap.get(fsType)) {
				sb.append(var.toStringShort()).append(' ');
			}
			sb.append("}\n");
		}
		return sb.toString();
	}
}