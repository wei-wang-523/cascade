package edu.nyu.cascade.c.pass.alias.steenscfsopt;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.pass.IRVar;
import xtc.type.Type;

class VarImpl implements IRVar {
	private final ECR ecr;
	private final String name;
	private final Type type;
	private final String scopeName;
	private final Map<String, Object> properties;

	VarImpl(String name, Type type, String scopeName, ECR ecr) {
		this.name = name;
		this.type = type;
		this.scopeName = scopeName;
		this.ecr = ecr;
		this.properties = Maps.newHashMap();
	}

	/**
	 * Create an IRVar for a symbol with struct or union type
	 * 
	 * @param name
	 * @param xtcType
	 * @param scopeName
	 * @return
	 */
	static VarImpl[] createForStructOrUnionSymbol(String name, Type xtcType,
			String scopeName) {
		Preconditions.checkArgument(
				xtcType.resolve().isStruct() || xtcType.resolve().isUnion());

		BlankType regionType = ValueType.blank(Size.createForType(xtcType),
				Parent.getBottom());

		ECR regECR = ECR.create(regionType);
		VarImpl regVar = new VarImpl(name, xtcType, scopeName, regECR);

		SimpleType varType = ValueType.simple(regECR, ECR.createBottom(),
				Size.createForType(xtcType), Parent.getBottom());

		ECR varECR = ECR.create(varType);

		VarImpl var = new VarImpl(name, xtcType, scopeName, varECR);

		return new VarImpl[] { var, regVar };
	}

	/**
	 * Create an IRVar for a symbol with array type
	 * 
	 * @param name
	 * @param type
	 * @param scopeName
	 * @return
	 */
	static VarImpl[] createForArraySymbol(String name, Type xtcType,
			String scopeName) {
		Preconditions.checkArgument(xtcType.resolve().isArray());

		BlankType blankType = ValueType.blank(Size.createForType(xtcType),
				Parent.getBottom());

		ECR regECR = ECR.create(blankType);
		VarImpl regVar = new VarImpl(name, xtcType, scopeName, regECR);

		SimpleType varType = ValueType.simple(regECR, ECR.createBottom(),
				Size.createForType(xtcType), Parent.getBottom());

		ECR varECR = ECR.create(varType);

		VarImpl var = new VarImpl(name, xtcType, scopeName, varECR);

		return new VarImpl[] { var, regVar };
	}

	static VarImpl createForScalarSymbol(String name, Type xtcType,
			String scopeName) {
		Parent parent = Parent.getBottom();
		BlankType blankType = ValueType.blank(Size.createForType(xtcType), parent);

		ECR varECR = ECR.create(blankType);

		return new VarImpl(name, xtcType, scopeName, varECR);
	}

	ECR getECR() {
		return (ECR) ecr.findRoot();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(name).append('@').append(scopeName).append(" (").append(type)
				.append(") : ");

		return sb.toString();
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public String getScopeName() {
		return scopeName;
	}

	@Override
	public void setProperty(String id, Object o) {
		properties.put(id, o);
	}

	@Override
	public Object getProperty(String id) {
		return properties.get(id);
	}
}
