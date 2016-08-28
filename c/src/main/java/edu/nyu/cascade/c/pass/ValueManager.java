package edu.nyu.cascade.c.pass;

import xtc.type.Type;
import xtc.type.VariableT;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;

public class ValueManager {
	private final SymbolTable symbolTable;

	public ValueManager(SymbolTable symTbl) {
		symbolTable = symTbl;
	}

	public static void reset() {
		Function.functionCache.clear();
		GlobalValue.GlobalMap.clear();
		MutableVariable.mutableCache.clear();
		Value.reset();
	}

	public Value getOrCreate(IRVarInfo Info) {
		Preconditions.checkNotNull(Info);
		String Name = Info.getName();
		Type Ty = Info.getXtcType();
		String Scope = Info.getScopeName();

		if (Ty.resolve().isFunction()) {
			Scope rootScope = symbolTable.rootScope();
			assert Scope.equals(rootScope.getName())
					|| Scope.equals(CAnalyzer.EXTERN_PATH);

			Function func = Function.getOrCreate(Name, Scope, Ty);
			String FuncName = xtc.util.SymbolTable.toFunctionScopeName(Name);
			String FuncScope = rootScope.qualify(FuncName);
			// assert rootScope.hasNested(FuncScope) : "Invalid FuncScope.";

			int index = 0;
			for (Type paramTy : Ty.resolve().toFunction().getParameters()) {
				// If the funcID is declared (not yet defined), the paramTy is not
				// attached
				// with a name, then skip registering the parameter.
				if (func.Args[index] == null && paramTy.isVariable()) {
					VariableT param = paramTy.toVariable();
					String paramID = param.getName();
					Type paramType = param.resolve();
					Value paramValue = MutableVariable.getOrCreate(paramID, FuncScope,
							paramType);
					func.Args[index] = paramValue;
				}
				++index;
			}

			return func;
		} else {
			boolean isGlobal = CScopeAnalyzer.getRootScopeName().equals(Scope);
			boolean isStatic = Ty.hasShape() && Ty.getShape().isStatic();
			if (isGlobal || isStatic) {
				return GlobalVariable.getOrCreate(Name, Scope, Ty);
			} else {
				return MutableVariable.getOrCreate(Name, Scope, Ty);
			}
		}
	}

	public Value get(String Name, Type Ty) {
		String Scope = Ty.getScope();

		if (Ty.resolve().isFunction()) {
			Function func = Function.get(Name);
			Scope FuncScope = symbolTable.lookupScope(Name);
			String FuncScopeName = FuncScope.getQualifiedName();

			int index = 0;
			for (Type paramTy : Ty.resolve().toFunction().getParameters()) {
				// If the funcID is declared (not yet defined), the paramTy is not
				// attached
				// with a name, then skip registering the parameter.
				if (func.Args[index] == null && paramTy.isVariable()) {
					VariableT param = paramTy.toVariable();
					String paramID = param.getName();
					Value paramValue = MutableVariable.getOrCreate(paramID, FuncScopeName,
							paramTy);
					func.Args[index] = paramValue;
				}
				++index;
			}

			return func;
		} else {
			boolean isGlobal = CScopeAnalyzer.getRootScopeName().equals(Scope);
			boolean isStatic = Ty.hasShape() && Ty.getShape().isStatic();

			if (isGlobal || isStatic) {
				return GlobalVariable.get(Name, Scope);
			} else {
				return MutableVariable.get(Name, Scope);
			}
		}
	}
}
