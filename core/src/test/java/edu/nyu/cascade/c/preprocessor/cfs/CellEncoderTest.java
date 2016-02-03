package edu.nyu.cascade.c.preprocessor.cfs;

import static org.junit.Assert.*;

import java.math.BigInteger;
import java.util.List;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import com.google.common.collect.Lists;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.ArrayT;
import xtc.type.NumberT;
import xtc.type.PointerT;
import xtc.type.StructOrUnionT;
import xtc.type.StructT;
import xtc.type.Type;
import xtc.type.UnionT;
import xtc.type.VariableT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.cfs.Cell;
import edu.nyu.cascade.c.preprocessor.cfs.CellEncoder;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.impl.SymbolTableImpl;
import edu.nyu.cascade.ir.impl.VarInfoFactory;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

public class CellEncoderTest {
	 private CellEncoder cellEncoder;
	 private CellManager cellManager;
	 private CFPGraphManager graphManager;
	 private SymbolTable symbolTable;
	 
	 private CType typeAnalyzer = CType.getInstance();
	 private String xVarName = "x", yVarName = "y";
	 private String zVarName = "z";
	 private String uVarName = "u";
	 private String arrIn1DimName = "a";
	 private String arrIn2DimName = "a2";
	 private String arrInStructName = "as";
	 private String structArrInStructName = "sas";
	 private long ptrSize = typeAnalyzer.getSize(new PointerT(VoidT.TYPE));
	 
	 @Before
	 public void setUp() throws Exception {
		 Preferences.set(Preferences.OPTION_BYTE_BASED);
	   IOUtils.enableDebug();
		 
	   symbolTable = new SymbolTableImpl(new xtc.util.SymbolTable());
	   cellManager = new CellManager();
	   graphManager = new CFPGraphManager();
	   cellEncoder = CellEncoder.create(symbolTable, cellManager, graphManager);
	    
	   createSimpleDeclarator(xVarName, NumberT.INT);
	   createSimpleDeclarator(yVarName, new PointerT(NumberT.INT));
	 	 createSimpleDeclarator(zVarName,
	 			 createStruct("S", NumberT.INT, NumberT.INT, NumberT.LONG));
	 	 createSimpleDeclarator(uVarName, createUnion());
	 	 createSimpleDeclarator(arrIn1DimName,
	 			 new ArrayT(NumberT.INT, 5));
	 	 createSimpleDeclarator(arrIn2DimName,
	 			 new ArrayT(new ArrayT(NumberT.INT, 5), 5));
	 	 createSimpleDeclarator(arrInStructName,
	 			 createStruct("SA", NumberT.INT, new ArrayT(NumberT.INT, 5)));
	 	 
	 	 createSimpleDeclarator(structArrInStructName,
	 			 createStruct("SAS", NumberT.INT,
	 					 new ArrayT(
	 							 createStruct("S", NumberT.INT, NumberT.INT),
	 							 5)));
	 }

	 private StructT createStruct(String name, Type... t) {
		 List<VariableT> fields = Lists.newArrayList();
		 for(int i = 1;i <= t.length;i++) {
			 String fieldName = "f" + i;
			 fields.add(VariableT.newField(t[i-1], fieldName));
		 }
		 return new StructT(name, fields);
	 }

	 private UnionT createUnion() {
		 VariableT field1 = VariableT.newField(
				 createStruct("S1", NumberT.INT, NumberT.INT, NumberT.INT), "g1");
		 VariableT field2 = VariableT.newField(
				 createStruct("S2", NumberT.INT, NumberT.INT), "g2");
		 return new UnionT("U", Lists.newArrayList(field1, field2));
	 }	 
	 
	 // Place-holder to avoid "no runnable tests" error
	 @Test
	 public void testNothing() { }
	 
	 @Test
	 public void testPrimaryIdentifier() {
		 Node varNode = createPrimaryIdentifier(xVarName);
	 	 Cell varCell = cellEncoder.toLval(varNode);
	 	 assertEquals(ptrSize, varCell.getSize());
	 	 assertTrue(cellManager.isScalar(varCell));
	 	 
	 	 Cell varRightCell = cellEncoder.toRval(varNode);
	 	 assertTrue(cellManager.isScalar(varRightCell));
	 	 Type type = symbolTable.lookup(xVarName).getXtcType();
	 	 assertEquals(varRightCell.getSize(),
	 			 typeAnalyzer.getSize(type));
	 	 
	 	 // lval(x) points-to rval(x)
	 	 assertEquals(graphManager.getPointsCell(varCell), varRightCell);
	 }
	 
	 @Test
	 public void testIntegerConstant() {
		 Node constantNode = createConstant(1024);
		 Cell constantCell = cellEncoder.toRval(constantNode);
		 
		 // constant is always attached with bottom cell
		 assertTrue(cellManager.isBottom(constantCell));
	 }
	 
	 @Test
	 public void testAddressExpression() {
		 Node varNode = createPrimaryIdentifier(xVarName);		 
		 Node addrNode = createAddressExpression(varNode);
		 
		 Cell varCell = cellEncoder.toLval(varNode);
		 Cell addrCell = cellEncoder.toRval(addrNode);
		 
		 // lcell(x) = rcell(&x)
		 assertEquals(varCell, addrCell);
	 }
	 
	 @Test
	 public void testIndirectionExpression() {
		 Node varNode = createPrimaryIdentifier(xVarName);		 
		 Node addrNode = createAddressExpression(varNode);
		 Node indNode = createIndirectionExpression(addrNode);
		 
		 Cell varCell = cellEncoder.toRval(varNode);
		 Cell indCell = cellEncoder.toRval(indNode);
		 
		 // rcell(x) = rcell(*(&x))
		 assertEquals(indCell, varCell);
	 }
	 
	 @Test(expected=IllegalArgumentException.class)
	 public void testAdditiveExpression() {
		 Node varNode = createPrimaryIdentifier(xVarName);
		 Node addrNode = createAddressExpression(varNode);
		 // &x + x
		 Node addNode =
				 GNode.create("AdditiveExpression", addrNode, "+", varNode);
		 CType.getType(addrNode).mark(addNode);
		 symbolTable.mark(addNode);
		 
		 Cell varCell = cellEncoder.toRval(varNode);
		 Cell addCell = cellEncoder.toRval(addNode);
		 
		 // cell(&x + x) points to cell(x)
		 assertEquals(varCell, graphManager.getPointsCell(addCell));
		 
		 // cell(x) is null
		 graphManager.getPointsCell(varCell);
	 }
	 
	 @Test
	 public void testSubscriptExpression() {
		 Node varNode = createPrimaryIdentifier(arrIn1DimName);
		 Node indexNode = createConstant(2);
		 // a[2]
		 Node subscriptNode =
				 GNode.create("SubscriptExpression", varNode, indexNode);
		 CType.getType(varNode).resolve().toArray().getType().mark(subscriptNode);
		 symbolTable.mark(subscriptNode);
		 
		 Cell varCell = cellEncoder.toRval(varNode);
		 Cell subscriptCell = cellEncoder.toRval(subscriptNode);
		 // cell(a) -> cell(a[2])
		 assertEquals(subscriptCell, graphManager.getPointsCell(varCell));
	 }
	 
	 @Ignore("array field is not yet supported")
	 @Test
	 public void testArrayInStruct() {
		 Node varNode = createPrimaryIdentifier(arrInStructName);
		 String field2 = "f2";
		 // as.f2
		 Node f2Node = GNode.create("DirectComponentSelection", varNode, field2);
		 CType.getType(varNode).resolve().toStruct().lookup(field2).mark(f2Node);
		 // as.f2[2]
		 Node indexNode = createConstant(2);
		 Node subscriptNode = GNode.create("SubscriptExpression",
				 f2Node, indexNode);
		 CType.getType(f2Node).resolve().toArray().getType().mark(subscriptNode);
		 
		 symbolTable.mark(f2Node);
		 symbolTable.mark(indexNode);
		 symbolTable.mark(subscriptNode);
		 
		 long offset = typeAnalyzer.getOffset(
				 CType.getType(varNode).resolve().toStruct(), field2);
		 long size = typeAnalyzer.getSize(CType.getType(f2Node));
		 
		 // Cell(as)
		 Cell varCell = cellEncoder.toRval(varNode);
		 // Cell(as.f2)
		 Cell f2Cell = cellEncoder.toRval(f2Node);		 
		 // Cell(as.f2[2])
		 Cell subscriptCell = cellEncoder.toRval(subscriptNode);
		 // Cell(as.f2) -> Cell(as.f2[2])
		 assertEquals(subscriptCell, graphManager.getPointsCell(f2Cell));
		 // Cell(as) -- (offset, offset + size) --> Cell(as.f2[2])
		 assertEquals(subscriptCell, graphManager.getContainsCell(
				 graphManager.getPointsCell(varCell), offset, offset + size));
	 }
	 
	 @Ignore("array field is not yet supported")
	 @Test
	 public void testStructArrayInStruct() {
		 Node varNode = createPrimaryIdentifier(structArrInStructName);
		 String field1 = "f1", field2 = "f2";
		 // sas.f2
		 Node f2Node = GNode.create("DirectComponentSelection", varNode, field2);
		 CType.getType(varNode).resolve().toStruct().lookup(field2).mark(f2Node);
		 // sas.f2[2]
		 Node indexNode = createConstant(2);
		 Node subscriptNode = GNode.create("SubscriptExpression",
				 f2Node, indexNode);
		 CType.getType(f2Node).resolve().toArray().getType().mark(subscriptNode);
		 // sas.f2[2].f1
		 Node f2f1Node =
				 GNode.create("DirectComponentSelection", subscriptNode, field1);
		 CType.getType(subscriptNode).resolve().toStruct().lookup(field1)
		 .mark(f2f1Node);
		 
		 symbolTable.mark(f2Node);
		 symbolTable.mark(indexNode);
		 symbolTable.mark(subscriptNode);
		 symbolTable.mark(f2f1Node);
		 
		 long offset = typeAnalyzer.getOffset(
				 CType.getType(varNode).resolve().toStruct(), field2);
		 long size = typeAnalyzer.getSize(CType.getType(f2Node));
		 
		 // Cell(as)
		 Cell varCell = cellEncoder.toRval(varNode);
		 // Cell(as.f2)
		 Cell f2Cell = cellEncoder.toRval(f2Node);		 
		 // Cell(as.f2[2])
		 Cell subscriptCell = cellEncoder.toRval(subscriptNode);
		 // Cell(as.f2) -> Cell(as.f2[2])
		 assertEquals(subscriptCell, graphManager.getPointsCell(f2Cell));
		 // Cell(as) -- (offset, offset + size) --> Cell(as.f2[2])
		 assertEquals(subscriptCell, graphManager.getContainsCell(
				 graphManager.getPointsCell(varCell), offset, offset + size));
	 }
	 
	 @Test
	 public void testRelationOpExpression() {
		 Node varNode = createPrimaryIdentifier(xVarName);
		 // x == x
		 Node eqNode = GNode.create("EqualityExpression", varNode, "==", varNode);
		 // x != x
		 Node neqNode = GNode.create("EqualityExpression", varNode, "!=", varNode);
		 symbolTable.mark(eqNode);
		 symbolTable.mark(neqNode);
		 
		 Cell eqCell = cellEncoder.toRval(eqNode);
		 Cell neqCell = cellEncoder.toRval(neqNode);
		 assertTrue(cellManager.isBottom(eqCell));
		 assertTrue(cellManager.isBottom(neqCell));
	 }
	 
	 @Test
	 public void testConditionalExpression() {
		 Node varNode = createPrimaryIdentifier(xVarName);
		 Node eqNode = GNode.create("EqualityExpression", varNode, "==", varNode);
		 Node addrNode = createAddressExpression(varNode);
		 Node constantNode = createConstant(0);
		 Node condNode =
				 GNode.create("ConditionalExpression", eqNode, addrNode, constantNode);
		 Type addrType = CType.getType(addrNode);
		 addrType.mark(condNode);
		
		 symbolTable.mark(eqNode);
		 symbolTable.mark(addrNode);
		 symbolTable.mark(condNode);
		 
		 Cell condCell = cellEncoder.toRval(condNode); // x == x ? &x : 0;
		 
		 Cell condPointsToCell = graphManager.getPointsCell(condCell);
		 Cell varCell = cellEncoder.toRval(varNode);
		 assertEquals(condPointsToCell, varCell);	 
	 }
	 
	 @Test
	 public void testAssignExpression() {
		 Node xVarNode = createPrimaryIdentifier(xVarName);
		 Node addrNode = createAddressExpression(xVarNode);
		 Node yVarNode = createPrimaryIdentifier(yVarName);
		 // y = &x
		 Node assignNode = GNode.create("AssignmentExpression", yVarNode, "=",
				 addrNode);
		 symbolTable.mark(assignNode);
		 symbolTable.lookup(yVarName).getXtcType().mark(assignNode);
		 
		 // cell(x)
		 Cell xCell = cellEncoder.toRval(xVarNode);
		 // cell(y)
		 Cell yCell = cellEncoder.toRval(yVarNode);
		 // cell(&x)
		 Cell addrCell = cellEncoder.toRval(addrNode);
		 // cell(y = &x)
		 Cell assignCell = cellEncoder.toRval(assignNode);
		 
		 // cell(y = &x) -> cell(x)
		 assertEquals(xCell, graphManager.getPointsCell(assignCell));
		 // cell(y) -> cell(x)
		 assertEquals(xCell, graphManager.getPointsCell(yCell));
		 // cell(y = &x) = cell(&x)
		 assertEquals(assignCell, addrCell);
	 }
	 
	 
	 @Test
	 public void testStructDirectComponentSelection() {
		 Node zVarNode = createPrimaryIdentifier(zVarName);
		 String field1 = "f1", field2 = "f2";
		 // z.f1
		 Node f1Node = GNode.create("DirectComponentSelection", zVarNode, field1);
		 // z.f2
		 Node f2Node = GNode.create("DirectComponentSelection", zVarNode, field2);
		 StructOrUnionT baseType = symbolTable.lookup(zVarName).getXtcType()
				 .resolve().toStructOrUnion();
		 Type f1Type = baseType.lookup(field1);
		 Type f2Type = baseType.lookup(field2);
		 f1Type.mark(f1Node);
		 f2Type.mark(f2Node);
		 symbolTable.mark(f1Node);
		 symbolTable.mark(f2Node);
		 
		 // cell(z.f1)
		 Cell f1Cell = cellEncoder.toRval(f1Node);
		 // cell(z.f2)
		 Cell f2Cell = cellEncoder.toRval(f2Node);
		 
		 long f1Offset = typeAnalyzer.getOffset(baseType, field1);
		 long f2Offset = typeAnalyzer.getOffset(baseType, field2);
		 long f1Size = typeAnalyzer.getSize(f1Type);
		 long f2Size = typeAnalyzer.getSize(f2Type);
		 
		 // cell(&z)
		 Cell addrVarCell = cellEncoder.toRval(zVarNode);
		 // cell(z)
		 Cell varCell = graphManager.getPointsCell(addrVarCell);
		 
		 // cell(z) -- (f1Offset, f1Offset + f1Size) --> cell(z.f1)
		 assertEquals(f1Cell, graphManager.getContainsCell(varCell, f1Offset,
				 f1Offset + f1Size));
		 // cell(z) -- (f2Offset, f2Offset + f2Size) --> cell(z.f2)
		 assertEquals(f2Cell, graphManager.getContainsCell(varCell, f2Offset,
				 f2Offset + f2Size));
	 }

	 @Test
	 public void testStructIndirectComponentSelection() {
		 Node zVarNode = createPrimaryIdentifier(zVarName);
		 Node zAddrNode = createAddressExpression(zVarNode);
		 String field1 = "f1", field2 = "f2";
		 // &z->f1
		 Node f1Node = GNode.create("IndirectComponentSelection",
				 zAddrNode, field1);
		 // &z->f2
		 Node f2Node = GNode.create("IndirectComponentSelection",
				 zAddrNode, field2);
		 Type baseType = symbolTable.lookup(zVarName).getXtcType();
		 Type f1Type = baseType.resolve().toStructOrUnion().lookup(field1);
		 Type f2Type = baseType.resolve().toStructOrUnion().lookup(field2);
		 f1Type.mark(f1Node);
		 f2Type.mark(f2Node);
		 symbolTable.mark(f1Node);
		 symbolTable.mark(f2Node);
		 Cell f1Cell = cellEncoder.toRval(f1Node);
		 Cell f2Cell = cellEncoder.toRval(f2Node);
		 
		 Node zDerefNode = createIndirectionExpression(zAddrNode);
		 // z.f1
		 Node f1NodePrime = GNode.create("DirectComponentSelection",
				 zDerefNode, field1);
		 // z.f2
		 Node f2NodePrime = GNode.create("DirectComponentSelection",
				 zDerefNode, field2);
		 f1Type.mark(f1NodePrime);
		 f2Type.mark(f2NodePrime);
		 symbolTable.mark(f1NodePrime);
		 symbolTable.mark(f2NodePrime);
		 Cell f1CellPrime = cellEncoder.toRval(f1Node);
		 Cell f2CellPrime = cellEncoder.toRval(f2Node);
		 
		 assertEquals(f1Cell, f1CellPrime);
		 assertEquals(f2Cell, f2CellPrime);
	 }
	 
	 @Test
	 public void testCastPointerToStruct() {
		 // z (with type S{int, int, long}
		 Node zVarNode = createPrimaryIdentifier(zVarName);
		 Node zAddrNode = createAddressExpression(zVarNode); // &z
		 Node specifier =
				 GNode.create("SpecifierQualifierList", GNode.create("Int"));
		 Node abstractDecl =
				 GNode.create("AbstractDeclarator",
						 GNode.create("Pointer",
								 GNode.create("TypeQualifierList"), null), null);
		 Node typeNode = GNode.create("TypeName", specifier, abstractDecl);
		 // (int *) &z
		 Node castNode = GNode.create("CastExpression", typeNode, zAddrNode);
		 new PointerT(NumberT.INT).mark(castNode);
		 symbolTable.mark(castNode);
		 
		 Cell varCell = cellEncoder.toRval(zVarNode); // &z
		 Cell addrCell = cellEncoder.toRval(zAddrNode);
		 assertEquals(varCell, addrCell);
		 Cell castCell = cellEncoder.toRval(castNode);
		 assertEquals(
				 graphManager.getPointsCell(varCell),
				 graphManager.getCastSourceCell(
						 graphManager.getPointsCell(castCell)));
	 }

	 @Test
	 public void testCastPointerToFieldSelectInStruct() {
		 Node zVarNode = createPrimaryIdentifier(zVarName);
		 StructT sType =
				 symbolTable.lookup(zVarName).getXtcType().resolve().toStruct();
		 // z.f1
		 Node f1Node =
				 GNode.create("DirectComponentSelection", zVarNode, "f1");
		 sType.lookup("f1").mark(f1Node);
		 // z.f2
		 Node f2Node =
				 GNode.create("DirectComponentSelection", zVarNode, "f2");
		 sType.lookup("f2").mark(f2Node);
		 // z.f3
		 Node f3Node =
				 GNode.create("DirectComponentSelection", zVarNode, "f3");
		 sType.lookup("f3").mark(f3Node);
		 
		 symbolTable.mark(f1Node);
		 symbolTable.mark(f2Node);
		 symbolTable.mark(f3Node);
		 
		 // Casting from a pointer to integer to a pointer to long.
		 Node f1AddrNode = createAddressExpression(f1Node);
		 Node specifier =
				 GNode.create("SpecifierQualifierList", GNode.create("Long"));
		 Node abstractDecl =
				 GNode.create("AbstractDeclarator", GNode.create("Pointer",
						 GNode.create("TypeQualifierList"), null), null);
		 Node typeNode = GNode.create("TypeName", specifier, abstractDecl);
		 Node castNode = GNode.create("CastExpression", typeNode, f1AddrNode);
		 new PointerT(NumberT.LONG).mark(castNode);
		 symbolTable.mark(castNode);
		 
		 Cell f1Cell = cellEncoder.toRval(f1Node);
		 Cell castPointsToCell =
				 graphManager.getPointsCell(cellEncoder.toRval(castNode));
		 assertEquals(f1Cell, graphManager.getCastSourceCell(castPointsToCell));
		 
		 // Casting from a pointer to integer to a pointer to integer.
		 Node f2AddrNode = createAddressExpression(f2Node);
		 Node specifier2 =
				 GNode.create("SpecifierQualifierList", GNode.create("INT"));
		 Node abstractDecl2 =
				 GNode.create("AbstractDeclarator", GNode.create("Pointer",
						 GNode.create("TypeQualifierList"), null), null);
		 Node typeNode2 = GNode.create("TypeName", specifier2, abstractDecl2);
		 Node castNode2 = GNode.create("CastExpression", typeNode2, f2AddrNode);
		 new PointerT(NumberT.INT).mark(castNode2);
		 symbolTable.mark(castNode2);
		 
		 Cell f2AddrCell = cellEncoder.toRval(f2AddrNode);
		 Cell castPointerCell2 = cellEncoder.toRval(castNode2);
		 assertEquals(castPointerCell2, f2AddrCell);
	 }	 
	 
	 @Test
	 public void testUnionDirectComponentSelection() {
		 Node uVarNode = createPrimaryIdentifier(uVarName);
		 String g1 = "g1", g2 = "g2", f1 = "f1", f2 = "f2", f3 = "f3";
		 
		 UnionT uType = symbolTable.lookup(uVarName)
				 .getXtcType().resolve().toUnion();
		 StructT g1Type = uType.lookup(g1).resolve().toStruct();
		 StructT g2Type = uType.lookup(g2).resolve().toStruct();
		 
		 Type g1f1Type = g1Type.lookup(f1);
		 Type g1f2Type = g1Type.lookup(f2);
		 Type g1f3Type = g1Type.lookup(f3);
		 
		 Type g2f1Type = g2Type.lookup(f1);
		 Type g2f2Type = g2Type.lookup(f2);
		 
		 long g1Offset = typeAnalyzer.getOffset(uType, g1);
		 long g2Offset = typeAnalyzer.getOffset(uType, g2);
		 
		 long g1f1Offset = typeAnalyzer.getOffset(g1Type, f1);
		 long g1f2Offset = typeAnalyzer.getOffset(g1Type, f2);
		 long g1f3Offset = typeAnalyzer.getOffset(g1Type, f3);
		 
		 long g2f1Offset = typeAnalyzer.getOffset(g2Type, f1);
		 long g2f2Offset = typeAnalyzer.getOffset(g2Type, f2);
		 
		 // u.g1
		 Node g1Node = GNode.create("DirectComponentSelection", uVarNode, g1);
		 g1Type.mark(g1Node);
		 // u.g2
		 Node g2Node = GNode.create("DirectComponentSelection", uVarNode, g2);
		 g2Type.mark(g2Node);
		 
		 // u.g1.f1		
		 Node g1f1Node = GNode.create("DirectComponentSelection", g1Node, f1);
		 g1f1Type.mark(g1f1Node);
		 // u.g1.f2
		 Node g1f2Node = GNode.create("DirectComponentSelection", g1Node, f2);
		 g1f2Type.mark(g1f2Node);
		 // u.g1.f3
		 Node g1f3Node = GNode.create("DirectComponentSelection", g1Node, f3);
		 g1f3Type.mark(g1f3Node);
		 
		 // u.g2.f1
		 Node g2f1Node = GNode.create("DirectComponentSelection", g2Node, f1);
		 g2f1Type.mark(g2f1Node);
		 // u.g2.f2
		 Node g2f2Node = GNode.create("DirectComponentSelection", g2Node, f2);
		 g2f2Type.mark(g2f2Node);
		 
		 symbolTable.mark(g1Node);
		 symbolTable.mark(g2Node);
		 symbolTable.mark(g1f1Node);
		 symbolTable.mark(g1f2Node);
		 symbolTable.mark(g1f3Node);
		 symbolTable.mark(g2f1Node);
		 symbolTable.mark(g2f2Node);
		 
		 Cell g1PtrCell = cellEncoder.toRval(g1Node);
		 Cell g1Cell = graphManager.getPointsCell(g1PtrCell);
		 Cell g1f1Cell = cellEncoder.toRval(g1f1Node);
		 Cell g1f2Cell = cellEncoder.toRval(g1f2Node);
		 Cell g1f3Cell = cellEncoder.toRval(g1f3Node);
		 Cell g2PtrCell = cellEncoder.toRval(g2Node);
		 Cell g2Cell = graphManager.getPointsCell(g2PtrCell);
		 Cell g2f1Cell = cellEncoder.toRval(g2f1Node);
		 Cell g2f2Cell = cellEncoder.toRval(g2f2Node);
		 
		 Cell unionPtrCell = cellEncoder.toRval(uVarNode);
		 Cell unionCell = graphManager.getPointsCell(unionPtrCell);
		 
//		 assertEquals(g1f1Cell, g2f1Cell);
//		 assertEquals(g1f2Cell, g2f2Cell);
		 
		 assertEquals(g1Cell,
				 graphManager.getContainsCell(unionCell, g1Offset,
						 g1Offset + typeAnalyzer.getSize(g1Type)));
		 assertEquals(g2Cell,
				 graphManager.getContainsCell(unionCell, g2Offset,
						 g2Offset + typeAnalyzer.getSize(g2Type)));
		 
		 assertEquals(g1f1Cell,
				 graphManager.getContainsCell(g1Cell, g1f1Offset,
						 g1f1Offset + typeAnalyzer.getSize(g1f1Type)));
		 assertEquals(g1f2Cell, 
				 graphManager.getContainsCell(g1Cell, g1f2Offset,
						 g1f2Offset + typeAnalyzer.getSize(g1f2Type)));
		 assertEquals(g1f3Cell,
				 graphManager.getContainsCell(g1Cell, g1f3Offset,
						 g1f3Offset + typeAnalyzer.getSize(g1f3Type)));
		 
		 assertEquals(g2f1Cell,
				 graphManager.getContainsCell(g2Cell, g2f1Offset,
						 g2f1Offset + typeAnalyzer.getSize(g2f1Type)));
		 assertEquals(g2f2Cell,
				 graphManager.getContainsCell(g2Cell, g2f2Offset,
						 g2f2Offset + typeAnalyzer.getSize(g2f2Type)));
	 }

	 @Test
	 public void testMultiSubscriptExpression() {
		 // a2[1][1]
		 Node aVarNode = createPrimaryIdentifier(arrIn2DimName);
		 Node indexNode = createConstant(1);
		 Node subscriptNode =
				 GNode.create("SubscriptExpression", aVarNode, indexNode);
		 Node multiSubscriptNode =
				 GNode.create("SubscriptExpression", subscriptNode, indexNode);
		 Type cellType =
				 symbolTable.lookup(arrIn2DimName)
				 .getXtcType().resolve().toArray().getType();
		 cellType.mark(subscriptNode);
		 cellType.resolve().toArray().getType().mark(multiSubscriptNode);
		 symbolTable.mark(subscriptNode);
		 symbolTable.mark(multiSubscriptNode);
		 
		 Cell varCell = cellEncoder.toRval(aVarNode);
		 Cell subscriptCell = cellEncoder.toRval(subscriptNode);
		 Cell multiSubscriptCell = cellEncoder.toRval(multiSubscriptNode);
		 
		 // cell(a2) -> cell(a2[1][1])
		 assertEquals(
				 multiSubscriptCell,
				 graphManager.getPointsCell(varCell));
		 // cell(a2[1]) -> cell(a2[1][1])
		 assertEquals(
				 multiSubscriptCell,
				 graphManager.getPointsCell(subscriptCell));
	 }	 
	 
	 private Node createConstant(int number) {
		 Node node = GNode.create("IntegerConstant", String.valueOf(number));
		 Type intType =
				 NumberT.INT.annotate().constant(BigInteger.valueOf(number));
		 intType.mark(node);
		 return node;
	 }

	 private Node createPrimaryIdentifier(String varName) {
		 Node node = GNode.create("PrimaryIdentifier", varName);
		 Type type = symbolTable.lookup(varName).getXtcType();
	   type.mark(node);
	   symbolTable.mark(node);
	   return node;
	 }
	 
	 private Node createSimpleDeclarator(String varName, Type type) {
		 Node varNode = GNode.create("SimpleDeclarator", varName);
		 Type varType = type.annotate().shape(false, varName);
		 varType.mark(varNode);
	 	 symbolTable.mark(varNode);
	 	 addBinding(varName, varNode);
	 	 return varNode;
	 }
	 
	 private Node createIndirectionExpression(Node addrNode) {
		 Node indNode = GNode.create("IndirectionExpression", addrNode);
		 CType.getType(addrNode).toPointer().getType().mark(indNode);
		 symbolTable.mark(indNode);
		 return indNode;
	 }

	private Node createAddressExpression(Node primaryId) {
		 Node addrNode = GNode.create("AddressExpression", primaryId);
		 Type varType = CType.getType(primaryId);
		 Type ptrType = new PointerT(varType);
		 ptrType.mark(addrNode);
		 symbolTable.mark(addrNode);
		 return addrNode;
	 }
	 
	 private IRVarInfo addBinding(String name, Node varNode) {	  	
	  	assert(!symbolTable.isDefined(name));
	  	
	    String scopeName = symbolTable.getCurrentScope().getQualifiedName();
	    Type type = CType.getType(varNode);
	  	IRVarInfo binding = VarInfoFactory.createVarInfoWithType(
	  			scopeName, name, type);
	  	
	  	symbolTable.define(name, binding);
	  	return binding;
	 }
//
//	 private String getCellInfo(Cell ecr) {
//		 StringBuilder sb = new StringBuilder();
//		 sb.append("Cell ").append(uf.findRoot(ecr).getId()).append(": ");
//  	 sb.append(uf.getType(ecr));
//  	 return sb.toString();
//	 }
//	 
//	 private String displaySnapShot() {
//		 ImmutableMap<Cell, Collection<IRVar>> snapShot = uf.snapshot();
//		 StringBuilder sb = new StringBuilder();
//		  
//		 for(Entry<Cell, Collection<IRVar>> entry : snapShot.entrySet()) {
//			 Cell ecr = entry.getKey();
//			 Collection<IRVar> vars = entry.getValue();
//			 if(!vars.isEmpty()) {
//		  	 sb.append(getCellInfo(ecr)).append("\n { ");
//		  		
//		  	 for(IRVar var : vars) sb.append(var.getName()).append(' ');
//		  	 sb.append("}\n");
//		   }
//		}
//		return sb.toString();
//	}
}
