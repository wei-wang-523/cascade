package edu.nyu.cascade.datatypes;

/** 
 * A datatype definition for compressed domain names as specified in 
 * <a href="http://www.faqs.org/rfcs/rfc883.html">RFC 883</a>. The
 * class defines a datatype Dn and auxiliary functions Dn and sizeDn.
 * The function Dn maps a bit-string (an array of bytes and an index) 
 * to a Dn value. The function sizeDn maps a bit-string to the size
 * of the Dn value returned by Dn (i.e., the number of indices sizeDn
 * will use to determine its return value).
 * 
 * This class refers to the Preference key DATATYPES_EXPLICIT_UNKNOWN to 
 * determine whether the unknown value is represented implicitly or
 * explicitly. The implicit representation leaves the results of Dn
 * undefined if the value is not uniquely determined by the input 
 * bit-string (e.g., because of ambiguity in the definition of the 
 * datatype). In this case we need an additional "non-interference" axiom,
 * which says that although the result of Dn is not always well-defined,
 * it will be consistent between "locally identical" bit-strings (see
 * the definition of the axiom for more information).
 * 
 * The explicit representation adds an arity-0 "unknown" constructor to
 * the datatype (with sizeDn(unknown) = 0) and defines it as the result of Dn
 * whenever no other constructor applies.
 * 
 * The datatype corresponds to the following pseudo-declaration:
 <pre>
 Dn =
 label    { tag:2 = 0b00, len:6, label:char[len], rest:Dn }
 | indirect { tag:2 = 0b11, offset: 14 }
 | nullt    { tag:8 = 0x00 } 
 </pre>
 * which gets dismantled in CVC notation into:
 <pre>
 PtrType : TYPE = BITVECTOR(32);
 CharType : TYPE = BITVECTOR(8);
 MemType : TYPE = ARRAY PtrType OF CharType;
 StringType : TYPE = ARRAY PtrType OF CharType;

 TagType : TYPE = BITVECTOR(2);
 LenType : TYPE = BITVECTOR(6);
 OffsetType : TYPE = BITVECTOR(14);

 DATATYPE 
 Dn = label( len: LenType, label : StringType, rest: Dn ),
 | indirect( offset: OffsetType ),
 | nullt
 END;
 </pre>

 */

import static com.google.common.base.Preconditions.checkArgument;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.DefaultPointerEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.FlatMemoryModel;
import edu.nyu.cascade.ir.expr.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BitVectorVariableExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

/*class Expression {
  public final boolean isDn;
  public final Expression dnVal;
  public final BitVectorExpression bvVal;

  public static Expression dn(Expression dnVal) {
    Preconditions.checkArgument(dnVal.isInductive());
    return new Expression(true, dnVal);
  }

  public static Expression bv(Expression bvVal) {
    Preconditions.checkArgument(bvVal.isBitVector());
    return new Expression(false, bvVal);
  }

  @SuppressWarnings("unchecked")
  protected Expression(boolean isDn, Expression e) {
    this.isDn = isDn;
    if (isDn) {
      this.dnVal = e;
      this.bvVal = null;
    } else {
      this.dnVal = null;
      this.bvVal = e;
    }
  }
}
*/

public class CompressedDomainNamesEncoding_CVC4 extends CompressedDomainNamesEncoding {

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding, IRSingleHeapEncoder heapEncoder) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    return FlatMemoryModel.create(encoding, heapEncoder);
  }
  
  protected final BitVectorIntegerEncoding bitVectorFactory;
  /* The Dn inductive data type */
  protected final InductiveType dn;
  /* The constructors for Dn */
  protected final Constructor indirectConstr, nullConstr, labelConstr,
      undefConstr;
  
  /* Selector for the length of label (a bit vector) in labelConstr */
  protected final Selector lenSel;
  /* Selector for the label field (a bit vector array) in labelConstr */
  protected final Selector labelSel;
  /* Selector for the "rest" field (a Dn value) in labelConstr */
  protected final Selector restSel;
  /* Selector for the offset of an indirect value (a bit vector) in indirectConstr */
  protected final Selector offsetSel ;

  protected final ImmutableSet<BooleanExpression> axioms;
  protected final HashSet<String> predicates;
  protected final HashSet<String> functions;

  /** The raw memory (bit vector array) -> Dn value mapping */
  protected final Expression bitsToDn;
  
  /** The Dn value -> size (in bytes, a bit vector) mapping */
  protected final Expression sizeDn;

  /** Maps a memory array to a string by offseting the indices.
   *  (bit vector array, bit vector base, bit vector size) -> bit vector array
   */
  protected final Expression toBvString;
  
  /** The memory variable (a bit vector array) */
  protected final ArrayVariableExpression memArray;

  /** The type of the memory variable */
  protected final ArrayType memType;
  
  /** Should the undefined case be explicit in the Dn datatype? */
  protected final boolean explicitUndefined;

  protected boolean useFrameAxiom;
  
  protected static int DEFAULT_WORD_SIZE;
  
  public static CompressedDomainNamesEncoding_CVC4 create(
      ExpressionManager exprManager) throws ExpressionFactoryException {
    int cellSize = 
    		Preferences.MEM_ENCODING_FIX.equals(
            Preferences.getString(Preferences.OPTION_MEM_ENCODING)) ? 
                DefaultSize
                : Preferences.isSet(Preferences.OPTION_MEM_CELL_SIZE) ?
                    Preferences.getInt(Preferences.OPTION_MEM_CELL_SIZE) 
                    : DefaultSize;

    int intCellSize = 
    		Preferences.MEM_ENCODING_FIX.equals(
            Preferences.getString(Preferences.OPTION_MEM_ENCODING)) ? 
                (int) (cAnalyzer.getSize(xtc.type.NumberT.INT) * cellSize) 
                : cellSize;
    
    DEFAULT_WORD_SIZE = intCellSize;
    
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager, intCellSize);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(exprManager);
    PointerEncoding<TupleExpression> tupleEncoding = new DefaultPointerEncoding(exprManager);
    
    return new CompressedDomainNamesEncoding_CVC4(integerEncoding,booleanEncoding,arrayEncoding,tupleEncoding);
    
  }
  
  public CompressedDomainNamesEncoding_CVC4(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> tupleEncoding) {
    super(integerEncoding, booleanEncoding, arrayEncoding, tupleEncoding);

    try {
      explicitUndefined = Preferences.isSet(OPTION_EXPLICIT_UNDEFINED);
      useFrameAxiom = Preferences.isSet(OPTION_FRAME_AXIOM);
      
      ExpressionManager exprManager = getExpressionManager();
      BitVectorType wordType = exprManager.bitVectorType(DEFAULT_WORD_SIZE);
      BitVectorType charType = exprManager.bitVectorType(8);
      BitVectorType lenType = exprManager.bitVectorType(6);
      BitVectorType offsetType = exprManager.bitVectorType(14);

      BitVectorType addrType = wordType;
      BitVectorType cellType = charType;

      memType = exprManager.arrayType(addrType, cellType);
      ArrayType stringType = memType;
      memArray = memType.variable(MEM_ARRAY_NAME,true);

      this.bitVectorFactory = (BitVectorIntegerEncoding) getIntegerEncoding();
/*      this.bitVectorFactory = BitVectorExpressionEncoding.create(symbolTables,
          exprManager, memArray);
*/
      /* Create datatype constructors */

      // labelTagSel = exprManager.selector(LABEL_TAG_SELECTOR_NAME, tagType);
      lenSel = exprManager.selector(LENGTH_SELECTOR_NAME, lenType);
      labelSel = exprManager.selector(LABEL_SELECTOR_NAME, stringType);
      /*restSel = exprManager.selector(REST_SELECTOR_NAME, exprManager
          .inductiveTypeDescriptor(DATATYPE_NAME));*/
      restSel = exprManager.selector(REST_SELECTOR_NAME, exprManager
          .inductiveType(DATATYPE_NAME));
      labelConstr = exprManager.constructor(LABEL_CONSTR_NAME, lenSel,
          labelSel, restSel);

      offsetSel = exprManager.selector(OFFSET_SELECTOR_NAME, offsetType);
      indirectConstr = exprManager.constructor(INDIRECT_CONSTR_NAME, offsetSel);

      nullConstr = exprManager.constructor(NULL_CONSTR_NAME);

      /* Create datatype */
      if (explicitUndefined) {
        undefConstr = exprManager.constructor(UNDEF_CONSTR_NAME);
        dn = exprManager.dataType(DATATYPE_NAME, labelConstr, indirectConstr,
            nullConstr, undefConstr);
      } else {
        undefConstr = null;
        dn = exprManager.dataType(DATATYPE_NAME, labelConstr, indirectConstr,
            nullConstr);
      }

      /* Create data constraints */
      ImmutableSet.Builder<BooleanExpression> axiomSetBuilder = ImmutableSet
          .builder();

/*      VariableExpression x = dn.variable("x", true);
      ArrayVariableExpression bits1 = stringType
          .variable("bits1",true);
      ArrayVariableExpression bits2 = stringType
          .variable("bits2",true);
      BitVectorVariableExpression i = addrType.variable("i", true);
      BitVectorVariableExpression j = addrType.variable("j", true);
      BitVectorVariableExpression k = addrType.variable("k", true);*/
      
      VariableExpression x = dn.boundVariable("x", true);
      ArrayVariableExpression bits1 = (ArrayVariableExpression) stringType
          .boundVariable("bits1",true);
      ArrayVariableExpression bits2 = (ArrayVariableExpression) stringType
          .boundVariable("bits2",true);
      BitVectorVariableExpression i = (BitVectorVariableExpression) addrType
          .boundVariable("i", true);
      BitVectorVariableExpression j = (BitVectorVariableExpression) addrType
          .boundVariable("j", true);
      BitVectorVariableExpression k = (BitVectorVariableExpression) addrType
          .boundVariable("k", true);

      /* to_string : (StringType, PtrType, PtrType) -> StringType; */
      toBvString = exprManager
          .functionVar("to_string", exprManager.functionType("to_string", ImmutableList.of(stringType,
              addrType, addrType), stringType), true);

      /*
       * Define the to_string function.
       * 
       * ASSERT FORALL (str : StringType, base, len, i : PtrType) :
       * to_string(str,base,len)[i] = IF i < len THEN str[BVPLUS(N,base,i)] ELSE
       * 0 ENDIF
       */
      BooleanExpression toStringAxiom = exprManager.forall(ImmutableList.of(
          bits1, i, j, k), bitVectorFactory.eq(
              doToBvString(bits1, i, j)
                  .index(k).asBitVector(),
                  bitVectorFactory.lessThan(k, j).ifThenElse(
                  bits1.index( i.plus(addrType.getSize(), k)), 
                  exprManager.bitVectorZero(addrType.getSize()))
              .asBitVector()));

      axiomSetBuilder.add(toStringAxiom);

      /*
       * bits_to_dn : (StringType, PtrType) -> Dn;
       */

      bitsToDn = exprManager.functionVar(FUN_INTERNAL_DN, exprManager.functionType(FUN_INTERNAL_DN,
          ImmutableList.of(stringType,
          addrType), dn), true);
      /* sizeDn : Dn -> AddrType */
      sizeDn = exprManager.functionVar(FUN_SIZE_DN, exprManager.functionType(FUN_SIZE_DN, dn, addrType), true);

      List<Expression> bitsToDnPattern = ImmutableList
          .of(exprManager.applyExpr(bitsToDn, bits1, i));
      IOUtils.debug().pln("PATTERN:" + bitsToDnPattern);

      /*
       * Define the mapping of bit-vector inputs to Dn constructors (i.e., the
       * following axioms decode the type tag).
       */

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN bits[i] = 0hex00 ⇒ is_nullt(x)
       */
      BooleanExpression nullDn = exprManager.forall(ImmutableList.of(
          bits1, i), toDnCase(bitVectorFactory.eq(
          stringDeref(bits1, i), bitVectorFactory.zero()), testDn(nullConstr,
          bits1, i)), bitsToDnPattern);

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN bits[i][7:6] = 0bin00 ∧ bits[i][5:0] ≠ 0bin00000
       * ⇒ is_label(x)
       */
      BooleanExpression labelDn = exprManager.forall(ImmutableList.of(
          bits1, i), toDnCase(exprManager.and(
          bitVectorFactory.eq(exprManager.extract(stringDeref(bits1, i),
              6, 7), exprManager.bitVectorConstant("00")), bitVectorFactory
              .neq(exprManager.extract(stringDeref(bits1, i), 0, 5),
                  exprManager.bitVectorConstant("000000"))), testDn(labelConstr,
          bits1, i)), bitsToDnPattern);

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN bits[i][7:6] = 0bin11 ⇒ is_indirect(x)
       */

      BooleanExpression indirectDn = exprManager.forall(ImmutableList.of(
          bits1, i), toDnCase(bitVectorFactory.eq(
          exprManager.extract(stringDeref(bits1, i), 6, 7), exprManager
              .bitVectorConstant("11")), testDn(indirectConstr, bits1, i)),
          bitsToDnPattern);

      axiomSetBuilder.add(nullDn, labelDn, indirectDn);

      /* Cases for undefined fall out, er, implicitly from the iff. rules above. */
/*      if (explicitUndefined) {
        
         * If none of the other constructor tags match, then we use undefined.
         * 
         * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
         * bits_to_dn(bits,i) IN bits[i][7:6] = 0bin10 ∨ bits[i][7:6] = 0bin01 ⇒
         * is_undefined(x)
         

        IBooleanExpression unknownDn = exprManager.forall(ImmutableList.of(
            bits1, i), exprManager.or(
            bitVectorFactory.eq(exprManager.extract(
                stringDeref(bits1, i), 6, 7), exprManager
                .bitVectorConstant("10")),
            bitVectorFactory.eq(exprManager.extract(
                stringDeref(bits1, i), 6, 7), exprManager
                .bitVectorConstant("01"))).implies(
            testDn(undefConstr, bits1, i)), bitsToDnPattern);
        axiomSetBuilder.add(unknownDn);
      }*/

      /*
       * Define the values of Dn fields in terms of the bit-vector input.
       */

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN is_label(x) ⇒ len(x) = bits[i][5:0] AND label(x)
       * = to_string(bits,BVPLUS(32,i,0bin1),len(x)) AND rest(x) =
       * bits_to_dn(bits,BVPLUS(32,i,len(x),0bin1))
       */
      BitVectorExpression iPlusOne = exprManager.plus(addrType.getSize(),i,
          exprManager.bitVectorOne(addrType.getSize()));
      BooleanExpression bitsToLabel1 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, exprManager.applyExpr(bitsToDn, bits1, i)),
          bitVectorFactory.eq(exprManager.asBitVector(
              exprManager.select(lenSel, 
                  exprManager.applyExpr(bitsToDn, bits1, i))), 
                  exprManager.extract(stringDeref(bits1, i), 0, 5))), bitsToDnPattern);
      BooleanExpression bitsToLabel2 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, exprManager.applyExpr(bitsToDn, bits1, i)), exprManager
          .eq(exprManager.select(labelSel, exprManager.applyExpr(bitsToDn, 
              bits1, i)), exprManager.applyExpr(toBvString, ImmutableList.of(
              bits1, iPlusOne, exprManager.zeroExtend(exprManager
                  .select(lenSel, exprManager.applyExpr(bitsToDn, bits1, i)), addrType
                  .getSize()))))), bitsToDnPattern);
      BooleanExpression bitsToLabel3 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, exprManager.applyExpr(bitsToDn, bits1, i)), exprManager
          .eq(exprManager.select(restSel, exprManager.applyExpr(bitsToDn, 
              bits1, i)), exprManager.applyExpr(bitsToDn, bits1, exprManager
              .plus(addrType.getSize(), iPlusOne, exprManager.select(lenSel, exprManager.applyExpr(bitsToDn, 
                  bits1, i)))))), bitsToDnPattern);

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN is_indirect(x) ⇒ offset(x) = bits[i][5:0] @
       * bits[BVPLUS(32,i,0bin1)]
       */
      BooleanExpression bitsToIndirect = exprManager.forall(ImmutableList.of(
          bits1, i), exprManager.implies(exprManager.testConstructor(
          indirectConstr, exprManager.applyExpr(bitsToDn, bits1, i)), bitVectorFactory.eq(
          exprManager.asBitVector(exprManager.select(offsetSel,
              exprManager.applyExpr(bitsToDn, bits1, i))), exprManager.concat(exprManager
              .extract(stringDeref(bits1, i), 0, 5), exprManager.index(bits1,
              iPlusOne)))), bitsToDnPattern);

      axiomSetBuilder.add(bitsToLabel1, bitsToLabel2, bitsToLabel3,
          bitsToIndirect);

      if (useFrameAxiom) {
        /*
         * A frame axiom: if none of the bytes inside the value changed, then
         * the value hasn't changed.
         * 
         * In the explicit encoding, this shouldn't be required, but it seems to
         * help to have it around.
         * 
         * In the implicit encoding, it becomes necessary. The idea is as
         * follows: if bits1 ≠ bits2 and Dn(bits1,i) is not well-defined, then
         * Dn(bits1,i) = Dn(bits2,i) is not required, even if we know bits1[i] =
         * bits2[i]. This can cause trouble, even for well-defined values. So we
         * require that Dn(bits1,i) = Dn(bits2,i) if bits1 and bits2 agree on
         * all the bytes between i and i + sizeDn(bits1,i). In other words,
         * bytes "outside" of Dn(bits1,i) can't "interfere" with the result of
         * Dn.
         * 
         * ASSERT (FORALL (bits1, bits2: StringType, q: PtrType) : (bits1[q] =
         * bits2[q] AND FORALL (p:PtrType):
         * (BVLE(BVSUB(8,p,q),BVSUB(8,sizeDn(bits_to_dn(bits1,q)),q)) =>
         * bits1[p] = bits2[p])) => bits_to_dn((bits1,q)) =
         * bits_to_dn((bits2,q)))
         */

        /*
         * [chris 10/4/2009] There's a mysterious crash if I try to add
         * triggers.
         */
      BooleanExpression frameAxiom = exprManager.forall(ImmutableList
          .of(bits1, bits2, j),
          stringDeref(bits1,j).eq(stringDeref(bits2,j)).and(
              exprManager.forall(i,
          exprManager.lessThanOrEqual(j, i).and(
              exprManager.lessThan(i, exprManager.plus(addrType.getSize(), j, 
                  exprManager.applyExpr(sizeDn, exprManager.applyExpr(bitsToDn, bits1, j))))).implies(
          stringDeref(bits1, i).eq(stringDeref(bits2, i))))).implies(
          exprManager.applyExpr(bitsToDn, bits1, j).eq(exprManager.applyExpr(bitsToDn, bits2, j)))
          // triggers cause a crash, for some reason
          /*,
          ImmutableList.of(exprManager.applyExpr(bitsToDn, bits1, j), exprManager.applyExpr(bitsToDn, bits2, j))*/
          );

        /*
         * IBooleanExpression frameAxiom = exprManager.forall(
         * ImmutableList.of(bits1, bits2, i, j), exprManager.implies(
         * exprManager.implies(exprManager.andExpression(exprManager
         * .lessThanOrEqual(j, i), exprManager.lessThan(i, exprManager
         * .plus(j, applySizeDn(bits1, j)))),
         * 
         * // exprManager.lessThanOrEqual(exprManager .minusExpr(i, j), //
         * exprManager.minusExpr(applySizeDn(bits1, j), j)),
         * exprManager.eq(stringDeref(bits1, i), stringDeref( bits2,
         * i))), exprManager.eq(applyBitsToDn(bits1, j),
         * applyBitsToDn(bits2, j))));
         */
        axiomSetBuilder.add(frameAxiom);
      }

      /* Define the sizeDn function */

      List<BitVectorExpression> sizeDnPattern = ImmutableList.of(applySizeDn(x));

      /*
       * ASSERT is_label(x) => sizeDn(x) = len(x) + sizeDn(rest(x)) + 1
       */
      BooleanExpression sizeLabel = exprManager.forall(
          ImmutableList.of(x), exprManager.implies(exprManager
              .testConstructor(labelConstr, x), bitVectorFactory.eq(applySizeDn(x), exprManager
              .plus(addrType.getSize(),exprManager.select(lenSel, x), exprManager
                  .applyExpr(sizeDn, exprManager.select(restSel, x)),
                  bitVectorFactory.one()))),
                  sizeDnPattern);

      /*
       * ASSERT is_indirect(x) => sizeDn(x) = 2
       */
      BooleanExpression sizeIndirect = exprManager.forall(ImmutableList.of(x),
          exprManager.implies(exprManager.testConstructor(indirectConstr, x),
              bitVectorFactory.eq(applySizeDn(x), bitVectorFactory.constant(2))),
          sizeDnPattern);
      /*
       * ASSERT is_nullt(x) => sizeDn(x) = 1
       */
      BooleanExpression sizeNull = exprManager.forall(ImmutableList.of(x),
          exprManager.implies(exprManager.testConstructor(nullConstr, x),
              bitVectorFactory.eq(applySizeDn(x), bitVectorFactory.one())), sizeDnPattern);

      axiomSetBuilder.add(sizeIndirect, sizeLabel, sizeNull);

      if (explicitUndefined) {
        /*
         * The size of unknown is 0 ,i.e., there is no valid Dn value here.
         * 
         * ASSERT is_unknown(x) => sizeDn(x) = 0
         */
        BooleanExpression sizeUnknown = exprManager.forall(ImmutableList
            .of(x), exprManager.testConstructor(undefConstr, x).implies(
            bitVectorFactory.eq(applySizeDn(x),
                bitVectorFactory.zero())),
                sizeDnPattern);
        axiomSetBuilder.add(sizeUnknown);
      }

      axioms = axiomSetBuilder.build();
      predicates = Sets.newHashSet();
      functions = Sets.newHashSet(FUN_REST, FUN_DN, FUN_SIZE_DN);

      /*
       * dnValSel = exprManager.selector("dn_val", dn); dnValConstr =
       * exprManager.constructor("dn_val", dnValSel); bvValSel =
       * exprManager.selector("bv_val", memType.getElementType()); bvValConstr =
       * exprManager.constructor("bv_val", bvValSel); valType =
       * exprManager.dataType("cdn_val", bvValConstr, dnValConstr);
       */
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }

  protected ArrayExpression doToBvString(ArrayExpression arr,
      Expression base, Expression len) {
    return getExpressionManager().applyExpr(toBvString, arr, base, len).asArray();
  }

  /* If we're using an explicit undefined, then the data constraints define
   * the datatype constructor. Otherwise, the constraints only imply the constructor.
   */
  protected BooleanExpression toDnCase(Expression dataConstraints,
      Expression constructorAssertion) {
    if (explicitUndefined) {
      return dataConstraints.asBooleanExpression().iff(constructorAssertion);
    } else {
      return dataConstraints.asBooleanExpression().implies(constructorAssertion);
    }
  }

  protected BitVectorExpression applySizeDn(Expression x) {
    Preconditions.checkArgument(x.isInductive());
    return getExpressionManager().applyExpr(sizeDn, x).asBitVector();
  }

  protected BitVectorExpression stringDeref(
      ArrayExpression bits1,
      BitVectorExpression p) {
    return bits1.index(p).asBitVector();
  }

  protected BooleanExpression testDn(Constructor constr,
      Expression bits1,
      BitVectorExpression p) throws TheoremProverException {
    return getExpressionManager().applyExpr(bitsToDn, bits1, p).asInductive().test(constr);
  }
  
  @Override
  public Expression functionCall(String name, Iterable<? extends Expression> argsIter) {
    List<Expression> args = ImmutableList.copyOf(argsIter);
    try {
      if (FUN_DN.equals(name)) {
        checkArgument(args.size() == 1);

        return bvValToDn(args.get(0));
      }

      ExpressionManager exprManager = getExpressionManager();
      if (FUN_IS_INDIRECT.equals(name)) {
        checkArgument(args.size() == 1);

        BooleanExpression b = exprManager.testConstructor(
            indirectConstr, bvValToDn(args.get(0)));
        return castToInteger(b);
      }

      if (FUN_IS_LABEL.equals(name)) {
        checkArgument(args.size() == 1);

        BooleanExpression b = exprManager.testConstructor(
            labelConstr, bvValToDn(args.get(0)));
        return castToInteger(b);
      }

      if (FUN_IS_NULLT.equals(name)) {
        checkArgument(args.size() == 1);

        BooleanExpression b = exprManager.testConstructor(
            nullConstr, bvValToDn(args.get(0)));
        return castToInteger(b);
      }

      if (FUN_REST.equals(name)) {
        checkArgument(args.size() == 1);
        
        return exprManager.select(restSel, bvValToDn(args.get(0)));
      }

      if (FUN_LEN.equals(name)) {
        checkArgument(args.size() == 1);

        return exprManager.select(lenSel, bvValToDn(args.get(0)));
      }

      if (FUN_SIZE_DN.equals(name)) {
        checkArgument(args.size() == 1);

        return exprManager.asBitVector(exprManager.applyExpr(sizeDn, bvValToDn(args.get(0))));
      }

      /* Otherwise, pass through to the underlying bit-vector encoding */
      List<BitVectorExpression> newArgs = Lists
          .newArrayListWithCapacity(args.size());
      for (Expression e : args) {
        checkArgument(e.isBitVector());
        newArgs.add(e.asBitVector());
      }

      return super.functionCall(name, newArgs);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }

  protected Expression bvValToDn(Expression expr)
      throws TheoremProverException {
    Preconditions.checkArgument(expr.isBitVector());
    Expression x = getExpressionManager().applyExpr(bitsToDn,
        memArray, expr);
    return x;
  }

  // @Override
  /*
   * public IExpression<IInductiveType> applyFunction(String name,
   * IExpression<?> arg) { if( FUN_DN.equals(name) ) { return
   * exprManager.functionApplication(bitsToDn, (IExpression<ITupleType>)arg); }
   * throw new IllegalArgumentException(name); else ( FUN_REST.equals(name) ) {
   * return exprManager.functionApplication(bitsToDn,
   * (IExpression<ITupleType>)arg);
   * 
   * } }
   */

  // @Override
  /*
   * public IBooleanExpression applyPredicate(String name, IExpression<?>
   * arg1, IExpression<?> arg2) { if( FUN_DN.equals(name) ) {
   * IExpression<IInductiveType> x = exprManager.functionApplication(bitsToDn,
   * (IExpression<ITupleType>)arg1); IExpression<IInductiveType> y =
   * exprManager.functionApplication(bitsToDn, (IExpression<ITupleType>)arg2); }
   * // TODO Auto-generated method stub return null; }
   */
  // @Override
  public Set<String> getFunctions() {
    return functions;
  }

  // @Override
  public Set<String> getPredicates() {
    return predicates;
  }

/*  @Override
  public BooleanExpression allocated(Expression ptr, Expression size)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(!ptr.isDn);
    Preconditions.checkArgument(!size.isDn);
    return bitVectorFactory.allocated(ptr.bvVal, size.bvVal);
  }*/

  @Override
  public ImmutableSet<BooleanExpression> getAssumptions() {
    return ImmutableSet.copyOf(Sets.union(axioms, super.getAssumptions()));
  }

  int getAddressSize() { return memType.getIndexType().asBitVectorType().getSize(); }
  int getWordSize() { return memType.getElementType().asBitVectorType().getSize(); }
/*  @Override
  public ArrayType getStateType()
      {
    return memType;
  }*/
}
