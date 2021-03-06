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

import xtc.type.PointerT;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.BitVectorFixedSizeEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.LinearPointerEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

public class CompressedDomainNamesEncoding_Z3 extends CompressedDomainNamesEncoding {
  
  private final BitVectorIntegerEncoding bitVectorFactory;

  /* The Dn inductive data type */
  private final InductiveType dn;
  
  /* The constructors for Dn */
  private final Constructor indirectConstr, nullConstr, labelConstr,
      undefConstr;
  
  /* Selector for the length of label (a bit vector) in labelConstr */
  private final Selector lenSel;
  /* Selector for the label field (a bit vector array) in labelConstr */
  private final Selector labelSel;
  /* Selector for the "rest" field (a Dn value) in labelConstr */
  private final Selector restSel;

  /* Selector for the offset of an indirect value (a bit vector) in indirectConstr */
  private final Selector offsetSel ;

  private final ImmutableSet<BooleanExpression> axioms;

  private final HashSet<String> predicates;

  private final HashSet<String> functions;

  /** The raw memory (bit vector array) -> Dn value mapping */
  private final FunctionExpression bitsToDn;
  
  /** The Dn value -> size (in bytes, a bit vector) mapping */
  private final FunctionExpression sizeDn;

  /** Maps a memory array to a string by offseting the indices.
   *  (bit vector array, bit vector base, bit vector size) -> bit vector array
   */
  private final FunctionExpression toBvString;
  
  /** The memory variable (a bit vector array) */
  private final ArrayExpression memArray;

  /** The type of the memory variable */
  private final ArrayType memType;
  
  /** Should the undefined case be explicit in the Dn datatype? */
  private final boolean explicitUndefined;

  private boolean useFrameAxiom;
  
  static CompressedDomainNamesEncoding_Z3 create(
      ExpressionManager expressionManager) throws ExpressionFactoryException {
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(expressionManager);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(expressionManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new DefaultArrayEncoding(expressionManager);  	
    PointerEncoding<? extends Expression> pointerEncoding = LinearPointerEncoding.create(
    		BitVectorFixedSizeEncoding.create(expressionManager, (BitVectorIntegerEncoding) integerEncoding, 
    				CType.getInstance().getWidth(PointerT.TO_VOID)));
    
    return new CompressedDomainNamesEncoding_Z3(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
    
  }
  
  private CompressedDomainNamesEncoding_Z3(
  		IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<? extends Expression> pointerEncoding) {
    super(integerEncoding, booleanEncoding, arrayEncoding, pointerEncoding);

    try {
      explicitUndefined = Preferences.isSet(OPTION_EXPLICIT_UNDEFINED);
      useFrameAxiom = Preferences.isSet(OPTION_FRAME_AXIOM);
      
      ExpressionManager exprManager = getExpressionManager();
      BitVectorType wordType = exprManager.bitVectorType(8);
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
          .inductiveType(DATATYPE_NAME), 0);
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
      
      Expression x = exprManager.boundExpression("x", 0, dn, true);
      ArrayExpression bits1 = stringType.boundExpression("bits1", 1, true);
      ArrayExpression bits2 = stringType.boundExpression("bits2", 2, true);
      BitVectorExpression i = addrType.boundExpression("i", 3, true);
      BitVectorExpression j = addrType.boundExpression("j", 4, true);
      BitVectorExpression k = addrType.boundExpression("k", 5, true);

      /* to_string : (StringType, PtrType, PtrType) -> StringType; */
      toBvString = exprManager.functionDeclarator("to_string",
      		exprManager.functionType(
      				ImmutableList.of(stringType, addrType, addrType), stringType), true);

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
                  bits1.index( exprManager.bitVectorPlus(addrType.getSize(), i, k)), 
                  exprManager.bitVectorZero(addrType.getSize()))
              .asBitVector()));

      axiomSetBuilder.add(toStringAxiom);

      /*
       * bits_to_dn : (StringType, PtrType) -> Dn;
       */

      bitsToDn = exprManager.functionDeclarator(FUN_INTERNAL_DN, 
      		exprManager.functionType(ImmutableList.of(stringType, addrType), dn), true);
      /* sizeDn : Dn -> AddrType */
      sizeDn = exprManager.functionDeclarator(FUN_SIZE_DN, 
      		exprManager.functionType(dn, addrType), true);

      List<Expression> bitsToDnPattern = ImmutableList
          .of(bitsToDn.apply(bits1, i));
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
          bits1, i)) /*, bitsToDnPattern*/);

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
          bits1, i))/*, bitsToDnPattern*/);

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN bits[i][7:6] = 0bin11 ⇒ is_indirect(x)
       */

      BooleanExpression indirectDn = exprManager.forall(ImmutableList.of(
          bits1, i), toDnCase(bitVectorFactory.eq(
          exprManager.extract(stringDeref(bits1, i), 6, 7), exprManager
              .bitVectorConstant("11")), testDn(indirectConstr, bits1, i))/*,
          bitsToDnPattern*/);

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
      BitVectorExpression iPlusOne = exprManager.bitVectorPlus(addrType.getSize(),i,
          exprManager.bitVectorOne(addrType.getSize()));
      BooleanExpression bitsToLabel1 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, bitsToDn.apply(bits1, i)),
          bitVectorFactory.eq(exprManager.asBitVector(exprManager.select(lenSel, bitsToDn
              .apply(bits1, i))), exprManager.extract(stringDeref(bits1,
              i), 0, 5)))/* , bitsToDnPattern */);
      BooleanExpression bitsToLabel2 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, bitsToDn.apply(bits1, i)), exprManager
          .eq(exprManager.select(labelSel, bitsToDn.apply(
              bits1, i)), exprManager.applyExpr(toBvString, ImmutableList.of(
              bits1, iPlusOne, exprManager.zeroExtend(
              		addrType.getSize(), 
              		exprManager.select(lenSel, bitsToDn.apply(bits1, i)))))))/* , bitsToDnPattern */);
      BooleanExpression bitsToLabel3 = exprManager.forall(ImmutableList
          .of(bits1, i), exprManager.implies(exprManager
          .testConstructor(labelConstr, bitsToDn.apply(bits1, i)), exprManager
          .eq(exprManager.select(restSel, bitsToDn.apply(
              bits1, i)), exprManager.applyExpr(bitsToDn, bits1, exprManager
              .bitVectorPlus(addrType.getSize(), iPlusOne, 
              		exprManager.select(lenSel, bitsToDn.apply(bits1, i))))))/* , bitsToDnPattern */);

      /*
       * ASSERT FORALL (bits : StringType, i : PtrType) : LET x =
       * bits_to_dn(bits,i) IN is_indirect(x) ⇒ offset(x) = bits[i][5:0] @
       * bits[BVPLUS(32,i,0bin1)]
       */
      BooleanExpression bitsToIndirect = exprManager.forall(ImmutableList.of(
          bits1, i), exprManager.implies(exprManager.testConstructor(
          indirectConstr, bitsToDn.apply(bits1, i)), bitVectorFactory.eq(
          exprManager.asBitVector(exprManager.select(offsetSel,
              bitsToDn.apply(bits1, i))), exprManager.concat(exprManager
              .extract(stringDeref(bits1, i), 0, 5), exprManager.index(bits1,
              iPlusOne))))/* , bitsToDnPattern */);

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
              exprManager.lessThan(i, exprManager.bitVectorPlus(
              		addrType.getSize(), j, 
              		sizeDn.apply(bitsToDn.apply(bits1, j))))).implies(
          stringDeref(bits1, i).eq(stringDeref(bits2, i))))).implies(
          bitsToDn.apply(bits1, j).eq(bitsToDn.apply(bits2, j)))
          // triggers cause a crash, for some reason
          /*,
          ImmutableList.of(bitsToDn.apply(bits1, j), bitsToDn.apply(bits2, j))*/
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
              .bitVectorPlus(addrType.getSize(),
              		exprManager.select(lenSel, x),
              		exprManager.applyExpr(sizeDn, exprManager.select(restSel, x)),
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

  protected ArrayExpression doToBvString(ArrayExpression bits1,
      Expression base, Expression len) {
    return toBvString.apply(bits1, base, len).asArray();
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
    return sizeDn.apply(x).asBitVector();
  }

  protected BitVectorExpression stringDeref(
      ArrayExpression bits1,
      BitVectorExpression p) {
    return bits1.index(p).asBitVector();
  }

  protected BooleanExpression testDn(Constructor constr,
      Expression bits1,
      BitVectorExpression p) throws TheoremProverException {
    return bitsToDn.apply(bits1, p).asInductive().test(constr);
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

        return exprManager.asBitVector(sizeDn.apply(bvValToDn(args.get(0))));
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
  int getValueSize() { return memType.getElementType().asBitVectorType().getSize(); }
/*  @Override
  public ArrayType getStateType()
      {
    return memType;
  }*/
}
