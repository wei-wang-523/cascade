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

import java.util.Set;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.ir.expr.AbstractExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorIntegerEncoding;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModel;
import edu.nyu.cascade.ir.expr.DefaultArrayEncoding;
import edu.nyu.cascade.ir.expr.DefaultBooleanEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.UnimplementedTupleEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Constructor;

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

public abstract class CompressedDomainNamesEncoding extends AbstractExpressionEncoding {

  protected static final String MEM_ARRAY_NAME = "m";

  protected static final String DATATYPE_NAME = "Dn";

  protected static final String LABEL_CONSTR_NAME = "clabel";
  
  protected static final String LENGTH_SELECTOR_NAME = "len";
  protected static final String LABEL_SELECTOR_NAME = "slabel";
  protected static final String REST_SELECTOR_NAME = "rest";

  protected static final String INDIRECT_CONSTR_NAME = "indirect";
  
  protected static final String OFFSET_SELECTOR_NAME = "offset";

  protected static final String NULL_CONSTR_NAME = "nullt";

  protected static final String FUN_DN = DATATYPE_NAME;
  protected static final String FUN_REST = REST_SELECTOR_NAME;
  protected static final String FUN_LEN = LENGTH_SELECTOR_NAME;

  protected static final String FUN_INTERNAL_DN = "toDn";
  protected static final String FUN_SIZE_DN = "sizeDn";

  protected static final String FUN_IS_LABEL = "is_label";
  protected static final String FUN_IS_INDIRECT = "is_indirect";
  protected static final String FUN_IS_NULLT = "is_nullt";

  public static final String DATATYPES_EXPLICIT_UNDEFINED = "dt_explicit_undef";

  protected static final String UNDEF_CONSTR_NAME = "undefined";

  public static final String OPTION_EXPLICIT_UNDEFINED = "explicit-undef";

  public static final String OPTION_FRAME_AXIOM = "frame-axiom";

  public static MemoryModel createMemoryModel(ExpressionEncoding encoding) { 
    Preconditions.checkArgument( encoding.getIntegerEncoding().getType().isBitVectorType() );
    return BitVectorMemoryModel.create(encoding);
  }

  public static int DEFAULT_WORD_SIZE;
  
  public CompressedDomainNamesEncoding(ExpressionManager exprManager) {
    super(BitVectorIntegerEncoding.create(exprManager, intCellSize),
        new DefaultBooleanEncoding(exprManager),
        new DefaultArrayEncoding(exprManager),
        new UnimplementedTupleEncoding<TupleExpression>());
    DEFAULT_WORD_SIZE = intCellSize;
  }

  protected abstract ArrayExpression doToBvString(ArrayExpression arr,
      Expression base, Expression len) ;

  /* If we're using an explicit undefined, then the data constraints define
   * the datatype constructor. Otherwise, the constraints only imply the constructor.
   */
  protected abstract BooleanExpression toDnCase(Expression dataConstraints,
      Expression constructorAssertion) ;

  protected abstract BitVectorExpression applySizeDn(Expression x) ;

  protected BitVectorExpression stringDeref(
      Expression bits1,
      BitVectorExpression p) {
    return bits1.asArray().index(p).asBitVector();
  }

  protected abstract BooleanExpression testDn(Constructor constr,
      Expression bits1,
      BitVectorExpression p) ;

  protected abstract Expression bvValToDn(Expression expr) ;

  public abstract Set<String> getFunctions() ;

  public abstract Set<String> getPredicates() ;

  abstract int getAddressSize() ;
  abstract int getWordSize() ;

}
