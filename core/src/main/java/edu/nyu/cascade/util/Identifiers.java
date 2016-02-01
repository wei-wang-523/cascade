package edu.nyu.cascade.util;

import static edu.nyu.cascade.util.Identifiers.IdType.DEFAULT;

import java.math.BigInteger;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.SymbolTable;

public class Identifiers {
  
	/** The infix for naming */
  public static final String SCOPE_INFIX = ".";
  public static final String UNDERLINE = "_";
  
  
  /** The reserved name in Rats! parser */
  public static final String NULL_LOC_NAME = "<null>";
	public static final String FUNC = "__func__";
	
	
	/** The name for global control flow graph (cfg-builder) */
  public static final String GLOBAL_CFG = "globalCfg";
  
	
	/** The elements associated with state expression or variable sets in pointer analysis */
	public static final String SCOPE = "scope";
	public static final String TYPE = "type";
  
  
  /** The pointer type (refType, intType) created for sync mem encoding */
  public static final String REF_TYPE_NAME = "refType";
  public static final String NULL_PTR_NAME = "nullRef";
  public static final String PTR_TYPE_NAME = "ptrType";
  
	/** Cascade created auxiliary variables */
  
  /** The names for condition, string variable, allocated region and return variable */
  public static final String STRING_VAR_PREFIX = "string_var";
  public static final String RETURN_VAR_PREFIX = "return";
  public static final String REGION_VARIABLE_NAME = "region";
  public static final String CONSTANT = "Constant";
  public static final String TEST_VAR_PREFIX = "condition";
  
  /** Label for auxiliary variables created by cascade internally */
	public static final String AUXLABEL = "auxVarLabel";
	
  /** Label for variables created by control file as quantified variable */
	public static final String CTRLVAR = "ctrlVarLabel";

	/** Label for variables with*/
	public static final String HOARE_VAR = "hoareVar";
	
  
  /** The elements about path-based encoding */
	
	/** The empty path (or fresh path) created for each path encoding (independent) */
	public static final String SRCPATH = "srcPath";
	
	public static final String ITERTIMES = "iterTimes";	
	
	/** The elements about function call statement encoding */
	
	/** The statement: y = f(x) */
	public static final String STMTFUNCASSIGN = "stmtFuncAssign";
	
	/** The statement: f(x) */
	public static final String STMTFUNC = "stmtFunc";
	
	/** The argument expressions of function call */
	public static final String ARGUMENTS = "arguments";
	
	/** The function name */
	public static final String FUNCNAME = "funcName";

	public static enum IdType {
    DEFAULT,
    C,
    SPL
  };
  private static final Set<String> identifiers = Sets.newHashSet();;
  private static final Set<String> internalLabels = Sets.newHashSet();

  private static final Pattern DEFAULT_VALID_ID = Pattern
      .compile("[A-Za-z_][A-Za-z0-9_']*");

  private static final Pattern C_VALID_ID = Pattern.compile("[A-Za-z_][A-Za-z0-9_]*");
  
  private static final char DEFAULT_REPLACEMENT_CHAR = '_';
  
	private static String addWart(String id) {
    Preconditions.checkArgument(isValidId(id));
    if (!identifiers.contains(id)) {
      identifiers.add(id);
      return id;
    }
    
    BigInteger idWart = BigInteger.ZERO;
    String maybeUid = id + "_" + idWart;
    while( identifiers.contains(maybeUid) ){
      idWart = idWart.add(BigInteger.ONE);
      maybeUid = id + "_" + idWart;
    }
    
    identifiers.add(maybeUid);
    return maybeUid;
  }

  public static String defineFreshLabel(SymbolTable symbolTable, Object def) {
    String label = freshLabel(symbolTable);
    defineLabel(symbolTable,label,def);
    return label;
  }
  public static void defineLabel(SymbolTable symbolTable, String name, Object def) {
    Preconditions.checkNotNull(symbolTable);
    Preconditions.checkNotNull(name);
    
    if( symbolTable.labelIsDefined(name) ) {
      throw new IllegalArgumentException("Multiply defined label: " + name);
    }
    
    symbolTable.defineLabel(name, def);
  }

  public static String freshLabel(SymbolTable symbolTable) {
    String name;
    do {
      name = uniquify("lbl");
    } while( symbolTable.labelIsDefined(name) );
  
    internalLabels.add(name);
    return symbolTable.toLabelName(name);
  }

  /**
   * Returns a name that is not defined in the current scope of the given
   * <code>symbolTable</code>, using <code>base</code> as a starting point.
   * <code>base</code> will be mangled if it includes any non-identifier
   * characters.
   */
  public static String freshName(SymbolTable symbolTable, String base) {
    return freshName(symbolTable,base,null);
  }

  /**
   * Returns a name that is not defined in the given <code>namespace</code> in
   * the current scope of the given <code>symbolTable</code>, using
   * <code>base</code> as a starting point. <code>base</code> will be mangled if
   * it includes any non-identifier characters.
   */
  public static String freshName(SymbolTable symbolTable, String base,
      String namespace) {
    String name;

    do {
      name = toValidId(uniquify(base), IdType.C);
    } while (symbolTable.isDefined(name, namespace));
    return name;
  }

  public static boolean isInternalLabel(String label) {
    return internalLabels.contains(label);
  }
  
  public static boolean isValidId(String s) {
    return isValidId(s, IdType.DEFAULT);
  }

  public static boolean isValidId(String s, IdType type) {
    return patternForIdType(type).matcher(s).matches();
  }

  private static Pattern patternForIdType(IdType idType) {
    switch (idType) {
    case DEFAULT:
      return DEFAULT_VALID_ID;
    case C:
    case SPL:
      return C_VALID_ID;
    default:
      assert (false);
      return null;
    }
  }
  
  private static char replacementCharForIdType(IdType idType) {
    return DEFAULT_REPLACEMENT_CHAR;
  }
  
  /**
   * Returns a valid id based on the input <code>s</code>. A valid id starts
   * witha letter or underscore and contains only letters, digits, underscores,
   * and the prime symbol (<code>'</code>).
   */
  public static String toValidId(String s) {
    return toValidId(s, DEFAULT);
  }
  
  public static String toValidId(String s, IdType type) {
    Pattern pattern = patternForIdType(type);
    char replacementChar = replacementCharForIdType(type);
    
    String result = s;
    Matcher matcher = pattern.matcher(result);
    while( !matcher.matches() ) {
      if( !matcher.lookingAt() ) {
        result = replacementChar + result;
      } else {
        int i = matcher.end();
        result = result.substring(0,i) + "_" + result.substring(i+1,result.length());
      }
      matcher = pattern.matcher(result);
    }
    
   return result;

/*     Replace non-id chars with underscore 
    String newString = s.replaceAll("[^A-Za-z0-9_']", "_");
     If the string begins with a digit or prime, add an underscore prefix 
    if (newString.matches("^[0-9']")) {
      newString = "_" + newString;
    }
   return newString;
 */
  }

  /**
   * Returns a name that has not been previously returned by this method, using
   * <code>base</code> as a starting point. <code>base</code> will be mangled if
   * it includes any non-identifier characters.
   */
  public static String uniquify(String id) {
    return addWart(toValidId(id));
  }
  
  public static String fullyQualify(String qName) {
    return qName.charAt(0) != '.' ? '.' + qName : qName;
  }

}
