package at.logic.gapt.formats.babel

import ast._

/**
 * Created by sebastian on 22.02.16.
 */

/**
 * A signature for the Babel parser.
 */
abstract class Signature {
  /**
   * Decides whether the symbol with the given identifier should be a variable or constant, and what its type should be.
   * @param s The name of the symbol.
   * @return Either IsVar(type) or IsConst(type).
   */
  def apply( s: String ): VarConst

  /**
   * Returns true iff the symbol with the given identifier is a variable.
   * @param s The name of the symbol.
   * @return
   */
  def isVar( s: String ): Boolean = apply( s ).isVar

  /**
   * Returns the type of the symbol with the given identifier.
   * @param s The name of the symbol.
   * @return
   */
  def getType( s: String ): ast.Type = apply( s ).t
}

/**
 * Contains various methods for generating signatures.
 *
 */
object Signature {
  /**
   * Creates a signature from a set of identifiers.
   * @param set A set of identifiers. The elements of the set are the (only) constants.
   * @return
   */
  def apply( set: Set[Ident] ): MapSignature = MapSignature( set.map( i => ( i.name, i.ty ) ).toMap )

  /**
   * Creates a signature from a set of strings.
   * @param set A set of names. The elements of the set are the (only) constants. Their types are arbitrary.
   * @return
   */
  def apply( set: Set[String] )( implicit d: DummyImplicit ): MapSignature = apply( set map { s => Ident( s, freshTypeVar() ) } )

  /**
   * Creates a signature from a list of identifiers.
   * @param sym The first identifier.
   * @param syms The rest of the identifiers.
   * @return
   */
  def apply( sym: Ident, syms: Ident* ): MapSignature = MapSignature( ( sym +: syms ).map( i => ( i.name, i.ty ) ).toMap )

  /**
   * Creates a signature from a list of strings.
   * @param sym The first string.
   * @param syms The rest of the strings.
   * @return
   */
  def apply( sym: String, syms: String* ): MapSignature = apply( Ident( sym, freshTypeVar() ), syms map ( s => Ident( s, freshTypeVar() ) ): _* )

  /**
   * The signature that the Babel parser will use if no other signature is in scope. In this signature, identifiers denote
   * variables iff they start with [u-zU-Z]. The types of all identifiers are arbitrary.
   */
  implicit val defaultSignature = new Signature {
    val varPattern = "[u-zU-Z].*".r

    override def apply( s: String ): VarConst = {
      if ( varPattern.pattern.matcher( s ).matches() )
        IsVar( freshTypeVar() )
      else
        IsConst( freshTypeVar() )
    }
  }
}

/**
 * A signature based on a map: The identifiers for which the map is defined are constants, the rest are variables.
 * @param map A map from strings to types.
 */
case class MapSignature( map: Map[String, ast.Type] ) extends Signature {
  override def apply( x: String ): VarConst =
    if ( map contains x )
      IsConst( map( x ) )
    else
      IsVar( ast.freshTypeVar() )
}

/**
 * Class with two possible cases, one for variables and one for constants.
 */
sealed trait VarConst {
  def t: ast.Type
  def isVar: Boolean
}

case class IsVar( t: ast.Type ) extends VarConst {
  def isVar = true
}

case class IsConst( t: ast.Type ) extends VarConst {
  def isVar = false
}