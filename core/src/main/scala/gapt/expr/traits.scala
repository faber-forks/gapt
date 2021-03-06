package gapt.expr

import gapt.expr.fol.FOLPosition._
import gapt.expr.fol.FOLPosition
import gapt.expr.hol.HOLPosition

trait Formula extends Expr {
  override def replace( pos: HOLPosition, exp: Expr ) = HOLPosition.replace( this, pos, exp )
}
trait Atom extends Formula with HOLPartialAtom {
  private[expr] override def numberOfArguments: Int = 0
}

trait VarOrConst extends Expr {
  def name: String
}

trait LogicalConstant extends Const

trait FOLExpression extends Expr {
  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: FOLPosition ): FOLExpression = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: FOLPosition ): Option[FOLExpression] =
    FOLPosition.toHOLPositionOption( this )( pos ).flatMap( get ).asInstanceOf[Option[FOLExpression]]

  def replace( pos: FOLPosition, replacement: FOLExpression ): FOLExpression =
    FOLPosition.replace( this, pos, replacement )

  /**
   * Tests whether this expression has a subexpression at a given position.
   *
   * @param pos The position to be tested.
   * @return Whether this(pos) is defined.
   */
  def isDefinedAt( pos: FOLPosition ): Boolean = get( pos ).isDefined

  /**
   * Finds all HOL positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find( exp: FOLExpression ): List[FOLPosition] = getPositions( this, _ == exp )

}

trait FOLPartialAtom extends HOLPartialAtom
trait FOLAtomConst extends HOLAtomConst with FOLPartialAtom {
  def apply( that: FOLTerm* )( implicit dummyImplicit: DummyImplicit ) = App( this, that ).asInstanceOf[FOLAtom]
}

private[expr] trait FOLPartialFormula extends Expr {
  private[expr] def numberOfArguments: Int
}

trait FOLPartialTerm extends Expr {
  private[expr] def numberOfArguments: Int
}
trait FOLFunctionConst extends Const with FOLPartialTerm {
  def apply( that: FOLTerm* )( implicit dummyImplicit: DummyImplicit ) = App( this, that ).asInstanceOf[FOLTerm]
}

trait HOLPartialAtom extends Expr {
  private[expr] def numberOfArguments: Int

  def apply( that: Expr* )( implicit dummyImplicit: DummyImplicit ) = App( this, that ).asInstanceOf[Atom]
}
trait HOLAtomConst extends Const with HOLPartialAtom

trait FOLTerm extends FOLPartialTerm with FOLExpression {
  private[expr] override val numberOfArguments = 0
}
trait FOLVar extends Var with FOLTerm
trait FOLConst extends Const with FOLTerm with FOLFunctionConst
trait FOLFormula extends FOLPartialFormula with Formula with FOLExpression {
  private[expr] override val numberOfArguments = 0

  def &( that: FOLFormula ): FOLFormula = And( this, that )
  def |( that: FOLFormula ): FOLFormula = Or( this, that )
  override def unary_- : FOLFormula = Neg( this )
  def -->( that: FOLFormula ): FOLFormula = Imp( this, that )
  def <->( that: FOLFormula ) = Iff( this, that ).asInstanceOf[FOLFormula]
}
trait FOLAtom extends FOLPartialAtom with Atom with FOLFormula {
  private[expr] override val numberOfArguments: Int = 0
}

private[expr] trait FOLFormulaWithBoundVar extends Expr
trait FOLQuantifier extends LogicalConstant

private[expr] trait PropPartialFormula extends FOLPartialFormula
trait PropFormula extends PropPartialFormula with FOLFormula
trait PropConnective extends LogicalConstant with PropPartialFormula
trait PropAtom extends Const with PropFormula with FOLAtom with FOLAtomConst

/**
 * Determine the correct traits for a given lambda expression.
 *
 * We assign to each lambda expression a set of traits it is supposed to have.  These traits are generated by a
 * (non-deterministic) tree automaton with rules such as App(NegC(), FOLFormula) -> FOLFormula.
 *
 * This object contains private classes for each of the resulting determinized states.  We could use anonymous types as
 * well, i.e. Var with FOLVar instead of Var_with_FOLVar, but these would show up in the debugger as
 * determineTraits$$anon$27, which is not particularly readable.
 */
private[expr] object determineTraits {
  private class Var_with_FOLVar( s: String, t: Ty ) extends Var( s, t ) with FOLVar
  private class Var_with_Formula( s: String, t: Ty ) extends Var( s, t ) with Formula
  private class Var_with_Atom( s: String, t: Ty ) extends Var( s, t ) with Atom
  private class Var_with_HOLPartialAtom( s: String, t: Ty, override val numberOfArguments: Int ) extends Var( s, t ) with HOLPartialAtom

  def forVar( sym: String, exptype: Ty ): Var = exptype match {
    case Ti                     => new Var_with_FOLVar( sym, exptype )
    case To                     => new Var_with_Atom( sym, exptype )
    case FunctionType( To, ts ) => new Var_with_HOLPartialAtom( sym, exptype, ts.length )
    case _                      => new Var( sym, exptype )
  }

  private class Const_with_FOLQuantifier( s: String, t: Ty, ps: List[Ty] ) extends Const( s, t, ps ) with FOLQuantifier
  private class Const_with_LogicalConstant( s: String, t: Ty, ps: List[Ty] ) extends Const( s, t, ps ) with LogicalConstant
  private class Const_with_PropConnective_with_PropFormula( s: String, t: Ty, ps: List[Ty] ) extends Const( s, t, ps ) with PropConnective with PropFormula
  private class Const_with_FOLConst( s: String, t: Ty, ps: List[Ty] ) extends Const( s, t, ps ) with FOLConst
  private class Const_with_PropAtom( s: String, t: Ty, ps: List[Ty] ) extends Const( s, t, ps ) with PropAtom
  private class Const_with_PropConnective( s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int ) extends Const( s, t, ps ) with PropConnective
  private class Const_with_PropPartialFormula( s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int ) extends Const( s, t, ps ) with PropPartialFormula
  private class Const_with_FOLFunctionConst( s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int ) extends Const( s, t, ps ) with FOLFunctionConst
  private class Const_with_FOLAtomConst( s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int ) extends Const( s, t, ps ) with FOLAtomConst
  private class Const_with_HOLAtomConst( s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int ) extends Const( s, t, ps ) with HOLAtomConst
  def forConst( sym: String, exptype: Ty, ps: List[Ty] ): Const = ( sym, exptype, ps ) match {
    case ForallC( Ti ) | ExistsC( Ti )    => new Const_with_FOLQuantifier( sym, exptype, ps )
    case ForallC( _ ) | ExistsC( _ )      => new Const_with_LogicalConstant( sym, exptype, ps )
    case AndC() | OrC() | ImpC()          => new Const_with_PropConnective( sym, exptype, ps, 2 )
    case NegC()                           => new Const_with_PropConnective( sym, exptype, ps, 1 )
    case TopC() | BottomC()               => new Const_with_PropConnective_with_PropFormula( sym, exptype, ps )
    case ( _, Ti, _ )                     => new Const_with_FOLConst( sym, exptype, ps )
    case ( _, To, _ )                     => new Const_with_PropAtom( sym, exptype, ps )
    case ( _, FOLHeadType( To, n ), _ )   => new Const_with_FOLAtomConst( sym, exptype, ps, n )
    case ( _, FOLHeadType( Ti, n ), _ )   => new Const_with_FOLFunctionConst( sym, exptype, ps, n )
    case ( _, FunctionType( To, ts ), _ ) => new Const_with_HOLAtomConst( sym, exptype, ps, ts.length )
    case _                                => new Const( sym, exptype, ps )
  }

  private class App_with_PropFormula( f: Expr, a: Expr ) extends App( f, a ) with PropFormula
  private class App_with_FOLTerm( f: Expr, a: Expr ) extends App( f, a ) with FOLTerm
  private class App_with_FOLAtom( f: Expr, a: Expr ) extends App( f, a ) with FOLAtom
  private class App_with_FOLFormula( f: Expr, a: Expr ) extends App( f, a ) with FOLFormula
  private class App_with_Atom( f: Expr, a: Expr ) extends App( f, a ) with Atom
  private class App_with_Formula( f: Expr, a: Expr ) extends App( f, a ) with Formula
  private class App_with_FOLPartialTerm( f: Expr, a: Expr, override val numberOfArguments: Int ) extends App( f, a ) with FOLPartialTerm
  private class App_with_FOLPartialAtom( f: Expr, a: Expr, override val numberOfArguments: Int ) extends App( f, a ) with FOLPartialAtom
  private class App_with_FOLPartialFormula( f: Expr, a: Expr, override val numberOfArguments: Int ) extends App( f, a ) with FOLPartialFormula
  private class App_with_PropPartialFormula( f: Expr, a: Expr, override val numberOfArguments: Int ) extends App( f, a ) with PropPartialFormula
  private class App_with_HOLPartialAtom( f: Expr, a: Expr, override val numberOfArguments: Int ) extends App( f, a ) with HOLPartialAtom
  def forApp( f: Expr, a: Expr ): App = ( f, a ) match {
    case ( f: PropPartialFormula, a: PropFormula ) => f.numberOfArguments match {
      case 1 => new App_with_PropFormula( f, a )
      case n => new App_with_PropPartialFormula( f, a, n - 1 )
    }

    case ( f: FOLPartialTerm, a: FOLTerm ) => f.numberOfArguments match {
      case 1 => new App_with_FOLTerm( f, a )
      case n => new App_with_FOLPartialTerm( f, a, n - 1 )
    }

    case ( f: FOLPartialAtom, a: FOLTerm ) => f.numberOfArguments match {
      case 1 => new App_with_FOLAtom( f, a )
      case n => new App_with_FOLPartialAtom( f, a, n - 1 )
    }

    case ( f: FOLPartialFormula, a: FOLFormula ) => f.numberOfArguments match {
      case 1 => new App_with_FOLFormula( f, a )
      case n => new App_with_FOLPartialFormula( f, a, n - 1 )
    }

    case ( f: FOLQuantifier, _ ) => a match {
      case a: FOLFormulaWithBoundVar => new App_with_FOLFormula( f, a )
      case _                         => new App_with_Formula( f, a )
    }

    case ( f: HOLPartialAtom, _ ) => f.numberOfArguments match {
      case 1 => new App_with_Atom( f, a )
      case n => new App_with_HOLPartialAtom( f, a, n - 1 )
    }

    case _ => f.ty match {
      case _ ->: To => new App_with_Formula( f, a )
      case _        => new App( f, a )
    }
  }

  private class Abs_with_FOLFormulaWithBoundVar( v: Var, t: Expr ) extends Abs( v, t ) with FOLFormulaWithBoundVar
  def forAbs( v: Var, t: Expr ): Abs = ( v.ty, t ) match {
    case ( Ti, t: FOLFormula ) => new Abs_with_FOLFormulaWithBoundVar( v, t )
    case _                     => new Abs( v, t )
  }
}

object FOLVar {
  def apply( sym: String ): FOLVar = Var( sym, Ti ).asInstanceOf[FOLVar]
  def unapply( e: FOLVar ) = Some( e.name )
}

object FOLConst {
  def apply( sym: String ): FOLConst = FOLFunction( sym ).asInstanceOf[FOLConst]
  def unapply( e: FOLConst ) = Some( e.name )
}

private[expr] class FOLHead( ret: Ty ) {
  def apply( sym: String, arity: Int ): Const =
    Const( sym, FOLHeadType( ret, arity ) )
  def unapply( e: Expr ): Option[( String, Int )] = e match {
    case NonLogicalConstant( sym, FOLHeadType( `ret`, arity ), Nil ) => Some( ( sym, arity ) )
    case _ => None
  }
}

object FOLAtomConst extends FOLHead( To ) {
  override def apply( sym: String, arity: Int ): FOLAtomConst =
    if ( sym == "=" && arity == 2 ) EqC( Ti ).asInstanceOf[FOLAtomConst] else
      super.apply( sym, arity ).asInstanceOf[FOLAtomConst]
  override def unapply( e: Expr ): Option[( String, Int )] = e match {
    case EqC( Ti ) => Some( "=", 2 )
    case _         => super.unapply( e )
  }
}
object FOLFunctionConst extends FOLHead( Ti ) {
  override def apply( sym: String, arity: Int ): FOLFunctionConst =
    super.apply( sym, arity ).asInstanceOf[FOLFunctionConst]
}

object FOLAtom {
  def apply( sym: String, args: FOLTerm* )( implicit dummyImplicit: DummyImplicit ): FOLAtom = FOLAtom( sym, args )
  def apply( sym: String, args: Seq[FOLTerm] ): FOLAtom =
    Apps( FOLAtomConst( sym, args.size ), args ).asInstanceOf[FOLAtom]

  def unapply( e: FOLAtom ): Option[( String, List[FOLTerm] )] = e match {
    case Apps( FOLAtomConst( sym, _ ), args ) if e.isInstanceOf[FOLAtom] =>
      Some( ( sym, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

object PropAtom {
  def apply( sym: String ): PropAtom = Const( sym, To ).asInstanceOf[PropAtom]
}

object HOLAtomConst {
  def apply( name: String, argTypes: Ty* ): HOLAtomConst =
    Const( name, FunctionType( To, argTypes ) ).asInstanceOf[HOLAtomConst]

  def unapply( e: Const with HOLPartialAtom ): Option[( String, Seq[Ty] )] = e match {
    case Const( name, FunctionType( To, argTypes ), _ ) => Some( name -> argTypes )
  }
}

object Atom {
  def apply( head: String, args: Expr* )( implicit dummyImplicit: DummyImplicit ): Atom =
    apply( head, args )
  def apply( head: String, args: Seq[Expr] ): Atom =
    Apps( Const( head, FunctionType( To, args.map( _.ty ) ) ), args ).asInstanceOf[Atom]

  def apply( head: Expr, args: Expr* ): Atom =
    apply( head, args toList )
  def apply( head: Expr, args: List[Expr] ): Atom =
    Apps( head, args ).asInstanceOf[Atom]

  def unapply( e: Atom ): Option[( Expr, List[Expr] )] = e match {
    case Apps( head @ ( NonLogicalConstant( _, _, _ ) | Var( _, _ ) ), args ) if e.ty == To => Some( head, args )
    case _ => None
  }
}

/**
 * Matches constants and variables, but nothing else.
 */
object VarOrConst {
  def unapply( e: VarOrConst ): Some[( String, Ty, List[Ty] )] =
    e match {
      case Const( n, t, p ) => Some( n, t, p )
      case Var( n, t )      => Some( n, t, Nil )
    }
}

