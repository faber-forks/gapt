package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkNew.{ LKToExpansionProof, LKProof }

/**
 * Extracts the instances used in a prenex FOL Pi_1 expansion tree / Sigma_1 expansion sequent.
 *
 * Each expansion tree is transformed into a list of instances of its shallow formula.
 *
 * In contrast to [[toDeep]], this function doesn't produce conjunctions of instances, but instead increases the
 * number of formulas in the antecedent/succedent.
 */
object extractInstances {
  def apply( expansionTree: ExpansionTree ): Set[HOLFormula] =
    if ( !containsQuantifier( toShallow( expansionTree ) ) )
      Set( toShallow( expansionTree ) )
    else expansionTree match {
      case ETWeakening( _ ) => Set()
      case ETWeakQuantifier( _, instances ) =>
        instances flatMap { i => extractInstances( i._1 ) } toSet
      case ETStrongQuantifier( _, _, t ) => extractInstances( t )
      case ETSkolemQuantifier( _, _, t ) => extractInstances( t )
      case ETAnd( t, s )                 => for ( ( ti, si ) <- apply( t, s ) ) yield ti & si
      case ETOr( t, s )                  => for ( ( ti, si ) <- apply( t, s ) ) yield ti | si
      case ETImp( t, s )                 => for ( ( ti, si ) <- apply( t, s ) ) yield ti --> si
      case ETNeg( t )                    => for ( ti <- extractInstances( t ) ) yield -ti
    }

  private def apply( a: ExpansionTree, b: ExpansionTree ): Set[( HOLFormula, HOLFormula )] = {
    val ais = extractInstances( a )
    val bis = extractInstances( b )
    if ( ais.isEmpty && bis.isEmpty ) {
      Set()
    } else if ( ais.isEmpty ) {
      val dummy = removeAllQuantifiers( toShallow( a ) )
      for ( bi <- bis ) yield ( dummy, bi )
    } else if ( bis.isEmpty ) {
      val dummy = removeAllQuantifiers( toShallow( b ) )
      for ( ai <- ais ) yield ( ai, dummy )
    } else {
      for ( ai <- ais; bi <- bis ) yield ( ai, bi )
    }
  }

  def apply( expansionSequent: ExpansionSequent ): HOLSequent =
    expansionSequent flatMap apply

}

object groundTerms {
  def apply( term: LambdaExpression ): LambdaExpression =
    Substitution( freeVariables( term ) map { case v @ Var( name, ty ) => v -> Const( name, ty ) } )( term )

  def apply( lang: Set[LambdaExpression] ): Set[LambdaExpression] = lang map apply

  def apply( term: FOLTerm ): FOLTerm = apply( term.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLTerm]
  def apply( lang: Set[FOLTerm] )( implicit dummyImplicit: DummyImplicit ): Set[FOLTerm] = lang map apply
}

/**
 * Encodes instances of an end-sequent as terms.
 *
 * The end-sequent must contain no strong quantifiers and each of its formulas must be in variable normal form.
 *
 * In the case of cut-introduction, the end-sequent has no free variables and we're encoding a Herbrand sequent as a
 * set of terms.  A term r_i(t_1,...,t_n) encodes an instance of the formula "forall x_1 ... x_n, phi(x_1,...,x_n)"
 * using the instances (t_1,...,t_n).
 *
 * In the case of simple inductive proofs, the end-sequent contains one free variable (alpha).  Here, we consider
 * proofs of instance sequents, which are obtained by substituting a numeral for alpha.  Hence the formulas occuring
 * in the end-sequents of instance proofs are substitution instances of [[endSequent]]; the encoded terms still only
 * capture the instances used in the instance proofs--i.e. not alpha.
 */
class InstanceTermEncoding private ( val endSequent: HOLSequent, val instanceTermType: Ty ) {

  require( !containsStrongQuantifier( endSequent ), s"$endSequent contains strong quantifiers" )
  endSequent.elements foreach { formula =>
    require( isInVNF( formula ), s"$formula is not in variable normal form" )
  }

  /**
   * The propositional matrices phi of the end-sequent.
   */
  val matrices = endSequent map { removeAllQuantifiers( _ ) }

  /**
   * The propositional matrices of the end-sequent, where the formulas in the antecedent are negated.
   */
  val signedMatrices = matrices.map( -_, identity )

  // we don't use variables() diff freeVariables() here as we would like the correct order
  private def getQuantVars( esFormula: HOLFormula ): Seq[Var] = esFormula match {
    case All( x, t )                        => x +: getQuantVars( t )
    case Ex( x, t )                         => x +: getQuantVars( t )
    case And( t, s )                        => getQuantVars( t ) ++ getQuantVars( s )
    case Or( t, s )                         => getQuantVars( t ) ++ getQuantVars( s )
    case Imp( t, s )                        => getQuantVars( t ) ++ getQuantVars( s )
    case Neg( t )                           => getQuantVars( t )
    case Top() | Bottom() | HOLAtom( _, _ ) => Seq()
  }
  /**
   * The quantified variables of each formula in the end-sequent.
   */
  val quantVars = endSequent map getQuantVars

  /**
   * Assigns each formula in the end-sequent a fresh function symbol name used to encode its instances.
   */
  protected def mkSym( idx: SequentIndex ) = idx match {
    case Ant( i ) => s"-{${endSequent( idx )}_a$i"
    case Suc( i ) => s"-{${endSequent( idx )}_s$i"
  }

  /**
   * The function symbols used to encode the instances of each formula in the end-sequent.
   */
  val symbols = for ( ( vars, idx ) <- quantVars.zipWithIndex )
    yield Const( mkSym( idx ), FunctionType( instanceTermType, vars map { _.exptype } ) )

  private def instanceTerms( signedInstance: HOLFormula, esFormula: SequentIndex ) =
    syntacticMatching( signedMatrices( esFormula ), signedInstance ) map { subst =>
      esFormula -> quantVars( esFormula ).map( subst.apply )
    }

  private def findInstance( signedInstance: HOLFormula ): Option[( SequentIndex, Seq[LambdaExpression] )] =
    endSequent.indices.flatMap { instanceTerms( signedInstance, _ ) }.headOption

  def encodeOption( signedInstance: HOLFormula ): Option[LambdaExpression] =
    findInstance( signedInstance ) map {
      case ( esFormula, terms ) => symbols( esFormula )( terms: _* )
    }

  def encode( signedInstance: HOLFormula ): LambdaExpression = encodeOption( signedInstance ).getOrElse {
    throw new IllegalArgumentException( s"Cannot find $signedInstance in $endSequent" )
  }

  /**
   * Encodes a sequent consisting of instances of an instance sequent.
   */
  def encode( instance: HOLSequent ): Set[LambdaExpression] =
    instance.map( -_, identity ).elements map encode toSet

  /**
   * Encodes an expansion sequent (of an instance proof).
   *
   * The shallow formulas of the expansion sequents should be subsumed by formulas in the end-sequent.
   */
  def encode( instance: ExpansionSequent )( implicit dummyImplicit: DummyImplicit ): Set[LambdaExpression] =
    encode( extractInstances( instance ) )

  /**
   * Maps a function symbol to the index of its corresponding formula in the end-sequent.
   */
  def findESIndex( sym: Const ): Option[SequentIndex] = symbols indexOfOption sym

  /**
   * Maps a function symbol to its corresponding formula in the end-sequent.
   */
  def findESFormula( sym: Const ): Option[HOLFormula] = findESIndex( sym ) map { endSequent( _ ) }

  def decodeOption( term: LambdaExpression ): Option[( SequentIndex, Substitution )] = term match {
    case Apps( f: Const, args ) =>
      findESIndex( f ) map { idx => idx -> Substitution( quantVars( idx ) zip args ) }
    case _ => None
  }

  /**
   * Decodes a term into its corresponding instance.
   *
   * The resulting instance can contain alpha in the inductive case.
   */
  def decodeToPolarizedFormula( term: LambdaExpression ): ( HOLFormula, Boolean ) =
    decodeOption( term ) map { case ( idx, subst ) => subst( matrices( idx ) ) -> idx.isSuc } get

  def decodeToInstanceSequent( terms: Iterable[LambdaExpression] ): HOLSequent =
    Sequent( terms map decodeToPolarizedFormula toSeq )

  def decodeToExpansionSequent( terms: Iterable[LambdaExpression] ): ExpansionSequent =
    Sequent( terms flatMap decodeOption groupBy { _._1 } map {
      case ( idx, instances ) =>
        formulaToExpansionTree( endSequent( idx ), instances map { _._2 } toList, idx.isSuc ) -> idx.isSuc
    } toSeq )
}

object InstanceTermEncoding {
  def apply( endSequent: HOLSequent, instanceTermType: Ty = TBase( "InstanceTermType" ) ): InstanceTermEncoding =
    new InstanceTermEncoding( endSequent map { toVNF( _ ) }, instanceTermType )

  def apply( expansionSequent: ExpansionSequent ): ( Set[LambdaExpression], InstanceTermEncoding ) = {
    val encoding = InstanceTermEncoding( toShallow( expansionSequent ) )
    encoding.encode( expansionSequent ) -> encoding
  }

  def apply( lkProof: LKProof ): ( Set[LambdaExpression], InstanceTermEncoding ) = {
    val encoding = InstanceTermEncoding( lkProof.endSequent )
    encoding.encode( LKToExpansionProof( lkProof ) ) -> encoding
  }
}

object FOLInstanceTermEncoding {
  def apply( endSequent: HOLSequent ): InstanceTermEncoding =
    InstanceTermEncoding( endSequent, Ti )

  def apply( expansionSequent: ExpansionSequent ): ( Set[FOLTerm], InstanceTermEncoding ) = {
    val encoding = FOLInstanceTermEncoding( toShallow( expansionSequent ) )
    encoding.encode( expansionSequent ).map( _.asInstanceOf[FOLTerm] ) -> encoding
  }

  def apply( lkProof: LKProof ): ( Set[FOLTerm], InstanceTermEncoding ) = {
    val encoding = FOLInstanceTermEncoding( lkProof.endSequent )
    encoding.encode( LKToExpansionProof( lkProof ) ).map( _.asInstanceOf[FOLTerm] ) -> encoding
  }
}
