package at.logic.gapt.grammars.deltatable

import at.logic.gapt.cutintro.{ GrammarFindingMethod, DeltaTableMethod }
import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ antiUnifier, antiUnifier1, VectTratGrammar }
import at.logic.gapt.utils.time

import scala.collection.mutable

object deltaTable {
  type Row = Set[( LambdaExpression, Set[LambdaExpression] )]

  def createTable( termSet: Set[LambdaExpression], maxArity: Option[Int] = None, singleVariable: Boolean = false ): Map[Set[Substitution], Row] = {
    // invariant:  deltatable(S) contains (u,T)  ==>  u S = T  &&  |S| = |T|
    val deltatable = mutable.Map[Set[Substitution], List[( LambdaExpression, Set[LambdaExpression] )]]().withDefaultValue( Nil )

    def populate(
      remainingTerms: List[LambdaExpression],
      currentAU:      LambdaExpression,
      currentCover:   Set[LambdaExpression],
      currentSubst:   Set[Substitution]
    ): Unit = if ( remainingTerms.nonEmpty ) {
      val ( newTerm :: rest ) = remainingTerms

      val ( newAU, substCurAU, substNewTerm ) =
        if ( currentAU == null ) ( newTerm, Map[Var, LambdaExpression](), Map[Var, LambdaExpression]() )
        else if ( singleVariable ) antiUnifier1( currentAU, newTerm )
        else antiUnifier( currentAU, newTerm )

      if ( !newAU.isInstanceOf[Var] && maxArity.forall { substCurAU.size <= _ } ) {
        val newSubst = currentSubst.map { subst => Substitution( substCurAU mapValues { subst( _ ) } ) } + Substitution( substNewTerm )
        val newCover = currentCover + newTerm
        deltatable( newSubst ) ::= ( newAU -> newCover )
        populate( rest, newAU, newCover, newSubst )
      }

      populate( rest, currentAU, currentCover, currentSubst )
    }

    populate( termSet.toList, null, Set(), Set() )

    deltatable.mapValues { _.toSet }.toMap
  }

  def keySubsumption( a: Set[Substitution], b: Set[Substitution] ): Set[Map[Var, Var]] =
    keySubsumption( a map { _.map }, b map { _.map }, Map() )

  def keySubsumption[K1, K2, V]( a: Set[Map[K1, V]], b: Set[Map[K2, V]], alreadyFixed: Map[K1, K2] ): Set[Map[K1, K2]] = {
    if ( a.size > b.size ) return Set()
    if ( a.head.size > b.head.size ) return Set()

    val nextKs = a.head.keySet diff alreadyFixed.keySet
    if ( nextKs isEmpty ) return Set( alreadyFixed )

    val chosenK = nextKs.head
    val chosenV = a.head( chosenK )

    for {
      ( corrK, `chosenV` ) <- b.flatten
      newAlreadyFixed = alreadyFixed + ( chosenK -> corrK )
      if a.map { _ filterKeys newAlreadyFixed.keySet } subsetOf b.map { newAlreadyFixed mapValues _ }
      solution <- keySubsumption( a, b, newAlreadyFixed )
    } yield solution
  }

  def tableSubsumption( table: Map[Set[Substitution], Row] ): Map[Set[Substitution], Row] =
    for ( ( s1, row1 ) <- table ) yield if ( s1.head.map.size <= 1 ) s1 -> row1 else {
      var newRow = row1.to[mutable.Set]
      for {
        ( s2, row2 ) <- table
        if s2.head.map.nonEmpty // do not add ground terms
        subs <- keySubsumption( s2, s1 )
        subst = Substitution( subs )
        ( u2, t2 ) <- row2
      } newRow += subst( u2 ) -> t2
      newRow = newRow.groupBy { _._1 }.mapValues { _ flatMap { _._2 } toSet }.to[mutable.Set]
      for {
        e1 @ ( u1, t1 ) <- newRow
        e2 @ ( u2, t2 ) <- newRow
        if newRow contains e1
        if e1 != e2
        if t2 subsetOf t1
      } newRow -= e2
      s1 -> newRow.toSet
    }

  def findGrammarFromDeltaTable( termSet: Set[LambdaExpression], deltatable: Map[Set[Substitution], Row] ): ( Set[LambdaExpression], Set[Substitution] ) = {
    var minSize = termSet.size
    val minGrammars = mutable.Buffer[( Set[LambdaExpression], Set[Substitution] )]()

    def minimizeGrammar(
      termSet:         Set[LambdaExpression],
      grammar:         Row,
      alreadyIncluded: Set[LambdaExpression],
      s:               Set[Substitution]
    ): Unit =
      if ( termSet isEmpty ) {
        val grammarSize = alreadyIncluded.size + s.size
        if ( grammarSize < minSize ) {
          minSize = grammarSize
          minGrammars += ( alreadyIncluded -> s )
        }
      } else if ( alreadyIncluded.size + s.size >= minSize ) {
        // Ignore this branch.
      } else if ( grammar isEmpty ) {
        throw new IllegalArgumentException
      } else {
        val focus = grammar maxBy { _._2.size }

        minimizeGrammar(
          termSet diff focus._2,
          grammar map { x => x._1 -> x._2.diff( focus._2 ) } filter { _._2.nonEmpty },
          alreadyIncluded + focus._1, s
        )

        val restLang = grammar - focus flatMap { _._2 }
        if ( termSet subsetOf restLang ) {
          minimizeGrammar( termSet, grammar - focus, alreadyIncluded, s )
        }
      }

    for ( ( s, decomps ) <- deltatable ) {
      val coveredTerms = decomps flatMap { _._2 }
      minimizeGrammar( coveredTerms, decomps, termSet diff coveredTerms, s )
    }

    for {
      g1 @ ( u1, s1 ) <- minGrammars
      g2 @ ( u2, s2 ) <- minGrammars
      if g1 != g2
      subst <- keySubsumption( s1, s2 )
      u = u2 ++ u1.map { Substitution( subst )( _ ) }
      s = s2
      row = for ( t <- u ) yield t -> s.map { _( t ) }.intersect( termSet )
    } minimizeGrammar( termSet, row, Set(), s )

    minGrammars minBy { g => g._1.size + g._2.size }
  }

  def grammarToVTRATG( us: Set[LambdaExpression], s: Set[Substitution] ): VectTratGrammar = {
    val alpha = freeVariables( us ).toList.sortBy { _.toString }.asInstanceOf[List[FOLVar]]
    val tau = rename( FOLVar( "tau" ), alpha )
    VectTratGrammar( tau, Seq( List( tau ), alpha ),
      ( for ( subst <- s ) yield alpha -> alpha.map { subst( _ ).asInstanceOf[FOLTerm] } )
        union ( for ( u <- us ) yield List( tau ) -> List( u.asInstanceOf[FOLTerm] ) ) )
  }

  def main( args: Array[String] ) = {
    //    val n = 9
    //    val terms = for (i <- 0 to n) yield FOLFunction("f", Numeral(i))

    //    val terms = FOLInstanceTermEncoding( SquareEdges2DimExampleProof( 10 ) )._1

    def iter( suc: String, zero: String )( i: Int ): FOLTerm =
      if ( i == 0 ) FOLConst( zero ) else FOLFunction( suc, iter( suc, zero )( i - 1 ) )
    val n = 12
    val terms1 = 0 until n map iter( "f", "c" ) map { FOLFunction( "r", _ ) }
    val terms2 = 0 until n map iter( "g", "d" ) map { FOLFunction( "s", _ ) }
    val terms = terms1 ++ terms2

    val deltatable = createTable( terms.toSet )

    //    val actualMinGrammar = findMinimalVectGrammar( terms.toSet, Seq( 1 ) )
    //
    //    val origDTableGrammar = DeltaTableMethod( false ).findGrammars( terms.toSet ).get

    val ( us, s ) = findGrammarFromDeltaTable( terms.toSet, deltatable )
    val vtratg = grammarToVTRATG( us, s )
    //    println( deltatable )
    println( vtratg )

    time { for ( i <- 1 to 5 ) DeltaTableMethodNew( singleQuantifier = true, tableSubsumption = false, None ).findGrammars( terms.toSet ).get }
    time { for ( i <- 1 to 5 ) DeltaTableMethod( false ).findGrammars( terms.toSet ).get }
    Thread sleep 4000
    ()
  }
}

case class DeltaTableMethodNew(
    singleQuantifier: Boolean,
    tableSubsumption: Boolean,
    keyLimit:         Option[Int]
) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val langSet = lang.toSet[LambdaExpression]

    var dtable = deltaTable.createTable( langSet, keyLimit, singleQuantifier )

    if ( tableSubsumption ) dtable = deltaTable.tableSubsumption( dtable )

    val ( us, s ) = deltaTable.findGrammarFromDeltaTable( langSet, dtable )

    Some( deltaTable.grammarToVTRATG( us, s ) )
  }

  def name = toString
}