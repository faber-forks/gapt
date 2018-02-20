package at.logic.gapt.testing
import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.expr._
import at.logic.gapt.examples._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.ceres.CERES
import at.logic.gapt.proofs.expansion.{ ExpansionProof, eliminateCutsET }
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof, ReductiveCutElimination, eliminateDefinitions }
import at.logic.gapt.proofs.lkt.{ LKToLKt, LKt, normalizeLKt }
import at.logic.gapt.proofs.resolution.ResolutionToLKProof
import at.logic.gapt.provers.escargot.Escargot

import scala.concurrent.duration._

object cutReductionBenchmark extends Script {
  def measure( f: => Unit ): Duration = {
    val begin = System.nanoTime()
    f
    val end = System.nanoTime()
    ( end - begin ).nanos
  }

  def robustlyMeasure( f: => Unit ): Duration = {
    val time0 = measure( f )
    val extraRuns =
      math.max( 0, math.min(
        math.max( 2, math.round( 1.second / time0 ) ),
        math.floor( 10.seconds / time0 ).toLong ) )
    val time1 = measure( ( 0L until extraRuns ).foreach( _ => f ) )
    ( time0 + time1 ) / ( 1 + extraRuns )
  }

  trait Method {
    type P
    def convert( p: LKProof ): P
    def eliminate( p: P ): Unit
    def robustlyMeasureElimination( lk: LKProof ): Duration = {
      val p = convert( lk )
      robustlyMeasure( eliminate( p ) )
    }
  }
  trait LKMethod extends Method {
    type P = LKProof
    def convert( p: LKProof ): P = p
  }
  case object LKReductive extends LKMethod { def eliminate( p: LKProof ): Unit = ReductiveCutElimination( p ) }
  case object LKCERES extends LKMethod { def eliminate( p: LKProof ): Unit = CERES( p ) }
  case object CERESEXP extends LKMethod { def eliminate( p: LKProof ): Unit = CERES.CERESExpansionProof( p ) }
  case object BogoElim extends Method {
    type P = HOLSequent
    def convert( p: LKProof ): P = p.endSequent
    def eliminate( p: P ): Unit = Escargot.getExpansionProof( p ).get
  }
  case object ExpCutElim extends Method {
    type P = ExpansionProof
    def convert( p: LKProof ): P = LKToExpansionProof( p )
    def eliminate( p: P ): Unit = eliminateCutsET( p )
  }
  class AbstractLKtNorm( skipAtomicCuts: Boolean = false, skipPropositionalCuts: Boolean = false ) extends Method {
    type P = LKt
    def convert( p: LKProof ): P = LKToLKt( p )._1
    def eliminate( p: LKt ): Unit = normalizeLKt( p, skipAtomicCuts, skipPropositionalCuts )
  }
  case object LKtNorm extends AbstractLKtNorm
  case object LKtNormA extends AbstractLKtNorm( skipAtomicCuts = true )
  case object LKtNormP extends AbstractLKtNorm( skipPropositionalCuts = true )
  val methods = List( LKReductive, LKCERES, CERESEXP, BogoElim, ExpCutElim, LKtNorm, LKtNormA, LKtNormP )

  def turnEqualityIntoPredicate[A: ClosedUnderReplacement]( a: A ): A =
    TermReplacement( a, { case EqC( t ) => Const( "E", t ->: t ->: To ) } )

  // warmup
  for ( m <- methods ) m.robustlyMeasureElimination( LinearCutExampleProof( 3 ) )

  println( "proof,n," + methods.mkString( "," ) )

  def bench( name: String, n: Int, lk: LKProof, exclude: Set[Method] = Set() ): Unit = {
    val times = methods.map {
      case m if exclude( m ) => "NaN"
      case m                 => m.robustlyMeasureElimination( lk ).toUnit( SECONDS ).toString
    }
    println( s"$name,$n," + times.mkString( "," ) )
  }

  bench( "pi2pigeon", -1, Pi2Pigeonhole.proof )
  bench( "pi3pigeon", -1, Pi3Pigeonhole.proof )

  {
    import at.logic.gapt.examples.lattice._
    bench( "lattice", -1, eliminateDefinitions( p ), exclude = Set( LKReductive, BogoElim ) )
  }

  for ( n <- 0 to 18; p <- CutIntroduction( LinearEqExampleProof( n ) ) )
    bench( "ci_lineareq", n, turnEqualityIntoPredicate( p ) )
  for ( n <- 0 to 18; p <- CutIntroduction( LinearExampleProof( n ) ) ) bench( "ci_linear", n, p )
  for ( n <- 0 to 18; p <- CutIntroduction( SquareDiagonalExampleProof( n ) ) ) bench( "ci_sqdiag", n, p )
  for ( n <- 0 to 5; p <- CutIntroduction( FactorialFunctionEqualityExampleProof( n ) ) )
    bench( "ci_fact", n, turnEqualityIntoPredicate( p ), exclude = Set( BogoElim ) )

  for ( n <- 0 to 10 ) {
    val Some( res ) = Escargot.getResolutionProof( fof"P(0) & !x (P(x) -> P(s(x))) -> P${Numeral( n )}" )
    val lk = ResolutionToLKProof( res )
    bench( "linearacnf", n, lk )
  }

  for ( n <- 0 to 8 ) bench( "linear", n, LinearCutExampleProof( n ) )

}
