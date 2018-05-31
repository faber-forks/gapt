package gapt.proofs.lk

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Substitution
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex

sealed trait Orientation
case object Ltor extends Orientation
case object Rtol extends Orientation

case class RewriteSequence( steps: Seq[Rewrite] ) {

  def lift( context: Abs ): RewriteSequence =
    this.copy( steps = steps.map { _.lift( context ) } )

  def ++( rewriteSequence: RewriteSequence ): RewriteSequence =
    RewriteSequence( steps ++ rewriteSequence.steps )

  def reverse: RewriteSequence =
    RewriteSequence( steps map { _.reverse } reverse )
}

case class Rewrite(
                    context:     Abs,
                    equation:    Formula,
                    orientation: Orientation ) {

  def lift( context: Abs ): Rewrite =
    this.copy( context = liftContext( context, this.context ) )

  def last: Expr = {
    val Apps( _, Seq( s, t ) ) = equation
    orientation match {
      case Ltor =>
        BetaReduction.betaNormalize( App( context, t ) )
      case Rtol =>
        BetaReduction.betaNormalize( App( context, s ) )
    }
  }

  def reverse: Rewrite = {
    val newOrientation = orientation match {
      case Ltor => Rtol
      case Rtol => Ltor
    }
    this.copy( orientation = newOrientation )
  }
}

object splitEquationRewriteSequence {

  def apply(
             rewriteSequence: RewriteSequence ): ( RewriteSequence, RewriteSequence ) = {
    val ( stepsL, stepsR ) = rewriteSequence.steps.map {
      splitEquality
    }.unzip
    ( RewriteSequence( stepsL ), RewriteSequence( stepsR ) )
  }

  def splitEquality( step: Rewrite ): ( Rewrite, Rewrite ) = {
    val Rewrite( context, equation, direction ) = step
    val Abs(
    contextVar,
    Apps( _, Seq( leftContext, rightContext ) ) ) = context
    (
      Rewrite( Abs( contextVar, leftContext ), equation, direction ),
      Rewrite( Abs( contextVar, rightContext ), equation, direction ) )
  }
}

object splitContext {
  def apply( context: Abs ): ( Abs, Abs ) = {
    val Abs( x, Apps( _, Seq( s, t ) ) ) = context
    ( Abs( x, s ), Abs( x, t ) )
  }
}

object liftContext {
  def apply( outerContext: Abs, innerContext: Abs ): Abs = {
    val Abs( innerVar, innerExpr ) = innerContext
    val Abs( outerVar, outerExpr ) = outerContext
    Abs( innerVar, Substitution( outerVar, innerExpr )( outerExpr ) )
  }
}

case class History( initial: Formula, steps: RewriteSequence )

object initialHistory {
  def apply( sequent: Sequent[Formula] ): Sequent[History] =
    sequent.map { History( _, RewriteSequence( Seq() ) ) }
}

class EliminateEqualityLeft( proof: LKProof ) {

  private val endSequent: Sequent[Formula] = proof.conclusion

  def apply(): LKProof = {
    apply( proof, initialHistory( proof.conclusion ) )
  }

  private def apply( proof: LKProof, histories: Sequent[History] ): LKProof = {
    proof match {
      case eql @ EqualityLeftRule( subProof, _, _, replacementContext ) =>
        val principalIndex = eql.mainIndices.head
        val equationIndex = eql.eqInConclusion
        val auxiliaryIndex = eql.aux

        val equationHistory = histories( equationIndex )
        val principalHistory = histories( principalIndex )

        val ( s0Tos, t0Tot ) = splitEquationRewriteSequence( equationHistory.steps )

        val newAuxHistory =
          getOrientation( eql ) match {
            case Ltor =>
              val sTos0 = s0Tos.reverse
              val AsToAs0 = sTos0.lift( replacementContext )
              val At0ToAt = t0Tot.lift( replacementContext )
              History(
                principalHistory.initial,
                principalHistory.steps ++
                  AsToAs0 ++
                  RewriteSequence(
                    Seq(
                      Rewrite(
                        replacementContext,
                        equationHistory.initial,
                        Ltor ) ) ) ++
                  At0ToAt )
            case Rtol =>
              val tTot0 = t0Tot.reverse
              val AtToAt0 = tTot0.lift( replacementContext )
              val As0ToAs = s0Tos.lift( replacementContext )
              History(
                principalHistory.initial,
                principalHistory.steps ++
                  AtToAt0 ++
                  RewriteSequence(
                    Seq(
                      Rewrite(
                        replacementContext,
                        equationHistory.initial,
                        Rtol ) ) ) ++
                  As0ToAs )
          }
        val newHistories = histories.zipWithIndex.map {
          case ( history, index ) =>
            if ( index == auxiliaryIndex )
              newAuxHistory
            else
              histories( eql.getSequentConnector.child( index ) )
        }
        apply( subProof, newHistories )

      case eqr @ EqualityRightRule( _, _, _, _ ) =>
        val equationIndex = eqr.eqInConclusion
        val equationHistory = histories( equationIndex )
        val ( s0Tos, t0Tot ) = splitEquationRewriteSequence( equationHistory.steps )
        getOrientation( eqr ) match {
          case Ltor =>
            val sTos0 = s0Tos.reverse
            val AsToAs0 = sTos0.lift( eqr.replacementContext )
            val At0ToAt = t0Tot.lift( eqr.replacementContext )
            val rewriteSequence = AsToAs0 ++
              RewriteSequence(
                Seq(
                  Rewrite(
                    eqr.replacementContext,
                    equationHistory.initial,
                    Ltor ) ) ) ++ At0ToAt
            rewrite( apply( eqr.subProof, histories ), rewriteSequence.reverse )
          case Rtol =>
            val tTot0 = t0Tot.reverse
            val AtToAt0 = tTot0.lift( eqr.replacementContext )
            val As0ToAs = s0Tos.lift( eqr.replacementContext )
            val rewriteSequence = AtToAt0 ++
              RewriteSequence(
                Seq(
                  Rewrite(
                    eqr.replacementContext,
                    equationHistory.initial,
                    Rtol ) ) ) ++ As0ToAs
            rewrite( apply( eqr.subProof, histories ), rewriteSequence.reverse )
        }
      case _ => retrieveAxiom( proof ) match {
        case LogicalAxiom( formula ) =>
          val index: SequentIndex = proof.endSequent.indexOfInAnt( formula )
          val history = histories( index )
          val upper = WeakeningMacroRule(
            LogicalAxiom( histories( index ).initial ),
            endSequent.antecedent ++: Sequent() :+ histories( index ).initial )
          pushAllWeakeningsToLeaves(
            WeakeningMacroRule(
              rewrite( upper, history.steps ),
              endSequent.antecedent ++:
                Sequent() :++
                proof.endSequent.succedent ) )
        case refl @ ReflexivityAxiom( _ ) =>
          WeakeningMacroRule( refl, endSequent.antecedent ++: Sequent() :++ proof.endSequent.succedent )
      }
    }
  }

  def rewrite( proof: LKProof, rewriteSequence: RewriteSequence ): LKProof = {
    rewriteSequence.steps.foldLeft( proof ) {
      case ( subProof, Rewrite( context, equation, orientation ) ) =>
        val Apps( _, Seq( s, t ) ) = equation
        val aux = orientation match {
          case Ltor => BetaReduction.betaNormalize( App( context, s ) )
          case Rtol => BetaReduction.betaNormalize( App( context, t ) )
        }
        EqualityRightRule(
          subProof,
          IndexOrFormula.ofFormula( equation ),
          IndexOrFormula.ofFormula( aux.asInstanceOf[Formula] ),
          context )

    }
  }

  def getOrientation( eql: EqualityRule ): Orientation = {
    val Apps( _, Seq( s, t ) ) = eql.equation
    if ( BetaReduction.betaNormalize( App( eql.replacementContext, s ) ) == eql.auxFormula )
      Rtol
    else
      Ltor
  }

  def retrieveAxiom( proof: LKProof ): LKProof = {
    proof.subProofs filter {
      case LogicalAxiom( _ )     => true
      case ReflexivityAxiom( _ ) => true
      case _                     => false
    } head
  }
}