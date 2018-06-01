package gapt.proofs.lk

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Substitution
import gapt.expr.freeVariables
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

private object splitEquationRewriteSequence {

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

private object dropIdentityRewriteSteps {
  def apply( rewriteSequence: RewriteSequence ): RewriteSequence = {
    rewriteSequence.copy( steps = rewriteSequence.steps.filter {
      step =>
        val Abs( v, t ) = step.context
        freeVariables( t ).contains( v )
    } )
  }
  def apply(
    rewriteSequences: ( RewriteSequence, RewriteSequence ) ) //
    : ( RewriteSequence, RewriteSequence ) = {
    (
      dropIdentityRewriteSteps( rewriteSequences._1 ),
      dropIdentityRewriteSteps( rewriteSequences._2 ) )
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

object eliminateEqualityLeft {
  def apply( proof: LKProof ): LKProof = new EliminateEqualityLeft( proof )()
}

class EliminateEqualityLeft( proof: LKProof ) {

  private val endSequent: Sequent[Formula] = proof.conclusion

  def apply(): LKProof = {
    apply( proof, initialHistory( proof.conclusion ) )
  }

  private def constructNewHistory(
    principalHistory:   History,
    equationHistory:    History,
    replacementContext: Abs,
    orientation:        Orientation ): History = {

    val ( s0Tos, t0Tot ) =
      orientation match {
        case Ltor => dropIdentityRewriteSteps(
          splitEquationRewriteSequence( equationHistory.steps ) )
        case Rtol => dropIdentityRewriteSteps(
          splitEquationRewriteSequence( equationHistory.steps ) ) swap
      }

    History(
      principalHistory.initial,
      principalHistory.steps ++
        constructRewriteSequence(
          replacementContext, equationHistory, orientation ) )
  }

  private def apply(
    eqr: EqualityRightRule, histories: Sequent[History] ): LKProof = {
    val equationHistory = histories( eqr.eqInConclusion )
    val rewriteSequence =
      constructRewriteSequence(
        eqr.replacementContext,
        equationHistory,
        getOrientation( eqr ) )

    rewrite( apply( eqr.subProof, histories ), rewriteSequence.reverse )
  }

  /**
   * Constructs a rewrite sequence based on a given equation and context.
   *
   * @param replacementContext The replacement context x.A(x).
   * @param equationHistory The rewriting history of an equation s = t.
   * @param orientation The orientation in which the equation s = t is to
   * to be applied.
   * @return If the orientation is left-to-right, then a rewrite sequence that
   * rewrites a formula of the form A(s) to the formula A(t) is returned,
   * otherwise a rewrite sequence that rewrites A(t) to A(s) is returned.
   */
  private def constructRewriteSequence(
    replacementContext: Abs,
    equationHistory:    History,
    orientation:        Orientation ): RewriteSequence = {
    val ( s0Tos, t0Tot ) =
      orientation match {
        case Ltor => dropIdentityRewriteSteps(
          splitEquationRewriteSequence( equationHistory.steps ) )
        case Rtol => dropIdentityRewriteSteps(
          splitEquationRewriteSequence( equationHistory.steps ) ) swap
      }

    val sTos0 = s0Tos.reverse
    val AsToAs0 = sTos0.lift( replacementContext )
    val At0ToAt = t0Tot.lift( replacementContext )

    AsToAs0 ++
      RewriteSequence(
        Seq(
          Rewrite(
            replacementContext,
            equationHistory.initial,
            orientation ) ) ) ++ At0ToAt
  }

  def updateHistories(
    histories:      Sequent[History],
    newAuxHistory:  History,
    auxiliaryIndex: SequentIndex,
    eql:            EqualityLeftRule ): Sequent[History] = {
    histories.zipWithIndex.map {
      case ( _, index ) =>
        if ( index == auxiliaryIndex )
          newAuxHistory
        else
          histories( eql.getSequentConnector.child( index ) )
    }
  }

  private def apply(
    eql: EqualityLeftRule, histories: Sequent[History] ): LKProof = {
    val principalIndex = eql.mainIndices.head
    val equationIndex = eql.eqInConclusion
    val auxiliaryIndex = eql.aux

    val auxiliaryHistory =
      constructNewHistory(
        histories( principalIndex ),
        histories( equationIndex ),
        eql.replacementContext,
        getOrientation( eql ) )

    val newHistories =
      updateHistories( histories, auxiliaryHistory, auxiliaryIndex, eql )

    apply( eql.subProof, newHistories )
  }

  private def apply( proof: LKProof, histories: Sequent[History] ): LKProof = {
    proof match {
      case eql @ EqualityLeftRule( _, _, _, _ ) =>
        apply( eql, histories )

      case eqr @ EqualityRightRule( _, _, _, _ ) =>
        apply( eqr, histories )

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
          WeakeningMacroRule(
            refl,
            endSequent.antecedent ++: Sequent() :++ proof.endSequent.succedent )
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
    if ( BetaReduction.betaNormalize( App( eql.replacementContext, s ) ) ==
      eql.auxFormula )
      Rtol
    else
      Ltor
  }
}

object retrieveAxiom {
  def apply( proof: LKProof ): LKProof = {
    proof.subProofs filter {
      case LogicalAxiom( _ )     => true
      case ReflexivityAxiom( _ ) => true
      case _                     => false
    } head
  }
}
