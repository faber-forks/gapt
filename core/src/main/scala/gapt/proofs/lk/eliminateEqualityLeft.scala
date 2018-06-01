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

object eliminateEqualityLeft {

  private sealed trait Orientation
  private case object Ltor extends Orientation
  private case object Rtol extends Orientation

  private case class RewriteSequence( steps: Seq[Rewrite] ) {

    /**
     * Lifts the contexts of a rewrite sequence.
     *
     * @param context The context x.B(x) into which the contexts of the rewrite
     * sequence are lifted.
     * @return Let (s_1 = t_1, x.A_1(x), o_1), ..., (s_n = t_n, x.A_n(x), o_n)
     * be the original rewrite sequence. Then the following rewrite sequence is
     * returned: (s_1 = t_1, x.B(A_1(x)), o_1), ..., (s_n = t_n, x.B(A_n(x)),
     * o_n).
     */
    def lift( context: Abs ): RewriteSequence =
      this.copy( steps = steps.map { _.lift( context ) } )

    /**
     * Concatenates two rewrite sequences.
     *
     * @param rewriteSequence The rewrite sequence whose steps are to be
     * appended to this rewrite sequence.
     * @return The rewrite sequence resulting of the concatenation of the steps
     * of this rewrite sequence with the steps of the given rewrite sequence.
     */
    def ++( rewriteSequence: RewriteSequence ): RewriteSequence =
      RewriteSequence( steps ++ rewriteSequence.steps )

    /**
     * Inverts this rewrite sequence.
     *
     * @return The rewrite sequence obtained from this rewrite sequence by
     * inverting each individual step and by reversing the resulting steps.
     */
    def reverse: RewriteSequence =
      RewriteSequence( steps map { _.reverse } reverse )
  }

  private case class Rewrite(
      context:     Abs,
      equation:    Formula,
      orientation: Orientation ) {

    /**
     * Lifts a rewrite step into a context.
     *
     * @param context The context x.B(x) into which the rewrite step is lifted.
     * @return Let x.A(x) be the original context, then a rewrite step with the
     * same equation, orientation and with context x.B(A(x)) is returned.
     */
    def lift( context: Abs ): Rewrite =
      this.copy( context = liftContext( context, this.context ) )

    /**
     * Reverses a rewrite by inverting its orientation.
     *
     * @return A rewrite step consisting having the same equation and context
     * but with inverted orientation.
     */
    def reverse: Rewrite = {
      val newOrientation = orientation match {
        case Ltor => Rtol
        case Rtol => Ltor
      }
      this.copy( orientation = newOrientation )
    }
  }

  private object splitEquationRewriteSequence {

    /**
     * Splits a rewrite sequence for an equational formula.
     *
     * @param rewriteSequence A rewrite sequence rewriting a formula s_1 = t_1
     * into a formula s_2 = t_2.
     * @return A pair of rewrite sequences that rewrite s_1 to s_2 and t_1 to
     * t_2, respectively.
     */
    def apply(
      rewriteSequence: RewriteSequence ): //
      ( RewriteSequence, RewriteSequence ) = {
      val ( stepsL, stepsR ) = rewriteSequence.steps.map {
        splitEquality
      }.unzip
      ( RewriteSequence( stepsL ), RewriteSequence( stepsR ) )
    }

    /**
     * Splits a rewrite step for an equational formula.
     *
     * @param step A rewrite step rewriting a formula s_1 = t_1 into a formula
     * s_2 = t_2.
     * @return A pair of rewrite steps rewriting s_1 to s_2 and t_1 to t_2
     * respectively.
     */
    private def splitEquality( step: Rewrite ): ( Rewrite, Rewrite ) = {
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

    /**
     * Discards all useless rewrite steps.
     *
     * A rewrite step is considered useless if its contexts is of the form
     * x.A and x is not a free variable of A.
     *
     * @param rewriteSequence The rewrite sequence whose useless rewrite steps
     * are to be removed.
     * @return A rewrite sequence obtained from the given one by discarding
     * all useless rewrite steps.
     */
    def apply( rewriteSequence: RewriteSequence ): RewriteSequence = {
      rewriteSequence.copy( steps = rewriteSequence.steps.filter {
        step =>
          val Abs( v, t ) = step.context
          freeVariables( t ).contains( v )
      } )
    }

    /**
     * Discards all useless rewrite steps in a pair of rewrite sequences.
     *
     * @param rewriteSequences A pair of rewrite sequences.
     * @return A pair of rewrite sequences obtained from the given pair by
     * applying `dropIdentityRewriteSteps` pointwise.
     */
    def apply(
      rewriteSequences: ( RewriteSequence, RewriteSequence ) ) //
      : ( RewriteSequence, RewriteSequence ) = {
      (
        dropIdentityRewriteSteps( rewriteSequences._1 ),
        dropIdentityRewriteSteps( rewriteSequences._2 ) )
    }
  }

  object liftContext {

    /**
     * Lifts a context into another context.
     *
     * @param outerContext A context of the form x.B(x).
     * @param innerContext A context of the form y.A(y).
     * @return The context y.B(A(y)).
     */
    def apply( outerContext: Abs, innerContext: Abs ): Abs = {
      val Abs( innerVar, innerExpr ) = innerContext
      val Abs( outerVar, outerExpr ) = outerContext
      Abs( innerVar, Substitution( outerVar, innerExpr )( outerExpr ) )
    }
  }

  /**
   * Represents the rewrite history of a formula.
   *
   * @param initial The initial formula.
   * @param steps The rewrite steps applied to the initial formula.
   */
  case class History( initial: Formula, steps: RewriteSequence )

  object initialHistory {

    /**
     * Creates the initial history for a given sequent.
     *
     * @param sequent A sequent A_1, ..., A_n :- B_1, ..., B_m for which the
     * initial history is to be constructed.
     * @return A sequent of the form History(A_1,[]), ...,History(A_n,[]) :-
     * History(B_1,[]), ..., History(B_m, []).
     */
    def apply( sequent: Sequent[Formula] ): Sequent[History] =
      sequent.map { History( _, RewriteSequence( Seq() ) ) }
  }

  /**
   * Eliminates all (=l) inferences from a nice equality sequence.
   *
   * @param proof A nice equality sequence from which (=l) inferences are
   * to be eliminated.
   * @return A normal equality sequence of the same end-sequent.
   */
  def apply( proof: LKProof ): LKProof = new EliminateEqualityLeft( proof )()

  private class EliminateEqualityLeft( proof: LKProof ) {

    private val endSequent: Sequent[Formula] = proof.conclusion

    /**
     * Eliminates all (=l) inferences from a nice equality sequence.
     *
     * @return A normal equality sequence of the same end-sequent as the given
     * end-sequent of the given proof.
     */
    def apply(): LKProof = {
      apply( proof, initialHistory( proof.conclusion ) )
    }

    /**
     * Constructs a history for a formula obtained by rewriting.
     *
     * Let A_0 be the initial formula of A(s), let steps(A) be the
     * rewrite steps used to derive A(s), let s_0 = t_0 be the initial formula
     * or s = t, then the constructed history is of the form
     * History(A_0, steps(A) -> A(s) -> A(s_0) -> A(t_0) -> A(t)).
     *
     * @param principalHistory The history of the formula A(s).
     * @param equationHistory The history of the formula s = t ( or t = s,
     * depending on the orientation ).
     * @param replacementContext The replacement context x.A(x).
     * @param orientation The orientation of the equation s = t.
     * @return The history of the formula A(t).
     */
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

    /**
     * Updates the history sequent.
     *
     * @param histories The old history sequent.
     * @param newAuxHistory The history to be inserted at the given index.
     * @param auxiliaryIndex The index at which the given history is to be
     * inserted.
     * @param eql The equality left inference with respect to which the
     * new histories are arranged.
     * @return A history sequent whose elements are obtained from the given
     * histories by the permutation given by the equality left formula and
     * whose element at index `auxiliaryIndex` is `newAuxHistory`.
     */
    private def updateHistories(
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

    /**
     * Eliminates (=l) inferences from the given nice equality sequence.
     *
     * @param eqr The nice equality sequence from which (=l) inferences are
     * to be eliminated.
     * @param histories A sequent of histories of the formulas in the given
     * equality sequence with respect to the target sequent.
     * @return A normal equality sequence of whose end-sequent's antecedent
     * contains the initial formulas of the histories and whose end-sequent's
     * succeedent is the same as the succeedent of the end-sequent of the
     * given equality sequence.
     */
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
     * Eliminates (=l) inferences from the given nice equality sequence.
     *
     * @param eql The nice equality sequence from which (=l) inferences are
     * to be eliminated.
     * @param histories A sequent of histories of the formulas in the given
     * equality sequence with respect to the target sequent.
     * @return A normal equality sequence of whose end-sequent's antecedent
     * contains the initial formulas of the histories and whose end-sequent's
     * succeedent is the same as the succeedent of the end-sequent of the
     * given equality sequence.
     */
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

    /**
     * Eliminates (=l) inferences from the given nice equality sequence.
     *
     * @param proof The nice equality sequence from which (=l) inferences are
     * to be eliminated.
     * @param histories A sequent of histories of the formulas in the given
     * equality sequence with respect to the target sequent.
     * @return A normal equality sequence of whose end-sequent's antecedent
     * contains the initial formulas of the histories and whose end-sequent's
     * succeedent is the same as the succeedent of the end-sequent of the
     * given equality sequence.
     */
    private def apply(
      proof: LKProof, histories: Sequent[History] ): LKProof = {
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
              endSequent.antecedent ++:
                Sequent() :+ histories( index ).initial )
            pushAllWeakeningsToLeaves(
              WeakeningMacroRule(
                rewrite( upper, history.steps ),
                endSequent.antecedent ++:
                  Sequent() :++
                  proof.endSequent.succedent ) )
          case refl @ ReflexivityAxiom( _ ) =>
            WeakeningMacroRule(
              refl,
              endSequent.antecedent ++:
                Sequent() :++
                proof.endSequent.succedent )
        }
      }
    }

    /**
     * Rewrites a formula in the succeedent.
     *
     * @param proof The proof whose end-sequent is of the form G => D, A(s)
     * where G contains all the equations used by the given rewrite sequence.
     * @param rewriteSequence A rewrite sequence that rewrites A(s) to A(t).
     * @return A proof obtained from proof by appending a sequence of
     * equality right inferences that rewrite the formula A(s) into the
     * formula A(t).
     */
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
  }

  object getOrientation {

    /**
     * Retrieves the orientation of an equality inference.
     *
     * @param eq The equality inference whose orientation is to be retrieved.
     * @return Ltor if the equality inference applies the equation from
     * left to right, Rtol otherwise.
     */
    def apply( eq: EqualityRule ): Orientation = {
      val Apps( _, Seq( s, t ) ) = eq.equation
      if ( BetaReduction.betaNormalize( App( eq.replacementContext, s ) ) ==
        eq.auxFormula )
        Rtol
      else
        Ltor
    }
  }

  object retrieveAxiom {

    /**
     * Retrieves the axiom of a list-like proof tree.
     *
     * @param proof The list-like proof whose axiom is to be retrieved.
     * @return The axiom of the given proof.
     */
    def apply( proof: LKProof ): LKProof = {
      proof.subProofs filter {
        case LogicalAxiom( _ )     => true
        case ReflexivityAxiom( _ ) => true
        case _                     => false
      } head
    }
  }
}

