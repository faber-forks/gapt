package gapt.proofs.lk

import gapt.expr.Apps
import gapt.expr.Formula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.reductions.CutReduction
import gapt.proofs.lk.reductions.LeftRankAndLeftReduction
import gapt.proofs.lk.reductions.LeftRankAndRightReduction
import gapt.proofs.lk.reductions.LeftRankContractionLeftReduction
import gapt.proofs.lk.reductions.LeftRankContractionRightReduction
import gapt.proofs.lk.reductions.LeftRankDefinitionLeftReduction
import gapt.proofs.lk.reductions.LeftRankDefinitionRightReduction
import gapt.proofs.lk.reductions.LeftRankExistsLeftReduction
import gapt.proofs.lk.reductions.LeftRankExistsRightReduction
import gapt.proofs.lk.reductions.LeftRankForallLeftReduction
import gapt.proofs.lk.reductions.LeftRankForallRightReduction
import gapt.proofs.lk.reductions.LeftRankImpLeftReduction
import gapt.proofs.lk.reductions.LeftRankImpRightReduction
import gapt.proofs.lk.reductions.LeftRankNegLeftReduction
import gapt.proofs.lk.reductions.LeftRankNegRightReduction
import gapt.proofs.lk.reductions.LeftRankOrLeftReduction
import gapt.proofs.lk.reductions.LeftRankOrRightReduction
import gapt.proofs.lk.reductions.RightRankAndLeftReduction
import gapt.proofs.lk.reductions.RightRankAndRightReduction
import gapt.proofs.lk.reductions.RightRankContractionLeftReduction
import gapt.proofs.lk.reductions.RightRankContractionRightReduction
import gapt.proofs.lk.reductions.RightRankDefinitionLeftReduction
import gapt.proofs.lk.reductions.RightRankDefinitionRightReduction
import gapt.proofs.lk.reductions.RightRankExistsLeftReduction
import gapt.proofs.lk.reductions.RightRankExistsRightReduction
import gapt.proofs.lk.reductions.RightRankForallLeftReduction
import gapt.proofs.lk.reductions.RightRankForallRightReduction
import gapt.proofs.lk.reductions.RightRankImpLeftReduction
import gapt.proofs.lk.reductions.RightRankImpRightReduction
import gapt.proofs.lk.reductions.RightRankNegLeftReduction
import gapt.proofs.lk.reductions.RightRankNegRightReduction
import gapt.proofs.lk.reductions.RightRankOrLeftReduction
import gapt.proofs.lk.reductions.RightRankOrRightReduction
import gapt.proofs.lk.reductions.gradeReduction

object cutFreeLKeq {

  def apply( proof: LKProof ): LKProof =

    new UppermostFirstStrategy( cutReduction ) run
      pushEqualityInferencesToLeaves( atomicWeakeningNormalForm( proof ) )

  private val rightRankReduction =
    RightRankWeakeningLeftReduction orElse
      RightRankWeakeningRightReduction orElse
      RightRankContractionLeftReduction orElse
      RightRankContractionRightReduction orElse
      RightRankDefinitionLeftReduction orElse
      RightRankDefinitionRightReduction orElse
      RightRankAndLeftReduction orElse
      RightRankAndRightReduction orElse
      RightRankOrLeftReduction orElse
      RightRankOrRightReduction orElse
      RightRankImpLeftReduction orElse
      RightRankImpRightReduction orElse
      RightRankNegLeftReduction orElse
      RightRankNegRightReduction orElse
      RightRankForallLeftReduction orElse
      RightRankForallRightReduction orElse
      RightRankExistsLeftReduction orElse
      RightRankExistsRightReduction

  private val leftRankReduction =
    LeftRankWeakeningLeftReduction orElse
      LeftRankWeakeningRightReduction orElse
      LeftRankContractionLeftReduction orElse
      LeftRankContractionRightReduction orElse
      LeftRankDefinitionLeftReduction orElse
      LeftRankDefinitionRightReduction orElse
      LeftRankAndLeftReduction orElse
      LeftRankAndRightReduction orElse
      LeftRankOrLeftReduction orElse
      LeftRankOrRightReduction orElse
      LeftRankImpLeftReduction orElse
      LeftRankImpRightReduction orElse
      LeftRankNegLeftReduction orElse
      LeftRankNegRightReduction orElse
      LeftRankForallLeftReduction orElse
      LeftRankForallRightReduction orElse
      LeftRankExistsLeftReduction orElse
      LeftRankExistsRightReduction

  private val cutReduction =
    gradeReduction orElse
      leftRankReduction orElse
      rightRankReduction orElse
      FinalCutReduction

  private object FinalCutReduction extends CutReduction {
    override def reduce( proof: CutRule ): Option[LKProof] =
      if ( isNiceEqualitySequence( proof.leftSubProof ) &&
        isNiceEqualitySequence( proof.rightSubProof ) ) {
        Some( eliminateFinalCut( proof ) )
      } else {
        None
      }
  }

  private object LeftRankWeakeningLeftReduction extends CutReduction {
    override def reduce( cut: CutRule ): Option[LKProof] =
      cut.leftSubProof match {
        case l @ WeakeningLeftRule( subProof, main ) //
        if !weakeningOnlySubTree( l ) =>
          val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
          val cutSub = CutRule(
            l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
          Some( WeakeningLeftRule( cutSub, main ) )
        case _ => None
      }
  }

  private object LeftRankWeakeningRightReduction extends CutReduction {
    override def reduce( cut: CutRule ): Option[LKProof] =
      cut.leftSubProof match {
        case l @ WeakeningRightRule( subProof, main ) //
        if !weakeningOnlySubTree( l ) =>
          Some(
            WeakeningRightRule(
              CutRule(
                subProof, l.getSequentConnector.parent( cut.aux1 ),
                cut.rightSubProof, cut.aux2 ),
              main ) )
        case _ => None
      }
  }

  private object RightRankWeakeningRightReduction extends CutReduction {
    def reduce( cut: CutRule ): Option[LKProof] =
      cut.rightSubProof match {
        case weakening @ WeakeningRightRule( _, _ ) //
        if !weakeningOnlySubTree( weakening ) =>
          val aux2Sub = weakening.getSequentConnector.parent( cut.aux2 )
          val cutSub = CutRule(
            cut.leftSubProof,
            cut.aux1,
            weakening.subProof,
            aux2Sub )
          Some( WeakeningRightRule( cutSub, weakening.mainFormula ) )
        case _ => None
      }
  }

  private object RightRankWeakeningLeftReduction extends CutReduction {
    def reduce( cut: CutRule ): Option[LKProof] =
      cut.rightSubProof match {
        case weakening @ WeakeningLeftRule( _, _ ) //
        if !weakeningOnlySubTree( weakening ) =>
          if ( cut.aux2 == cut.rightSubProof.mainIndices.head ) {
            Some( WeakeningMacroRule( weakening.subProof, cut.endSequent ) )
          } else {
            Some(
              WeakeningLeftRule(
                CutRule(
                  cut.leftSubProof,
                  cut.aux1,
                  weakening.subProof,
                  weakening.getSequentConnector.parent( cut.aux2 ) ),
                weakening.mainFormula ) )
          }
        case _ => None
      }
  }
}

object eliminateFinalCut {

  /**
   * Eliminates a final cut inference.
   *
   * A cut inference is final if its left and right subproofs are nice
   * equality sequences.
   *
   * @param finalCut The final cut to be eliminated
   * @return Returns a normal equality sequence having the same end-sequent
   * as the given final cut. This equality sequence is obtained from the given
   * final cut by equality left-elimination and local rule permutations.
   */
  def apply( finalCut: CutRule ): LKProof = {
    val weakEqualitySequence =
      pushCut( CutRule(
        eliminateEqualityLeft( finalCut.leftSubProof ),
        eliminateEqualityLeft( finalCut.rightSubProof ), finalCut.cutFormula ) )
    removeRedundantAssumptions(
      pushAllWeakeningsToLeaves( weakEqualitySequence ),
      finalCut.endSequent.antecedent )
  }

  /**
   * Eliminates a final cut inference.
   *
   * @param finalCut The final cut to be eliminated.
   * @return The resulting proof is a normal equality sequence whose
   * end-sequent is obtained from that of final cut by duplicating some
   * formulas in the antecedent. The result is obtained by permuting the cut-
   * inference upwards and by shifting equality right rules from the right
   * subproof to the left subproof.
   */
  private def pushCut( finalCut: CutRule ): LKProof = {
    finalCut.leftSubProof match {
      case LogicalAxiom( _ ) =>
        finalCut.rightSubProof
      case ReflexivityAxiom( _ ) =>
        dropReflexiveEquation( finalCut.aux2, finalCut.rightSubProof )
      case wkl @ WeakeningLeftRule( _, _ ) //
      if wkl.mainIndices.contains( finalCut.aux1 ) =>
        WeakeningMacroRule( wkl.subProof, finalCut.endSequent )
      case wkl @ WeakeningLeftRule( _, _ ) =>
        val newSubProof =
          pushCut(
            CutRule(
              wkl.subProof,
              finalCut.rightSubProof,
              finalCut.cutFormula ) )
        WeakeningLeftRule( newSubProof, wkl.formula )
      case wkr @ WeakeningRightRule( _, _ ) =>
        val newSubProof =
          pushCut(
            CutRule(
              wkr.subProof,
              finalCut.rightSubProof,
              finalCut.cutFormula ) )
        WeakeningRightRule( newSubProof, wkr.formula )
      case eqr @ EqualityRightRule( _, _, _, _ ) //
      if eqr.mainIndices.contains( finalCut.aux1 ) =>
        val newRightSubProof =
          eliminateEqualityLeft(
            pushAllWeakeningsToLeaves(
              EqualityLeftRule(
                WeakeningLeftRule( finalCut.rightSubProof, eqr.equation ),
                eqr.equation,
                eqr.mainFormula,
                eqr.replacementContext ) ) )
        pushCut( CutRule( eqr.subProof, newRightSubProof, eqr.auxFormula ) )
      case eqr @ EqualityRightRule( _, _, _, _ ) =>
        val newSubProof =
          pushCut(
            CutRule(
              eqr.subProof,
              finalCut.rightSubProof,
              finalCut.cutFormula ) )
        EqualityRightRule(
          newSubProof,
          eqr.equation,
          eqr.auxFormula,
          eqr.replacementContext )
    }
  }

  private object removeRedundantAssumptions {

    /**
     * Removes redundant assumptions from an (=l)-free equality sequence.
     *
     * An assumption is considered as redundant if it occurs twice in the
     * antecedent of the given proof's end-sequent.
     *
     * @param proof The (=l)-free equality sequence from which redundant left
     *              contractions are to be removed.
     * @param targetAntecedent Obtained from proof.antencedent by removing
     *                         duplicate formulas.
     * @return An (=l)-free equality sequence with end-sequent
     *         `targetAntecedent ++: Sequent() :++ proof.endSequent.succeedent`.
     *         The resulting proof is obtained from the given proof by omitting
     *         inference rules.
     */
    def apply( proof: LKProof, targetAntecedent: Seq[Formula] ): LKProof = {
      def removeContractionsLeft( proof: LKProof ): LKProof =
        proof match {
          case eqr @ EqualityRightRule( _, _, _, _ ) =>
            EqualityRightRule(
              removeContractionsLeft( eqr.subProof ),
              eqr.equation,
              eqr.auxFormula,
              eqr.replacementContext )
          case WeakeningLeftRule( _, _ ) | WeakeningRightRule( _, _ ) =>
            WeakeningMacroRule(
              retrieveAxiom( proof ),
              targetAntecedent ++: Sequent() :++ proof.endSequent.succedent )
        }
      removeContractionsLeft( proof )
    }
  }

  object dropReflexiveEquation {

    /**
     * Discards an assumption t = t from a (=l)-free equality sequence.
     *
     * Given an (=l)-free equality sequence P with an end-sequent of the form
     * t = t, G => D, this function returns a (=l)-fee equality sequence P'
     * with end-sequent of the form G => D. Moreover P' is obtained from P only
     * by discarding inferences.
     *
     * @param equationIndex The index of the assumption t = t in the antecedent
     *                      of the end-sequent of the given proof.
     * @param proof The (=l)-free equality sequence from which the assumption
     *              t = t is to be removed.
     * @return An (=l)-free equality sequence of the sequent G => D obtained
     *         from P by discarding inferences having t = t as main formula or
     *         equation.
     */
    def apply( equationIndex: SequentIndex, proof: LKProof ): LKProof = {
      proof match {
        case eqr @ EqualityRightRule( _, _, _, _ ) //
        if eqr.eqInConclusion == equationIndex =>
          dropReflexiveEquation( eqr.eq, eqr.subProof )
        case eqr @ EqualityRightRule( _, _, _, _ ) =>
          val newSubProof =
            dropReflexiveEquation(
              eqr.getSequentConnector.parent( equationIndex ),
              eqr.subProof )
          EqualityRightRule(
            newSubProof,
            eqr.equation,
            eqr.auxFormula,
            eqr.replacementContext )
        case wkr @ WeakeningRightRule( _, _ ) =>
          val newSubProof =
            dropReflexiveEquation(
              wkr.getSequentConnector.parent( equationIndex ),
              wkr.subProof )
          WeakeningRightRule( newSubProof, wkr.formula )
        case wkl @ WeakeningLeftRule( _, _ ) //
        if wkl.mainIndices.contains( equationIndex ) =>
          wkl.subProof
        case wkl @ WeakeningLeftRule( _, _ ) =>
          val newSubProof =
            dropReflexiveEquation(
              wkl.getSequentConnector.parent( equationIndex ),
              wkl.subProof )
          WeakeningLeftRule( newSubProof, wkl.formula )
        case LogicalAxiom( reflexivityFormula ) =>
          val Apps( _, Seq( t, _ ) ) = reflexivityFormula
          ReflexivityAxiom( t )
      }
    }
  }
}

object isNiceEqualitySequence {
  /**
   * Checks whether the given proof is a nice equality sequence.
   *
   * A proof is a nice equality sequence if it is a weakening only subtree
   * followed by some equality inferences.
   *
   * @param proof The proof to be checked.
   * @return true if the given proof is a nice equality sequence, false
   * otherwise.
   */
  def apply( proof: LKProof ): Boolean = {
    proof match {
      case eqr @ EqualityRightRule( _, _, _, _ ) =>
        isNiceEqualitySequence( eqr.subProof )
      case eql @ EqualityLeftRule( _, _, _, _ ) =>
        isNiceEqualitySequence( eql.subProof )
      case _ => weakeningOnlySubTree( proof )
    }
  }
}
