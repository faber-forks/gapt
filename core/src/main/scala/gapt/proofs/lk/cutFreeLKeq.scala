package gapt.proofs.lk

import gapt.expr.Apps
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
      if ( isEqualitySequence( proof.leftSubProof ) &&
        isEqualitySequence( proof.rightSubProof ) ) {
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

  def apply( finalCut: CutRule ): LKProof = {
    val weakEqualitySequence =
      pushCut( CutRule(
        eliminateEqualityLeft( finalCut.leftSubProof ),
        eliminateEqualityLeft( finalCut.rightSubProof ), finalCut.cutFormula ) )
    removeRedundantLeftContractions(
      pushAllWeakeningsToLeaves( weakEqualitySequence ) )
  }

  def pushCut( finalCut: CutRule ): LKProof = {
    finalCut.leftSubProof match {
      case LogicalAxiom( _ ) =>
        finalCut.rightSubProof
      case ReflexivityAxiom( _ ) =>
        dropRedundantEquation( finalCut.aux2, finalCut.rightSubProof )
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
        ContractionMacroRule(
          pushCut(
            CutRule(
              eqr.subProof,
              newRightSubProof,
              eqr.auxFormula ) ),
          finalCut.conclusion,
          true )
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

  private object removeRedundantLeftContractions {
    def apply( proof: LKProof ): LKProof = {
      val targetAntecedent = proof.endSequent.antecedent

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
          case crl @ ContractionLeftRule( _, _, _ ) =>
            removeContractionsLeft( crl.subProof )
        }

      removeContractionsLeft( proof )
    }
  }

  object dropRedundantEquation {
    /**
     * Discards a useless formula of the form t = t.
     *
     * Given an (=l)-free equality sequence P with an end-sequent of the form
     * t = t, G => D, this function returns an (=l)-free equality sequence
     * with end-sequent for the form G => D, containing not more inferences than
     * P.
     *
     * @param equationIndex The index of t = t in the end-sequent.
     * @param proof The equality sequence from which t = t is to be removed.
     * @return An (=l)-free equality sequence of the sequent G => D containing
     *         not more inferences than `proof`.
     */
    def apply( equationIndex: SequentIndex, proof: LKProof ): LKProof = {
      proof match {
        case eqr @ EqualityRightRule( _, _, _, _ ) //
        if eqr.eqInConclusion == equationIndex =>
          dropRedundantEquation( eqr.eq, eqr.subProof )
        case eqr @ EqualityRightRule( _, _, _, _ ) =>
          val newSubProof =
            dropRedundantEquation(
              eqr.getSequentConnector.parent( equationIndex ),
              eqr.subProof )
          EqualityRightRule(
            newSubProof,
            eqr.equation,
            eqr.auxFormula,
            eqr.replacementContext )
        case wkr @ WeakeningRightRule( _, _ ) =>
          val newSubProof =
            dropRedundantEquation(
              wkr.getSequentConnector.parent( equationIndex ),
              wkr.subProof )
          WeakeningRightRule( newSubProof, wkr.formula )
        case wkl @ WeakeningLeftRule( _, _ ) //
        if wkl.mainIndices.contains( equationIndex ) =>
          wkl.subProof
        case wkl @ WeakeningLeftRule( _, _ ) =>
          val newSubProof =
            dropRedundantEquation(
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

object isEqualitySequence {
  def apply( proof: LKProof ): Boolean = {
    proof match {
      case eqr @ EqualityRightRule( _, _, _, _ ) =>
        isEqualitySequence( eqr.subProof )
      case eql @ EqualityLeftRule( _, _, _, _ ) =>
        isEqualitySequence( eql.subProof )
      case _ => weakeningOnlySubTree( proof )
    }
  }
}
