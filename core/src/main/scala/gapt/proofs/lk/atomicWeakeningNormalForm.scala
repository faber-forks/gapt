package gapt.proofs.lk
import gapt.expr.All
import gapt.expr.And
import gapt.expr.Ex
import gapt.expr.Imp
import gapt.expr.Neg
import gapt.expr.Or
import gapt.proofs.SequentConnector

object atomicWeakeningNormalForm {

  /**
   * Transforms a proof to atomic weakening normal form.
   *
   * A proof is in atomic weakening normal form if all of its weakening
   * inferences have an atomic main formula.
   *
   * @param proof The proof to be transformed to atomic weakening normal form.
   * @return A proof in atomic weakening normal form of the same end-sequent
   * as the given proof.
   */
  def apply( proof: LKProof ): LKProof = visitor.apply( proof, () )

  private object visitor extends LKVisitor[Unit] {
    override def visitWeakeningLeft(
      proof:    WeakeningLeftRule,
      otherArg: Unit ): ( LKProof, SequentConnector ) = {
      proof.formula match {
        case And( leftFormula, rightFormula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule(
              WeakeningLeftRule( proof.subProof, rightFormula ), leftFormula ) )
          val newProof = AndLeftRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Or( leftFormula, rightFormula ) =>
          val newLeftSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, leftFormula ) )
          val newRightSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, rightFormula ) )
          val newProof =
            OrLeftRule( newLeftSubProof, newRightSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Imp( leftFormula, rightFormula ) =>
          val newLeftSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, leftFormula ) )
          val newRightSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, rightFormula ) )
          val newProof =
            ImpLeftRule( newLeftSubProof, newRightSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Neg( formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, formula ) )
          val newProof =
            NegLeftRule( newSubProof, formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case All( v, formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, formula ) )
          val newProof =
            ForallLeftRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Ex( v, formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, formula ) )
          val newProof =
            ExistsLeftRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case _ => ( proof, SequentConnector( proof.conclusion ) )
      }
    }

    override def visitWeakeningRight(
      proof:    WeakeningRightRule,
      otherArg: Unit ): ( LKProof, SequentConnector ) =
      proof.formula match {
        case And( leftFormula, rightFormula ) =>
          val newLeftSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, leftFormula ) )
          val newRightSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, rightFormula ) )
          val newProof = AndRightRule(
            newLeftSubProof, newRightSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Or( leftFormula, rightFormula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule(
              WeakeningRightRule( proof.subProof, rightFormula ),
              leftFormula ) )
          val newProof =
            OrRightRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Imp( leftFormula, rightFormula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule(
              WeakeningLeftRule( proof.subProof, leftFormula ),
              rightFormula ) )
          val newProof =
            ImpRightRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Neg( formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningLeftRule( proof.subProof, formula ) )
          val newProof =
            NegRightRule( newSubProof, formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case All( v, formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, formula ) )
          val newProof =
            ForallRightRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case Ex( v, formula ) =>
          val newSubProof = atomicWeakeningNormalForm(
            WeakeningRightRule( proof.subProof, formula ) )
          val newProof =
            ExistsRightRule( newSubProof, proof.formula )
          (
            newProof,
            SequentConnector.guessInjection(
              proof.conclusion,
              newProof.conclusion ).inv )
        case _ => ( proof, SequentConnector( proof.conclusion ) )
      }
  }
}
