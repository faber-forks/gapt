package gapt.proofs.lk

import gapt.expr.{ Apps, Expr, Substitution }
import gapt.proofs.SequentIndex

object unfoldInduction {
  /**
   * Unfolds an induction induction inference.
   *
   * @param induction A regular proof with an induction inference as its last inference.
   *              The induction must be a ground term in constructor form.
   * @return
   */
  def apply( induction: InductionRule ) = ( new UnfoldInduction( induction ) ).apply
}

class UnfoldInduction( induction: InductionRule ) {

  def apply = {
    val ( unfoldedProof, _ ) = constructInstanceProof( induction.term )
    WeakeningMacroRule(
      ContractionMacroRule( unfoldedProof, induction.endSequent, false ),
      induction.endSequent, false )
  }

  private def constructInstanceProof( term: Expr ): ( LKProof, SequentIndex ) = {
    val Apps( constructor, arguments ) = term
    val inductiveArguments = arguments filter { _.ty == induction.term.ty }
    val Seq( stepProof ) = induction.cases.filter { _.constructor == constructor }
    val instanceProofs: List[( ( LKProof, SequentIndex ), SequentIndex )] =
      inductiveArguments.map( constructInstanceProof ).zipWithIndex map {
        case ( ( proof, hypIndexSuc ), index ) => ( ( proof, hypIndexSuc ), stepProof.hypotheses( index ) )
      }
    val stepProofInstance = instantiateProof( arguments, stepProof )
    cutInductionHypotheses( instanceProofs, stepProofInstance, stepProof.conclusion )
  }

  /**
   * Instantiates the proof of an induction step.
   *
   * @param arguments The eigenvariables of the induction step are substituted by these terms.
   * @param inductionCase The induction case that is to be instantiated with the given terms.
   * @return The induction step instantiated for the given terms. The substitution is with respect to the ordering
   *         of the eigenvariables and the terms, i.e. the first eigenvariable is substituted by the first term, and
   *         so on.
   */
  private def instantiateProof( arguments: Seq[Expr], inductionCase: InductionCase ): LKProof = {
    val InductionCase( proof, _, _, eigenVariables, _ ) = inductionCase
    Substitution( eigenVariables zip arguments )( proof )
  }
}

private object cutInductionHypotheses {
  def apply(
    cuts:            Seq[( ( LKProof, SequentIndex ), SequentIndex )],
    stepProof:       LKProof,
    conclusionIndex: SequentIndex ): ( LKProof, SequentIndex ) = {
    cuts match {
      case Seq( cut, rest @ _* ) =>
        val ( ( proofHypothesis, hypothesisInSuc ), hypothesisInAnt ) = cut
        val intermediaryProof = CutRule( proofHypothesis, hypothesisInSuc, stepProof, hypothesisInAnt )
        // keep track of indices for remaining cuts
        val remainingCuts = rest map {
          case ( hyp, hypInAnt ) => ( hyp, intermediaryProof.getRightSequentConnector.child( hypInAnt ) )
        }
        cutInductionHypotheses(
          remainingCuts,
          intermediaryProof,
          intermediaryProof.getRightSequentConnector.child( conclusionIndex ) )
      case _ => ( stepProof, conclusionIndex )
    }
  }
}

