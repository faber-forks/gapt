package at.logic.gapt.examples.autded
import at.logic.gapt.examples.PigeonHolePrinciple
import at.logic.gapt.expr.Neg
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.expr.hol.existsclosure
import at.logic.gapt.proofs.{ Sequent, FOLClause }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.MiniSAT

object exercise4 {

  println(
    """
  It is well known that the group of all permutations of n >= 2 elements
  is generated by a rotation and the transposition (1 2).

  Generate first-order clause sets by
  gapt> Permutations( n )
  for several n and describe what Permutations( n ) expresses.

  Use
  gapt> Prover9 isUnsat Permutations( n )
  to show that several of these clause sets are unsatisfiable. How far do you
  get in < 5 seconds?

  The command
  gapt> Permutations.constants( n )
  returns the set of constants which appear in Permutations( n )

  Given a set of clauses S and a set of terms T use
  gapt> instantiate( S, T )
  to obtain _all_ ground instances of S that can be formed from substituting
  terms from T.

  Use
  gapt> MiniSAT isUnsat instantiate( Permutations( n ), Permutations.constants( n ) )
  to show that Permutations( n ) is unsatisfiable using minisat. How far do you
  get in < 5 seconds?
"""
  )

}
