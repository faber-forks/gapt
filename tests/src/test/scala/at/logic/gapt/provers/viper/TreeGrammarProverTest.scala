package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.{ MutableContext, SequentMatchers }
import at.logic.gapt.provers.escargot.QfUfEscargot
import at.logic.gapt.provers.maxsat.MaxSat4j
import at.logic.gapt.provers.viper.grammars.{ TreeGrammarProver, TreeGrammarProverOptions }
import org.specs2.mutable.Specification

class TreeGrammarProverTest extends Specification with SequentMatchers {

  "linear" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"
    val opts = TreeGrammarProverOptions( smtSolver = QfUfEscargot, maxSATSolver = MaxSat4j )
    val sequent = hos"p(0), !x (p(x) -> p(s(x))) :- !x p(x)"
    val prover = new TreeGrammarProver( ctx, sequent, opts )
    val lk = prover.solve()
    lk.endSequent must beMultiSetEqual( sequent )
  }

}
