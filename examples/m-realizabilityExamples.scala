package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.InductiveType

object addRecorsorExamples extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += InductiveType(
    ty"conj ?c  ?b",
    hoc"pair: ?c > ?b > conj ?c ?b" )
  ctx += InductiveType(
    ty"list ?a",
    hoc"nil: list ?a",
    hoc"cons: ?a > list ?a > list ?a" )
  ctx += InductiveType(
    ty"bitree ?a",
    hoc"leaf: ?a > bitree ?a",
    hoc"node: bitree ?a > bitree ?a > bitree ?a" )

  println( MRealizability.addRecursors )
}

//  \x^{i}\x^{1}.x^{1}
object logicalAxiom1 extends Script {
  val a1 = LogicalAxiom( hof"P(x)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// \x^{conj 1 1}.x^{conj 1 1}
object logicalAxiom2 extends Script {
  val a1 = LogicalAxiom( hof"0 = s(0) & 0 + 0 = 0" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// \x^{i -> conj i (1 -> 1)}.x^{i -> conj i (1 -> 1)}
object logicalAxiom3 extends Script {
  val a1 = LogicalAxiom( hof"!x ?y ( x * 0 = y -> y = s(0))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// \x^{i} \y^{i} \x^{1}.x^{1}
object logicalAxiom4 extends Script {
  val a1 = LogicalAxiom( hof"x = y" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object theoryAxiom1 extends Script {
  val a1 = TheoryAxiom( hof"!z (s(z) = 0 -> ⊥)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object theoryAxiom2 extends Script {
  val a1 = TheoryAxiom( hof"!y (y*0 = 0)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object theoryAxiom3 extends Script {
  val a1 = TheoryAxiom( hof"!y (y*0 = y)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// i
object equalityIntro1 extends Script {
  val a1 = EqualityIntroRule( fot"s(s(s(0)))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// \x^{i} \y^{i} \z^{i}.i
object equalityIntro2 extends Script {
  val a1 = EqualityIntroRule( fot"s(s(s(x + (y * z))))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

// \z^{i}\y^{i}\z^{i>1}.i
object weakeningRule1 extends Script {
  val a1 = EqualityIntroRule( fot"s(s(y))" )
  val a2 = WeakeningRule( a1, hof"!x( x = x + (0 * s(z)))" )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type: " ); println( m2.ty )
}

// \z^{i}\x^{i}\y^{i}\z^{i>1}\x^{1}.x^1
object weakeningRule2 extends Script {
  val a1 = LogicalAxiom( hof"s(x) = s(s(y))" )
  val a2 = WeakeningRule( a1, hof"!x( x = x + (0 * s(z)))" )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type: " ); println( m2.ty )
}

object weakeningRule3 extends Script {
  val a1 = LogicalAxiom( hof"x = y" )
  val a2 = WeakeningRule( a1, hof"!x( x = z)" )
  val a3 = WeakeningRule( a2, hof"?x (x = y)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
  val m3 = MRealizability.mrealize( a3 )
  print( m3 ); print( " of type " ); println( m3.ty )
}

object contractionRule1 extends Script {
  val a1 = LogicalAxiom( hof"x = 0" )
  val a2 = WeakeningRule( a1, hof"x = z" )
  val a3 = WeakeningRule( a2, hof"x = y" )
  val a4 = WeakeningRule( a3, hof"x = y" )
  val a5 = ContractionRule( a4, hof"x=y" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
  val m3 = MRealizability.mrealize( a3 )
  print( m3 ); print( " of type " ); println( m3.ty )
  val m4 = MRealizability.mrealize( a4 )
  print( m4 ); print( " of type " ); println( m4.ty )
  val m5 = MRealizability.mrealize( a5 )
  print( m5 ); print( " of type " ); println( m5.ty )
}

object andElim1Rule1 extends Script {
  val a1 = LogicalAxiom( hof"0 = 0 & s(0) = s(0)" )
  val a2 = AndElim1Rule( a1 )
  val m1 = MRealizability.mrealize( a2 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object andElim2Rule1 extends Script {
  val a1 = LogicalAxiom( hof"x = 0 & y = 0" )
  val a2 = AndElim2Rule( a1 )
  val m1 = MRealizability.mrealize( a2 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object andIntroElim1 extends Script {
  val a1 = LogicalAxiom( hof"0 = 0" )
  val a2 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = AndIntroRule( a1, a2 )
  val a4 = AndElim1Rule( a3 )
  val m1 = MRealizability.mrealize( a4 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object impElimRule extends Script {
  val a1 = LogicalAxiom( hof"s(0) = s(0) -> 0 =0" )
  val a2 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = ImpElimRule( a1, a2 )
  val m1 = MRealizability.mrealize( a3 )
  print( m1 ); print( " of type" ); println( m1.ty )
}

object impIntroRule extends Script {

}

object bottomElimRule extends Script {
}

// Should give an exception.
object excludedMiddle extends Script {
}