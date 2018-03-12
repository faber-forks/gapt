package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr.{ TBase, _ }
import at.logic.gapt.proofs.{ Ant, Checkable, Context, Sequent }
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun }

object addRecorsorsExamples extends Script {

  var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += InductiveType(
    ty"conjj ?c  ?b",
    hoc"pairr{?c ?b}: ?c > ?b > conjj ?c ?b" )
  ctx += InductiveType(
    ty"list ?a",
    hoc"nil{?a}: list ?a",
    hoc"cons{?a}: ?a > list ?a > list ?a" )
  ctx += InductiveType(
    ty"bitree ?a",
    hoc"leaf{?a}: ?a > bitree ?a",
    hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

  implicit var systemT = MRealizability.systemT( ctx )
  println( systemT )

  systemT += Definition( Const( "length", ty"list ?a > nat", List( ty"?a" ) ), le"listRec(0,^(z1:?a)^(z2: list ?a)^(z3:nat) s(z3))" )
  systemT += Definition( Const( "mirror", ty"bitree ?a > bitree ?a", List( ty"?a" ) ), le"bitreeRec( (^(x:?a)leaf(x)), (^(z1:bitree ?a)^(z2:bitree ?a)^(z3:bitree ?a)^(z4:bitree ?a) node(z4,z2)) )" )

  val plus = le"natRec(s(s(0)))(^z1 ^z2 (s(z2)))"
  println( normalize( App( plus, le"s(s(0))" ) ) )

  val pluspair = le"conjjRec (^x ^y natRec(x,(^z1 ^z2 (s(z2))),y))"
  println( normalize( App( pluspair, le"pairr(s(0),s(s(0)))" ) ) )

  println( normalize( le"length( cons(nil,cons(nil,cons(nil,nil))) )" ) )

  println( normalize( le"mirror( node( leaf(0) , leaf(s(0)) ) )" ) )

  val sum = le"bitreeRec((^x x),(^t1 ^y1 ^t2 ^y2 (natRec(y1,(^z1 ^z2 (s(z2))),y2))))"
  println( normalize( App( sum, le"node(leaf(0),node(leaf(s(0)),leaf(s(s(0)))))" ) ) )
}

object test {
  def apply( proof: NDProof )( implicit ctx: Context ): Unit = {
    val m1 = MRealizability.mrealize( proof, false )
    print( proof ); print( m1 ); print( " of type " ); println( m1._2.ty )
    val m1n = MRealizability.mrealize( proof )
    print( "normalized with respect to the empty program: " ); print( m1n )
    println(); println()
  }
}

object examplesLogicalAxiom extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"P(x)" )
  test( a1 )

  val a2 = LogicalAxiom( hof"x = y" )
  test( a2 )

  val a3 = LogicalAxiom( hof"(x:nat) = y" )
  test( a3 )

  val a4 = LogicalAxiom( hof"x = 0 & y = 0" )
  test( a4 )

  val a5 = LogicalAxiom( hof" 0 + 0 = 0" )
  test( a5 )

  val a6 = LogicalAxiom( hof"!x ?y x + y = s(x)" )
  test( a6 )
}

object examplesEqualityIntroRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"s(s(s(0)))" )
  test( a1 )

  val a2 = EqualityIntroRule( le"x + s(y + z)" )
  test( a2 )

  val a3 = EqualityIntroRule( le"s(s(s(0)))" )
  test( a3 )

  val a4 = EqualityIntroRule( le"x + s(y + z)" )
  test( a4 )
}

object examplesWeakeningRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"s(s(y))" )
  val a11 = WeakeningRule( a1, hof"!x x = x + (0 + s(z))" )
  test( a11 )

  val a2 = LogicalAxiom( hof"s(x) = s(s(y))" )
  val a22 = WeakeningRule( a2, hof"!x x = x + (0 + s(z))" )
  test( a22 )

  val a3 = LogicalAxiom( hof"(x : nat) = y" )
  test( a3 )

  val a33 = WeakeningRule( a3, hof"!(x:nat) x = z" )
  test( a33 )

  val a333 = WeakeningRule( a33, hof"?(x : nat) x = y" )
  test( a333 )
}

object exampleContractionRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"x = 0" )
  test( a1 )

  val a2 = WeakeningRule( a1, hof"(x:nat) = z" )
  test( a2 )

  val a3 = WeakeningRule( a2, hof"(x:nat) = y" )
  test( a3 )

  val a4 = WeakeningRule( a3, hof"(x:nat) = y" )
  test( a4 )

  val a5 = ContractionRule( a4, hof"(x:nat) = y" )
  test( a5 )

  val a55 = ContractionRule( a4, Ant( 1 ), Ant( 0 ) )
  test( a55 )

  val a6 = WeakeningRule( a5, hof"0 = 0" )
  test( a6 )
}

object examplesConjuctionRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"0 = 0 & s(0) = s(0)" )
  val a2 = AndElim1Rule( a1 )
  test( a2 )

  val a11 = LogicalAxiom( hof"x = 0 & y = 0" )
  val a22 = AndElim2Rule( a11 )
  test( a22 )

  val a111 = LogicalAxiom( hof"x = 0" )
  val a222 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = AndIntroRule( a111, a222 )
  val a4 = AndElim1Rule( a3 )
  test( a4 )
}

object examplesImplicationRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"s(0) = s(0) -> 0 = 0" )
  val a2 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = ImpElimRule( a1, a2 )
  test( a3 )

  val a11 = LogicalAxiom( hof"0 = 0" )
  val a22 = WeakeningRule( a11, hof"s(0) = s(0)" )
  val a33 = ImpIntroRule( a22, Ant( 0 ) )
  test( a33 )
  val a44 = ImpIntroRule( a33 )
  test( a44 )
}

object examplesForallIntroRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"x + s(y)" )
  val a2 = ForallIntroRule( a1, hov"x:nat", hov"z:nat" )
  test( a2 )

  val a3 = ForallIntroRule( a2, hov"y:nat", hov"y:nat" )
  test( a3 )
}

object exampleExistsElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"?x (x = 0)" )
  val a2 = EqualityIntroRule( le"0" )
  val a3 = WeakeningRule( a2, hof"y = 0" )
  val a4 = ExistsElimRule( a1, a3, hov"y:nat" )
  test( a4 )
}

object examplesEqualityElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"!(x0:nat) !(x1:nat) s(x2) = x2 + s(0)" )
  val a2 = LogicalAxiom( hof"(x2:nat) = x3" )
  val a3 = EqualityElimRule( a2, a1 )
  test( a3 )

  val b1 = LogicalAxiom( hof"s(x) = x + s(0)" )
  val b2 = LogicalAxiom( hof"!z s(x) = z" )
  val b3 = EqualityElimRule( b1, b2 )
  val b4 = LogicalAxiom( hof"s(0) = 0 + s(0)" )
  val b5 = EqualityElimRule( b4, b3 )
  test( b5 )
}

object exampleForallElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"!x ?y x = s(y)" )
  val a2 = ForallElimRule( a1, le"s(s(0))" )
  test( a2 )
}

object exampleExistsIntroRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"s(s(x))" )
  val a2 = ExistsIntroRule( a1, hof"y = s(s(x))", le"s(s(x))", hov"y:nat" )
  test( a2 )
}

object exampleBotElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"⊥" )
  val a2 = WeakeningRule( a1, hof"!x ?y y = s(x)" )
  val a3 = BottomElimRule( a2, hof"!x ?y x = s(y)" )
  test( a3 )
}

object examplesInductionRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val s0 = LogicalAxiom( hof"!x x + 0 = x" )
  val s01 = ForallElimRule( s0, le"0" )
  val s1 = LogicalAxiom( hof"!x !y s(x) + y = s(x + y)" )
  val s2 = ForallElimRule( s1, le"x0: nat" )
  val s3 = ForallElimRule( s2, le"0" )
  val s4 = LogicalAxiom( hof"x0 + 0 = x0" )
  val s5 = EqualityElimRule( s4, s3, hof"s(x0) + 0 = s(z)", hov"z: nat" )
  val cases = Seq(
    InductionCase( s01, hoc"0", Seq.empty, Seq.empty ),
    InductionCase( s5, hoc"s", Seq( Ant( 0 ) ), Seq( hov"x0: nat" ) ) )
  val p = InductionRule( cases, Abs( Var( "x", TBase( "nat" ) ), hof"x + 0 = x" ), le"x : nat" )
  test( p )

  val a1 = LogicalAxiom( hof"P(0)" )
  val b1 = LogicalAxiom( hof"!x (P(x) -> P(s(x)))" )
  val b2 = ForallElimRule( b1, le"x:nat" )
  val b3 = LogicalAxiom( hof"P(x:nat)" )
  val b4 = ImpElimRule( b2, b3 )
  val casess = Seq(
    InductionCase( a1, hoc"0", Seq(), Seq() ),
    InductionCase( b4, hoc"s", Seq( Ant( 1 ) ), Seq( hov"x:nat" ) ) )
  val c3 = InductionRule( casess, Abs( hov"x:nat", hof"P(x:nat)" ), le"x:nat" )
  val d1 = ForallIntroRule( c3, hov"x:nat", hov"x:nat" )
  val d2 = ImpIntroRule( d1, Ant( 0 ) )
  val d3 = ImpIntroRule( d2 )
  test( d3 )
}

object exampleTopIntroRule extends Script {

  implicit var ctx = Context()

  val a1 = TopIntroRule()
  test( a1 )
}

object examplesNegationRules extends Script {

  implicit var ctx = Context()

  val a1 = LogicalAxiom( hof"¬a" )
  val a2 = LogicalAxiom( hof"a" )
  val a3 = NegElimRule( a1, a2 )
  test( a3 )

  val a4 = NegIntroRule( a3, Ant( 0 ) )
  test( a4 )
}

object examplesOrIntroRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"0" )
  val a2 = OrIntro1Rule( a1, hof"s(0) = 0" )
  test( a2 )

  val a3 = OrIntro2Rule( a1, hof"s(0) = 0" )
  test( a3 )
}

object exampleOrElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = LogicalAxiom( hof"x = 0 & x = s(0)" )
  val b2 = AndElim1Rule( b1 )
  val b3 = LogicalAxiom( hof"x = 0 & x = s(s(0))" )
  val b4 = AndElim1Rule( b3 )
  val b5 = LogicalAxiom( hof"(x = 0 & x = s(0)) | (x = 0 & x = s(s(0)))" )
  val b6 = OrElimRule( b5, b2, b4 )
  test( b6 )
}

object examplesTheoryAxiom extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  //val a1 = TheoryAxiom( hof"!y (y+0 = 0)" )
  val a1 = TheoryAxiom( hof"y + 0 = 0" )
  test( a1 )

  //val a2 = TheoryAxiom( hof"!z ¬(s(z) = 0)" )
  val a2 = TheoryAxiom( hof"¬ s(z) = 0" )
  test( a2 )
}

object emptyProgramType extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += InductiveType(
    ty"1",
    hoc"i : 1" )

  val natToNat = ty"nat > nat"
  print( natToNat ); print( " normalized: " ); println( MRealizability.remEmpProgType( natToNat ) )
  val one = ty"1"
  print( one ); print( " normalized: " ); println( MRealizability.remEmpProgType( one ) )
  val a = TBase( "conj", natToNat, one )
  print( a ); print( " normalized: " ); println( MRealizability.remEmpProgType( a ) )
  val b = TArr( a, a )
  print( b ); print( " normalized: " ); println( MRealizability.remEmpProgType( b ) )
  val c = TArr( b, one )
  print( c ); print( " normalized: " ); println( MRealizability.remEmpProgType( c ) )
  val d = TArr( one, b )
  print( d ); print( " normalized: " ); println( MRealizability.remEmpProgType( d ) )
}

object exampleSuccessorFunction extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "x + 0 = x",
    "x + s(y) = s(x + y)" )

  val a1 = EqualityIntroRule( le"x + s(0)" )
  val a2 = ExistsIntroRule( a1, hof"y = x + s(0)", le"x + s(0)", hov"y:nat" )
  val a3 = ForallIntroRule( a2, hov"x:nat", hov"x:nat" )
  test( a3 )

  val b1 = EqualityIntroRule( le"s(x)" )
  val b2 = DefinitionRule( b1, hof"s(x) = x + s(0)" )
  Checkable.requireDefEq( b1.conclusion.succedent( 0 ), b2.conclusion.succedent( 0 ) )
  val b3 = ExistsIntroRule( b2, hof"y = x + s(0)", le"s(x)", hov"y:nat" )
  val b4 = ForallIntroRule( b3, hov"x:nat", hov"x:nat" )
  test( b4 )
}

object mrealizerDivisionByTwo extends Script {

  val m1 = MRealizability.mrealize( divisionByTwo.proof, false )( divisionByTwo.ctx )
  val m1n = MRealizability.mrealize( divisionByTwo.proof )( divisionByTwo.ctx )

  implicit var systemT = MRealizability.systemT( divisionByTwo.ctx )

  print( divisionByTwo.proof ); print( m1 ); print( " of type " ); println( m1._2.ty )
  print( "normalized: " ); print( m1n ); print( " of type " ); println( m1n._2.ty )

  println()

  def test( x: Expr ) = println( x + " divided by 2 is: " + normalize( le"pi1(${App( m1._2, x )})" ) )
  test( le"0" )
  test( le"s(0)" )
  test( le"s(s(0))" )
  test( le"s(s(s(0)))" )
  test( le"s(s(s(s(0))))" )
  test( le"s(s(s(s(s(0)))))" )
  test( le"s(s(s(s(s(s(0))))))" )
}

object divisionByTwo {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "x + 0 = x",
    "x + s(y) = s(x + y)" )
  ctx += PrimRecFun(
    hoc"'*': nat>nat>nat",
    "x * 0 = 0",
    "x * s(y) = (x * y) + x" )

  val mo1 = LogicalAxiom( hof"(x:nat) = (y:nat)" )
  val mo2 = EqualityIntroRule( le"s(x)" )
  val mo3 = EqualityElimRule( mo1, mo2, hof"s(x)=s(z)", hov"z:nat" )
  val mo4 = ImpIntroRule( mo3 )
  val mo5 = ForallIntroRule( mo4, hov"y:nat", hov"y:nat" )
  val mo6 = ForallIntroRule( mo5, hov"x:nat", hov"x:nat" )

  val b1 = EqualityIntroRule( le"0" )
  val b2 = DefinitionRule( b1, hof"0 = s(s(0)) * 0" )
  Checkable.requireDefEq( b1.conclusion.succedent( 0 ), b2.conclusion.succedent( 0 ) )
  val b3 = OrIntro1Rule( b2, hof"0 = (s(s(0)) * 0) + s(0)" )
  val b4 = ExistsIntroRule( b3, hof"0 = s(s(0)) * y | 0 = (s(s(0)) * y) + s(0)", le"0", hov"y:nat" )

  val l1 = LogicalAxiom( hof"x = s(s(0)) * z" )
  val l2 = ForallElimRule( mo6, le"x:nat" )
  val l3 = ForallElimRule( l2, le"s(s(0)) * z" )
  val l4 = DefinitionRule( l3, hof"x = s(s(0)) * z -> s(x) = (s(s(0)) * z) + s(0)" )
  Checkable.requireDefEq( le"s(s(s(0)) * z)", le"(s(s(0)) * z) + s(0)" )
  val l5 = ImpElimRule( l4, l1 )
  val l6 = OrIntro2Rule( l5, hof"s(x) = s(s(0)) * z" )
  val l7 = ExistsIntroRule( l6, hof"s(x) = s(s(0)) * y | s(x) = (s(s(0)) * y) + s(0)", le"z:nat", hov"y:nat" )

  val r1 = LogicalAxiom( hof"x = (s(s(0)) * z) + s(0)" )
  val r2 = ForallElimRule( mo6, le"x:nat" )
  val r3 = ForallElimRule( r2, le"(s(s(0)) * z) + s(0)" )
  val r4 = DefinitionRule( r3, hof"x = (s(s(0)) * z) + s(0) -> s(x) = s(s(0)) * s(z)" )
  Checkable.requireDefEq( le"s(s(s(0)) * z) + s(0)", le"s(s(0)) * s(z)" )
  val r5 = ImpElimRule( r4, r1 )
  val r6 = OrIntro1Rule( r5, hof"s(x) = (s(s(0)) * s(z)) + s(0)" )
  val r7 = ExistsIntroRule( r6, hof"s(x) = s(s(0)) * y | s(x) = (s(s(0)) * y) + s(0)", le"s(z)", hov"y:nat" )

  val i1 = LogicalAxiom( hof"?y (x = s(s(0)) * y | x = (s(s(0)) * y) + s(0))" )
  val i2 = LogicalAxiom( hof"x = s(s(0)) * z | x = (s(s(0)) * z) + s(0)" )
  val i3 = OrElimRule( i2, l7, r7 )
  val i4 = ExistsElimRule( i1, i3, hov"z:nat" )

  val cases = Seq( InductionCase( b4, hoc"0", Seq(), Seq() ), InductionCase( i4, hoc"s", Seq( Ant( 0 ) ), Seq( hov"x:nat" ) ) )
  val a1 = InductionRule( cases, Abs( hov"x:nat", hof"?y (x = s(s(0)) * y | x = (s(s(0)) * y) + s(0))" ), hov"x:nat" )
  val proof = ForallIntroRule( a1, hov"x:nat", hov"x:nat" )
}