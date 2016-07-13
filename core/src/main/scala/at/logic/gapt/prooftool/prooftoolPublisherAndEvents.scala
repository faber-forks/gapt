package at.logic.gapt.prooftool

import at.logic.gapt.proofs.{ DagProof, SequentProof }

import scala.swing.event.Event
import scala.swing.{ Color, Publisher }

class ProofToolPublisher extends Publisher

case object ProofDbChanged extends Event
case object DisableMenus extends Event
case object EnableMenus extends Event
case object ShowLeaf extends Event
case object HideLeaf extends Event
case object HideTree extends Event
case object HideStructuralRules extends Event
case class HideEndSequent( pos: List[Int] ) extends Event
case class ShowAllRules( pos: List[Int] ) extends Event
case class HideProof( pos: List[Int] ) extends Event
case class ShowProof( pos: List[Int] ) extends Event
case class HideSequentProof( pos: List[Int] ) extends Event
case class ShowSequentProof( pos: List[Int] ) extends Event

case object ShowDebugBorders extends Event
case object HideDebugBorders extends Event

