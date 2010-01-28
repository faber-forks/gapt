/*
 * quantificationRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import propositionalRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._

package quantificationRules {

  // Quanitifier rules
  case object ForallLeftRuleType extends UnaryRuleTypeA
  case object ForallRightRuleType extends UnaryRuleTypeA
  case object ExistsLeftRuleType extends UnaryRuleTypeA
  case object ExistsRightRuleType extends UnaryRuleTypeA

  object ForallLeftRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, term: HOLTerm) : LKProof =
      s1.root.antecedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, term )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
        }

    def apply(s1: LKProof, aux_fo: FormulaOccurrence, main: Formula, term: HOLTerm) : LKProof = {
      main match {
        case All( sub, _ ) => {
          val aux_form = betaNormalize( App( sub, term ) )
          assert( aux_form == aux_fo.formula, "The computed auxiliary formula " + aux_form.toStringSimple + " is not equal to the formula " + aux_fo.formula.toStringSimple + " at the given occurrence")
            val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil)
            new UnaryTree[SequentOccurrence](
              SequentOccurrence(createContext((s1.root.antecedent - aux_fo)) + prinFormula,
                                createContext((s1.root.succedent))), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
              def rule = ForallLeftRuleType
              def aux = (aux_fo::Nil)::Nil
              def prin = prinFormula::Nil
              def subst = term
            }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ForallLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.subst))
      }
      else None
  }

  object ExistsRightRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, term: HOLTerm) : LKProof = {
      s1.root.succedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, term )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
        }
    }

    def apply(s1: LKProof, aux_fo: FormulaOccurrence, main: Formula, term: HOLTerm) : LKProof = {
      main match {
        case Ex( sub, _ ) => {
          assert( betaNormalize( App( sub, term ) ) == aux_fo.formula )
          val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil)
          new UnaryTree[SequentOccurrence](
              SequentOccurrence(createContext(s1.root.antecedent),
                                createContext((s1.root.succedent - aux_fo)) + prinFormula), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ExistsRightRuleType
            def aux = (aux_fo::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = term
          }
        }
        case _ => throw new LKRuleCreationException("Main formula of ExistsRightRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ExistsRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.subst))
      }
      else None
  }

  object ForallRightRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, eigen_var: HOLVar) : LKProof =
      s1.root.succedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, eigen_var )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def apply( s1: LKProof, aux_fo: FormulaOccurrence, main: Formula, eigen_var: HOLVar ) : LKProof =
      main match {
        case All( sub, _ ) => {
          // eigenvar condition
          assert( ( s1.root.antecedent ++ (s1.root.succedent - aux_fo) ).forall( fo => !fo.formula.getFreeAndBoundVariables._1.contains( eigen_var ) ),
            "Eigenvariable " + eigen_var.toStringSimple + " occurs in context " + s1.root.getSequent.toStringSimple )
          // correct auxiliary formula
          assert( betaNormalize( App( sub, eigen_var ) ) == aux_fo.formula )
              val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil)
              new UnaryTree[SequentOccurrence](
                  SequentOccurrence(createContext(s1.root.antecedent),
                                    createContext((s1.root.succedent - aux_fo)) + prinFormula), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
                def rule = ForallRightRuleType
                def aux = (aux_fo::Nil)::Nil
                def prin = prinFormula::Nil
                def eigenvar = eigen_var
              }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallRightRule must have a universal quantifier as head symbol.")
      }

    def unapply(proof: LKProof) = if (proof.rule == ForallRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.eigenvar))
      }
      else None
  }

  object ExistsLeftRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, eigen_var: HOLVar) : LKProof =
      s1.root.antecedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, eigen_var )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def apply( s1: LKProof, aux_fo: FormulaOccurrence, main: Formula, eigen_var: HOLVar ) : LKProof =
      main match {
        case Ex( sub, _ ) => {
          // eigenvar condition
          assert( ( (s1.root.antecedent - aux_fo) ++ s1.root.succedent ).forall( fo => !fo.formula.getFreeAndBoundVariables._1.contains( eigen_var ) ),
            "Eigenvariable " + eigen_var.toStringSimple + " occurs in context " + s1.root.getSequent.toStringSimple )
          // correct auxiliary formula
          assert( betaNormalize( App( sub, eigen_var ) ) == aux_fo.formula )
          val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil)
          new UnaryTree[SequentOccurrence](
              SequentOccurrence(createContext((s1.root.antecedent - aux_fo)) + prinFormula,
                                createContext((s1.root.succedent))), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
            def rule = ExistsLeftRuleType
            def aux = (aux_fo::Nil)::Nil
            def prin = prinFormula::Nil
            def eigenvar = eigen_var
          }
        }
        case _ => throw new LKRuleCreationException("Main formula of ExistsLeftRule must have an existential quantifier as head symbol.")
      }

      def unapply(proof: LKProof) = if (proof.rule == ExistsLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.eigenvar))
      }
      else None
  }
}
