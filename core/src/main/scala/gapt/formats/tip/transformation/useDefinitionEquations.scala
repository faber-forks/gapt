package gapt.formats.tip.transformation

import gapt.formats.tip.analysis.SymbolTable
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtVariableDecl

object useDefiningFormulas extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new UseDefinitionEquations( problem )()
}

/**
 * Replaces bodies of function definitions by a formula that defines the
 * function.
 *
 * Let E be the body of a function f with formal parameters X, then
 * E is replaced by the formula !X f(X) = E.
 *
 * @param problem The TIP problem in which the bodies of function definitions
 *                are to be replaced by defining formulas.
 */
class UseDefinitionEquations( problem: TipSmtProblem ) {

  problem.symbolTable = Some( SymbolTable( problem ) )

  /**
   * Replaces bodies of function definitions by defining formulas.
   *
   * @return A problem in which all function definitions have as bodies
   *         defining formulas.
   */
  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions.map {
      case fun @ TipSmtFunctionDefinition( name, _, parameters, _, body ) =>
        apply( fun )
      case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        funDefs.copy( functions = funDefs.functions map { apply } )
      case definition => definition
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    val TipSmtFunctionDefinition( name, _, parameters, _, body ) = fun
    val boundVariables =
      parameters.map { p => TipSmtVariableDecl( p.name, p.typ ) }
    val arguments = parameters map { p => TipSmtIdentifier( p.name ) }
    fun.copy( body =
      if ( boundVariables.isEmpty )
        TipSmtEq( Seq( TipSmtFun( name, arguments ), body ) )
      else
        TipSmtForall(
          boundVariables,
          TipSmtEq( Seq( TipSmtFun( name, arguments ), body ) ) ) )
  }
}
