////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 2017-2020 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// DESCRIPTION:
// Builtin '@max'
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.builtins

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.frontend.Frontend
import com.argondesign.alogic.util.unreachable

private[builtins] class AtMax(implicit cc: CompilerContext) extends BuiltinPolyFunc {

  val name = "@max"

  def returnType(args: List[Expr], feOpt: Option[Frontend]): Option[TypeFund] = args partialMatch {
    case args if args.nonEmpty && (args forall { _.tpe.isNum }) => {
      TypeNum(args forall { _.tpe.isSigned })
    }
  }

  def isKnown(args: List[Expr]) = true

  val isPure: Boolean = true

  def simplify(loc: Loc, args: List[Expr]) =
    Option.when(args forall { _.isInstanceOf[ExprNum] }) {
      args match {
        case Nil       => unreachable
        case List(arg) => arg
        case args => {
          val (s, v) = (args collect { case ExprNum(signed, value) => (signed, value) }).unzip
          ExprNum(s reduceLeft { _ && _ }, v.max)
        }
      }
    }

}
