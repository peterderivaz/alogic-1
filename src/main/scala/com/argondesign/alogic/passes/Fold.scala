////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Fold expressions and statements
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.StatelessTreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.TypeAssigner
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec

final class Fold(implicit cc: CompilerContext) extends StatelessTreeTransformer {

  private val zero = BigInt(0)

  private def empty(stmts: List[Stmt]): Boolean = stmts forall {
    case _: StmtComment => true
    case _              => false
  }

  private def simplifyAssignmentSource(expr: Expr): Expr = expr.simplify match {
    // Drop pointless call to $unsigned/$signed
    case ExprCall(ExprSym(Symbol("$unsigned" | "$signed")), args) => args.head.expr
    case other                                                    => other
  }

  private var condLvl = 0

  override def enter(tree: Tree): Option[Tree] = tree match {
    // Simplify expressions
    case expr: Expr => Some(expr.simplify)

    // Simplify expressions in assignments specially
    case StmtAssign(lhs, rhs) =>
      Some {
        TypeAssigner {
          StmtAssign(lhs.simplifyLValue, simplifyAssignmentSource(rhs)) withLoc tree.loc
        }
      }
    case StmtDelayed(lhs, rhs) =>
      Some {
        TypeAssigner {
          StmtDelayed(lhs.simplifyLValue, simplifyAssignmentSource(rhs)) withLoc tree.loc
        }
      }
    case StmtOutcall(output, func, inputs) =>
      Some {
        TypeAssigner {
          StmtOutcall(
            output.simplifyLValue,
            func.simplify,
            inputs map simplifyAssignmentSource
          ) withLoc tree.loc
        }
      }
    case EntAssign(lhs, rhs) =>
      Some {
        TypeAssigner {
          EntAssign(lhs.simplifyLValue, simplifyAssignmentSource(rhs)) withLoc tree.loc
        }
      }
    // Fold 'if' with known conditions
    case StmtIf(cond, thenStmts, elseStmts) =>
      cond.value match {
        case Some(v) if v != 0 => Some(Thicket(walk(thenStmts)))
        case Some(v) if v == 0 => Some(Thicket(walk(elseStmts)))
        case None =>
          condLvl += 1
          None
      }

    // Fold 'wait' with known conditions
    case StmtWait(cond) =>
      cond.value match {
        case Some(v) if v != 0 => Some(Stump)
        case Some(v) if v == 0 && condLvl == 0 =>
          cc.error(tree, "Wait condition is always false")
          None
        case _ => None
      }

    // Fold 'case' with known conditions
    case StmtCase(expr, cases) =>
      expr.value match {
        case None => None
        case Some(v) =>
          @tailrec
          def loop(remaining: List[Case]): Option[Tree] = remaining match {
            case CaseRegular(cond, stmts) :: tail =>
              if (cond exists { _.value contains v }) {
                // A condition matches
                Some(Thicket(walk(stmts)))
              } else if (cond exists { _.value.isEmpty }) {
                // At least one condition has an unknown value, and therefore
                // might match, so we cannot fold further, but drop leading
                // eliminated cases
                Option.when(remaining ne cases) {
                  val retained = walk(remaining) map { _.asInstanceOf[Case] }
                  TypeAssigner(StmtCase(expr, retained) withLoc tree.loc)
                }
              } else {
                // None of the conditions match, proceed with the tail
                loop(tail)
              }
            // Default case always matches
            case CaseDefault(stmts) :: _ => Some(Thicket(walk(stmts)))
            // Reached the end of cases, nothing matched, so Stump
            case Nil => Some(Stump)
            //
            case _ => unreachable
          }
          loop(cases)
      }

    // Just to track we are in a conditional (it's easier here than in StmtCase above)
    case _: Case =>
      condLvl += 1
      None

    // Drop type definitions, references to these will be folded by expr.simplify
    case _: DeclType => Some(Stump)
    case _: DefnType => Some(Stump)

    // Drop unsized symbols, references to these will be folded by expr.simplify
    case Decl(symbol) if symbol.kind.underlying.isNum => Some(Stump)
    case Defn(symbol) if symbol.kind.underlying.isNum => Some(Stump)

    //
    case _ => None
  }

  private def alwaysFalseError(tree: Tree, msgOpt: Option[String]): tree.type = {
    val suffix = msgOpt match {
      case Some(msg) => ": " + msg;
      case None      => ""
    }
    cc.error(tree.loc, s"Assertion is always false$suffix")
    tree
  }

  override def transform(tree: Tree): Tree = tree match {
    // Remove all blocks (this will also remove empty blocks)
    case StmtBlock(stmts) => Thicket(stmts)

    // Simplify 'if' with empty branches
    case StmtIf(cond, ts, es) =>
      condLvl -= 1
      (empty(ts), empty(es)) match {
        case (true, true)  => Stump
        case (false, true) => TypeAssigner(StmtIf(cond, ts, Nil) withLoc tree.loc)
        case (true, false) => TypeAssigner(StmtIf((!cond).simplify, es, Nil) withLoc tree.loc)
        case _             => tree
      }

    // Remove empty 'case' statements
    case StmtCase(_, cases) if cases.iterator map { _.stmts } forall empty => Stump

    case _: Case =>
      condLvl -= 1
      tree

    // Drop empty processes
    case EntCombProcess(stmts) if empty(stmts)          => Stump
    case EntClockedProcess(_, _, stmts) if empty(stmts) => Stump

    // Fail on known false assertions
    case AssertionAssert(cond, msgOpt) if cond.value contains zero =>
      alwaysFalseError(tree, msgOpt)
    case AssertionAssume(cond, msgOpt) if cond.value contains zero =>
      alwaysFalseError(tree, msgOpt)

    //
    case _ => tree
  }

  override protected def finalCheck(tree: Tree): Unit = {
    assert(condLvl == 0, s"condLvl: $condLvl")
  }

}

object Fold extends PairTransformerPass {
  val name = "fold"
  def transform(decl: Decl, defn: Defn)(implicit cc: CompilerContext): (Tree, Tree) =
    (cc.fold(decl), cc.fold(defn))
}
