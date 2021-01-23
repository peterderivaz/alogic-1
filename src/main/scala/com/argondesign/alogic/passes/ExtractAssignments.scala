////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz
//
// DESCRIPTION:
//
// Generates an additional comb process for output wires that can be driven
// directly from registers.
// The intention is to avoid UNOPTFLAT warning from Verilator for
// a common case of a fence block with wired outputs.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.analysis.WrittenSymbols
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.TypeAssigner

import scala.collection.mutable

object ExtractAssignments extends PairTransformerPass {
  val name = "extract-assignments"

  override def skip(decl: Decl, defn: Defn)(implicit cc: CompilerContext): Boolean = defn match {
    case d: DefnEntity => d.combProcesses.isEmpty
    case _             => true
  }

  override def transform(decl: Decl, defn: Defn)(implicit cc: CompilerContext): (Tree, Tree) = {

    val entityDefn = defn.asInstanceOf[DefnEntity]

    // Identify output wires
    val isOutWire = mutable.Set[Symbol]()
    decl.decls.iterator foreach {
      case DeclOut(symbol, _, _, _) if !symbol.attr.flop.isSet => isOutWire += symbol
      case _                                                   =>
    }

    // Count of number of times each symbol is written
    val writeCounts = mutable.Map[Symbol, Int]().withDefaultValue(0)
    for {
      EntCombProcess(stmts) <- entityDefn.combProcesses
      stmt <- stmts
    } {
      stmt visit {
        case StmtAssign(lhs, _)     => WrittenSymbols(lhs) foreach { x => writeCounts(x) += 1 }
        case StmtOutcall(out, _, _) => WrittenSymbols(out) foreach { x => writeCounts(x) += 1 }
      }
    }

    // Go through statements tracking flow of simple assignments and stopping once a more
    // complicated statement is found
    val valueTracker = mutable.Map[Symbol, Symbol]()
    val forbidden = mutable.Set[Symbol]() // These are assigned with complex expressions
    // follow finds original source of this symbol by following links in valueTracer
    def follow(s: Symbol): Symbol = {
      if (valueTracker.contains(s)) follow(s) else s
    }
    for {
      EntCombProcess(stmts) <- entityDefn.combProcesses
    } {
      var continueSearch = true
      for { stmt <- stmts } {
        stmt match {
          case StmtComment(_) =>
          case StmtAssign(ExprSym(lhs), ExprSym(rhs))
              if continueSearch && !forbidden.contains(rhs) => {
            valueTracker(lhs) = follow(rhs)
          }
          case StmtAssign(lhs, rhs) if continueSearch =>
            WrittenSymbols(lhs) foreach { x => forbidden += x }
          case default =>
            continueSearch =
              false // Should be a better way of expressing this, really want "break" here
          // While would also work, but then not sure how to iterate over statements
          // Tried writing as a function and using return, but this seemed to make the compiler unhappy:
          //"return statement uses an exception to pass control to the caller of the enclosing named method searchStmts"
        }
      }
    }

    // Can only apply optimization for outputs written exactly once for which valueTracker contains a known value
    isOutWire.filter(x => (writeCounts(x) == 1) && (valueTracker contains x))

    if (isOutWire.isEmpty) {
      (decl, defn)
    } else {

      val newBody = entityDefn.body flatMap {
        case ent @ EntCombProcess(stmts) =>
          List(
            {
              val strippedStmts = stmts filter {
                case StmtAssign(ExprSym(lhs), ExprSym(_)) if isOutWire contains lhs => false
                case default                                                        => true
              }
              TypeAssigner(EntCombProcess(strippedStmts) withLoc ent.loc)
            }, {
              val extractedStmts: List[Stmt] =
                for { s <- isOutWire.toList } yield StmtAssign(
                  ExprSym(s),
                  ExprSym(follow(s))
                )
              TypeAssigner(EntCombProcess(extractedStmts) withLoc ent.loc)
            }
          )
        case other => Some(other)
      }

      val newDefn = TypeAssigner(entityDefn.copy(body = newBody) withLoc entityDefn.loc)

      (decl, newDefn)
    }
  }

}
