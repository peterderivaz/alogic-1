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
// TreeTransformer tests
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.AlogicTest
import com.argondesign.alogic.SourceTextConverters._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Messages.Warning
import com.argondesign.alogic.core.Types.TypeUInt
import com.argondesign.alogic.util.SequenceNumbers
import org.scalatest.flatspec.AnyFlatSpec

final class StatelessTreeTransformerSpec extends AnyFlatSpec with AlogicTest {

  implicit val cc: CompilerContext = new CompilerContext

  "A TreeTransformer" should "rewrite all nodes where it applies" in {
    val tree = """{
                 |  u1 foo;
                 |  u2 foo;
                 |}""".stripMargin.asTree[Stmt] rewrite new StatelessTreeTransformer {
      override val typed = false
      override def transform(tree: Tree): Tree = tree match {
        case _: Ident => Ident("bar", Nil) withLoc tree.loc
        case other    => other
      }
    }

    tree should matchPattern {
      case StmtBlock(
            List(
              StmtSplice(DescVar(Ident("bar", Nil), Nil, ExprType(TypeUInt(w1)), None)),
              StmtSplice(DescVar(Ident("bar", Nil), Nil, ExprType(TypeUInt(w2)), None))
            )
          ) if w1 == 1 && w2 == 2 =>
    }
  }

  it should "return the same tree instance if it is not rewritten" in {
    val oldTree = "{ a = b; bool c = a; }".asTree[Stmt]
    val newTree = oldTree rewrite new StatelessTreeTransformer {
      override val typed = false
      val sequenceNumbers = new SequenceNumbers
      override def transform(tree: Tree): Tree = tree tap { _ =>
        cc.warning(tree, s"Saw it ${sequenceNumbers.next}")
      }
    }

    newTree should be theSameInstanceAs oldTree

    cc.messages should have length 12
    cc.messages.zipWithIndex foreach {
      case (msg, idx) => msg should beThe[Warning](s"Saw it $idx")
    }

  }

}
