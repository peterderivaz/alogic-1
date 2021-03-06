////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 2017-2020 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// DESCRIPTION:
//  Statement type checking tests
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.frontend

import com.argondesign.alogic.AlogicTest
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Source
import org.scalatest.freespec.AnyFreeSpec

final class TypeCheckerStmtSpec extends AnyFreeSpec with AlogicTest {

  implicit private val cc: CompilerContext = new CompilerContext

  private val fe = new Frontend

  private def elaborate(text: String): Option[Desc] =
    fe.elaborate(Source("TyperCheckerExprSpec", text)) pipe {
      case Left(ms)      => ms foreach cc.addMessage; None
      case Right(result) => Some(result)
    }

  private def typeCheck(tree: Tree): Unit =
    fe.typeCheck(tree) match {
      case Complete(_) =>
      case Unknown(_)  => fail
      case Failure(ms) => ms foreach cc.addMessage
    }

  private def typeCheck(text: String): Tree =
    elaborate(text) tap { _ =>
      cc.messages foreach println
      cc.messages shouldBe empty
    } pipe { _.value } tap { tree =>
      typeCheck(tree)
    }

  "The Typer should type check statements" - {
    "blocks" - {
      for {
        (stmt, err) <- List(
          ("{ $display(); }", Nil),
          ("{ fence; }", Nil),
          ("{ $display(); fence; }", Nil),
          ("{ $display(); fence; $display(); fence; }", Nil),
          (
            "{ fence; $display();}",
            "Block must contain only combinational statements, or end with a control statement" :: Nil
          )
        )
      } {
        stmt in {
          typeCheck {
            s"""
               |fsm a {
               |  void main() {
               |    $stmt
               |    fence;
               |  }
               |}
               |""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }

    "fundamental flow control statements" - {
      for {
        (stmt, err) <- List(
          ("if (true) $display();", Nil),
          ("if (true) $display(); else $display();", Nil),
          ("if (true) fence;", Nil),
          ("if (true) fence; else fence;", Nil),
          (
            "if (true) fence; else $display();",
            "Either both or neither branches of 'if' statement must be control statements" :: Nil
          ),
          (
            "if (true) $display(); else fence;",
            "Either both or neither branches of 'if' statement must be control statements" :: Nil
          ),
          (
            "if (true) fence; else {}",
            "Either both or neither branches of 'if' statement must be control statements" :: Nil
          ),
          (
            "if (true) {} else fence;",
            "Either both or neither branches of 'if' statement must be control statements" :: Nil
          ),
          (
            "if (void) $display();",
            "Condition of 'if' statement is of non-packed type, a 1 bit value is expected" :: Nil
          ),
          ("case(1) { 1: $display(); }", Nil),
          ("case(1) { 1: fence; }", Nil),
          ("case(1) { default: $display(); }", Nil),
          ("case(1) { default: fence; }", Nil),
          ("case(1) { 1: $display(); 2: $display(); }", Nil),
          ("case(1) { 1: fence; 2: fence; }", Nil),
          ("case(1) { 1: $display(); default: $display(); }", Nil),
          ("case(1) { 1: fence; default: fence; }", Nil),
          (
            "case(1) { 1: $display(); 2: fence; }",
            "Either all or no cases of a 'case' statement must be control statements" :: Nil
          ),
          (
            "case(1) { 1: fence; 2: $display(); }",
            "Either all or no cases of a 'case' statement must be control statements" :: Nil
          ),
          (
            "case(1) { 1: $display(); default: fence; }",
            "Either all or no cases of a 'case' statement must be control statements" :: Nil
          ),
          (
            "case(1) { 1: fence; default: $display(); }",
            "Either all or no cases of a 'case' statement must be control statements" :: Nil
          ),
          (
            "case(void) { 1: $display(); }",
            "'case' expression is of neither numeric nor packed type" :: Nil
          ),
          ("loop { fence; }", Nil),
          ("loop { }", "Body of 'loop' must be a control statement" :: Nil),
          ("loop { $display(); }", "Body of 'loop' must end in a control statement" :: Nil),
          ("loop { fence; $display(); }", "Body of 'loop' must end in a control statement" :: Nil)
        )
      } {
        stmt in {
          typeCheck {
            s"""
               |fsm a {
               |  void main() {
               |    $stmt
               |    fence;
               |  }
               |}
               |""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }

    "assignments" - {
      for {
        (assignment, err) <- List(
          ("a = 2", Nil),
          ("a = 8'd2", Nil),
          (
            "a = bool",
            "Right hand side of assignment is of non-packed type, a 8 bit value is expected" :: Nil
          ),
          ("a += 8'd2", Nil),
          (
            "a += bool",
            "Right hand side of assignment is of non-packed type, a 8 bit value is expected" :: Nil
          ),
          (
            "a = 9'd2",
            "Right hand side of assignment yields 9 bits, a 8 bit value is expected" :: Nil
          ),
          (
            "a = 7'd2",
            "Right hand side of assignment yields 7 bits, a 8 bit value is expected" :: Nil
          )
        )
      } {
        assignment in {
          typeCheck {
            s"""
               |fsm x {
               |  void main() {
               |    i8 a;
               |    $assignment;
               |    fence;
               |  }
               |}""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }

    "postfix increment/decrement" - {
      for (op <- List("++", "--")) {
        for {
          (assignment, err) <- List(
            (s"a$op", Nil),
            (s"main$op", s"Target of postfix '$op' is of non-packed type" :: Nil)
          )
        } {
          assignment in {
            typeCheck {
              s"""
                 |fsm x {
                 |  void main() {
                 |    i8 a;
                 |    $assignment;
                 |    fence;
                 |  }
                 |}""".stripMargin
            }
            checkSingleError(err)
          }
        }
      }
    }

    "assignments to illegal lhs" - {
      val iPortErr = "Input port cannot be modified" :: Nil
      val oPortErr = "Output port with flow control can only be modified using .write()" :: Nil
      val constErr = "Constant cannot be modified" :: Nil
      val memoryErr = "Memory can only be modified using .write()" :: Nil
      val valErr = "'const' qualified variable cannot be modified" :: Nil

      for (op <- List("=", "+=")) {
        for {
          (assignment, err) <- List(
            (s"a $op 8'd0", iPortErr),
            (s"b $op 8'd0", Nil),
            (s"c $op 8'd0", iPortErr),
            (s"d $op 8'd0", oPortErr),
            (s"e $op 8'd0", iPortErr),
            (s"f $op 8'd0", oPortErr),
            (s"h $op 8'd0", constErr),
            (s"j $op 8'b0", valErr),
            (s"a[0] $op 1'b0", iPortErr),
            (s"b[0] $op 1'b0", Nil),
            (s"c[0] $op 1'b0", iPortErr),
            (s"d[0] $op 1'b0", oPortErr),
            (s"e[0] $op 1'b0", iPortErr),
            (s"f[0] $op 1'b0", oPortErr),
            (s"h[0] $op 1'b0", constErr),
            (s"i[0] $op 4'b0", memoryErr),
            (s"j[0] $op 1'b0", valErr),
            (s"a[1:0] $op 2'b0", iPortErr),
            (s"b[1:0] $op 2'b0", Nil),
            (s"c[1:0] $op 2'b0", iPortErr),
            (s"d[1:0] $op 2'b0", oPortErr),
            (s"e[1:0] $op 2'b0", iPortErr),
            (s"f[1:0] $op 2'b0", oPortErr),
            (s"h[1:0] $op 2'b0", constErr),
            (s"i[0][1:0] $op 2'b0", memoryErr),
            (s"j[1:0] $op 2'b0", valErr),
            (s"{b[1], a[0]} $op 2'b0", iPortErr),
            (s"{b[1], b[0]} $op 2'b0", Nil),
            (s"{b[1], c[0]} $op 2'b0", iPortErr),
            (s"{b[1], d[0]} $op 2'b0", oPortErr),
            (s"{b[1], e[0]} $op 2'b0", iPortErr),
            (s"{b[1], f[0]} $op 2'b0", oPortErr),
            (s"{b[1], h[0]} $op 2'b0", constErr),
            (s"{b[1], i[0]} $op 9'b0", memoryErr),
            (s"{b[1], j[0]} $op 2'b0", valErr)
          )
        } {
          assignment in {
            typeCheck {
              s"""
                 |fsm x {
                 |  in i8 a;
                 |  out i8 b;
                 |  in sync i8 c;
                 |  out sync i8 d;
                 |  in sync ready i8 e;
                 |  out sync ready i8 f;
                 |  const i8 h = 8'd2;
                 |  u8 i[4];
                 |
                 |  void main() {
                 |    const i8 j = 8'd0;
                 |    $assignment;
                 |    fence;
                 |  }
                 |}""".stripMargin
            }
            checkSingleError(err)
          }
        }
      }
    }

    "postfix increment/decrement of illegal target" - {
      val iPortErr = "Input port cannot be modified" :: Nil
      val oPortErr = "Output port with flow control can only be modified using .write()" :: Nil
      val constErr = "Constant cannot be modified" :: Nil
      val memoryErr = "Memory can only be modified using .write()" :: Nil
      val valErr = "'const' qualified variable cannot be modified" :: Nil

      for (op <- List("++", "--")) {
        for {
          (assignment, err) <- List(
            (s"a$op", iPortErr),
            (s"b$op", Nil),
            (s"c$op", iPortErr),
            (s"d$op", oPortErr),
            (s"e$op", iPortErr),
            (s"f$op", oPortErr),
            (s"h$op", constErr),
            (s"j$op", valErr),
            (s"a[0]$op", iPortErr),
            (s"b[0]$op", Nil),
            (s"c[0]$op", iPortErr),
            (s"d[0]$op", oPortErr),
            (s"e[0]$op", iPortErr),
            (s"f[0]$op", oPortErr),
            (s"h[0]$op", constErr),
            (s"i[0]$op", memoryErr),
            (s"j[0]$op", valErr),
            (s"a[1:0]$op", iPortErr),
            (s"b[1:0]$op", Nil),
            (s"c[1:0]$op", iPortErr),
            (s"d[1:0]$op", oPortErr),
            (s"e[1:0]$op", iPortErr),
            (s"f[1:0]$op", oPortErr),
            (s"h[1:0]$op", constErr),
            (s"i[0][1:0]$op", memoryErr),
            (s"j[1:0]$op", valErr),
            (s"{b[1], a[0]}$op", iPortErr),
            (s"{b[1], b[0]}$op", Nil),
            (s"{b[1], c[0]}$op", iPortErr),
            (s"{b[1], d[0]}$op", oPortErr),
            (s"{b[1], e[0]}$op", iPortErr),
            (s"{b[1], f[0]}$op", oPortErr),
            (s"{b[1], h[0]}$op", constErr),
            (s"{b[1], i[0]}$op", memoryErr),
            (s"{b[1], j[0]}$op", valErr)
          )
        } {
          assignment in {
            typeCheck {
              s"""
                 |fsm x {
                 |  in i8 a;
                 |  out i8 b;
                 |  in sync i8 c;
                 |  out sync i8 d;
                 |  in sync ready i8 e;
                 |  out sync ready i8 f;
                 |  const i8 h = 8'd2;
                 |  u8 i[4];
                 |
                 |  void main() {
                 |    const i8 j = 8'd0;
                 |    $assignment;
                 |    fence;
                 |  }
                 |}""".stripMargin
            }
            checkSingleError(err)
          }
        }
      }
    }

    "error for pure expressions in statement position" - {
      val error = "A pure expression in statement position does nothing" :: Nil
      for {
        (text, err) <- List(
          ("1 * 2", error),
          ("-(1s)", error),
          ("@unknownu(1)", Nil),
          ("1 + @unknownu(1)", Nil),
          ("1 + $clog2(2)", error),
          ("$display(\"\")", Nil)
        )
      } {
        text in {
          typeCheck {
            s"""
               |struct s {
               |  void function() {
               |   $text;
               |  }
               |}""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }

    "assertion conditions" - {
      for (kw <- List("assert", "static assert")) {
        for {
          (cond, err) <- List(
            ("true", Nil),
            ("8'd1", Nil),
            ("1", Nil),
            ("main", s"Condition of '$kw' is of neither numeric nor packed type" :: Nil),
            ("bool", s"Condition of '$kw' is of neither numeric nor packed type" :: Nil)
          )
        } {
          s"$kw $cond" in {
            val f: Function1[String, Any] = if (kw startsWith "static") elaborate else typeCheck
            f {
              s"""
                 |fsm x {
                 |  void main() {
                 |    $kw $cond;
                 |    fence;
                 |  }
                 |}""".stripMargin
            }
            checkSingleError(err)
          }
        }
      }
    }

    "return" - {

      "packed" - {
        for {
          (kind, value, err) <- List(
            ("u8", "2", Nil),
            ("u8", "8'd2", Nil),
            ("u8", "bool", "Return value is of non-packed type, a 8 bit value is expected" :: Nil),
            ("u8", "9'd2", "Return value yields 9 bits, a 8 bit value is expected" :: Nil),
            ("u8", "7'd2", "Return value yields 7 bits, a 8 bit value is expected" :: Nil),
            ("u8", "", "non-void function 'f' must return a value" :: Nil),
            ("void", "", Nil),
            ("void", "8'd2", "void function 'f' cannot return a value" :: Nil),
            ("void", "bool", "void function 'f' cannot return a value" :: Nil)
          )
        } {
          s"$kind return $value" in {
            typeCheck {
              s"""
                 |struct s {
                 |  $kind f() {
                 |    return $value;
                 |  }
                 |}""".stripMargin
            }
            checkSingleError(err)
          }
        }
      }

      "outside function" in {
        elaborate {
          s"""
             |fsm a {
             |  fence {
             |    return;
             |  }
             |}""".stripMargin
        }
        checkSingleError("'return' statement not inside function" :: Nil)
      }
    }

    "error for conditionals with packed condition wider than 1 bit" - {
      for {
        (cond, err) <- List(
          ("a", Nil),
          ("b", Nil),
          ("c", "Condition of 'if' statement yields 2 bits, a 1 bit value is expected" :: Nil),
          ("d", "Condition of 'if' statement yields 8 bits, a 1 bit value is expected" :: Nil),
          ("c[0]", Nil),
          ("d[1]", Nil),
          (
            "0",
            "Condition of 'if' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          (
            "1",
            "Condition of 'if' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          (
            "5",
            "Condition of 'if' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          ("1'd0", Nil),
          ("1'd1", Nil),
          ("2'd0", "Condition of 'if' statement yields 2 bits, a 1 bit value is expected" :: Nil),
          ("9'd1", "Condition of 'if' statement yields 9 bits, a 1 bit value is expected" :: Nil)
        )
      } {
        cond in {
          typeCheck {
            s"""fsm  f {
               |  u1 a;
               |  i1 b;
               |  u2 c;
               |  i8 d;
               |
               |  void main() {
               |     if ($cond) {}
               |     fence;
               |  }
               |}""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }

    "wait" - {
      for {
        (cond, err) <- List(
          ("a", Nil),
          ("b", Nil),
          ("c", "Condition of 'wait' statement yields 2 bits, a 1 bit value is expected" :: Nil),
          ("d", "Condition of 'wait' statement yields 8 bits, a 1 bit value is expected" :: Nil),
          ("c[0]", Nil),
          ("d[1]", Nil),
          (
            "0",
            "Condition of 'wait' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          (
            "1",
            "Condition of 'wait' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          (
            "5",
            "Condition of 'wait' statement yields an unsized value, a 1 bit value is expected" :: Nil
          ),
          ("1'd0", Nil),
          ("1'd1", Nil),
          ("2'd0", "Condition of 'wait' statement yields 2 bits, a 1 bit value is expected" :: Nil),
          ("9'd1", "Condition of 'wait' statement yields 9 bits, a 1 bit value is expected" :: Nil),
          (
            "bool",
            "Condition of 'wait' statement is of non-packed type, a 1 bit value is expected" :: Nil
          )
        )
      } {
        cond in {
          typeCheck {
            s"""fsm  f {
               |  u1 a;
               |  i1 b;
               |  u2 c;
               |  i8 d;
               |
               |  void main() {
               |     wait $cond;
               |     fence;
               |  }
               |}""".stripMargin
          }
          checkSingleError(err)
        }
      }
    }
  }
}
