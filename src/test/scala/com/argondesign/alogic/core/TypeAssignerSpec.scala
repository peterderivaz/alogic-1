////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 2017-2020 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// DESCRIPTION:
//  TypeAssigner tests
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import com.argondesign.alogic.AlogicTest
import com.argondesign.alogic.SourceTextConverters.String2Repr
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.FlowControlTypes._
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.frontend.Frontend
import org.scalatest.freespec.AnyFreeSpec

final class TypeAssignerSpec extends AnyFreeSpec with AlogicTest {

  implicit private val cc: CompilerContext = new CompilerContext

  private val fe = new Frontend

  private def elaborate(text: String): Tree =
    fe.elaborate(Source("TypeAssignerSpec", text)) pipe {
      case Left(ms)      => ms foreach cc.addMessage; None
      case Right(result) => Some(result)
    } tap { _ =>
      cc.messages foreach println
      cc.messages shouldBe empty
    } pipe {
      _.value
    }

  // Apply types of all children
  private def assignChildren(tree: Tree): Unit = tree.postOrderIterator foreach {
    case node @ ExprSym(symbol) =>
      fe.typeOf(symbol, Loc.synthetic)
      if (!node.hasTpe && (node ne tree)) TypeAssigner(node)
    case node if node eq tree =>
    case node if node.hasTpe  =>
    case node                 => TypeAssigner(node)
  }

  "The TypeAssigner should assign correct types to" - {
    "expressions" - {
      "references" - {
        for {
          (decl, kind) <- List[(String, PartialFunction[Any, Unit])](
            // format: off
            ("bool a;", { case TypeUInt(w) if w == 1 => }),
            ("u8 a;", { case TypeUInt(w) if w == 8 => }),
            ("i1 a;", { case TypeSInt(w) if w == 1 => }),
            ("i8 a;", { case TypeSInt(w) if w == 8 => }),
            ("s a;", { case TypeRecord(s, List(b, c)) if s.name == "s" && b.name == "b" && c.name == "c" => }),
            ("t a;", { case TypeUInt(w) if w == 4 => }),
            ("u8[2] a;", { case TypeVector(TypeUInt(w1), w2) if w1 == 8 && w2 == 2 => }),
            ("u8 a[2];", { case TypeArray(TypeUInt(w1), w2) if w1 == 8 && w2 == 2 => }),
            ("const u8 a = 8'd2;", { case TypeUInt(w) if w == 8 => }),
            ("in u8 a;", { case TypeIn(TypeUInt(w), FlowControlTypeNone) if w == 8 => }),
            ("out u8 a;", { case TypeOut(TypeUInt(w), FlowControlTypeNone, StorageTypeDefault) if w == 8 => }),
            ("void a() {}", { case TypeCtrlFunc(_, TypeVoid, Nil) => }),
            ("import void a();", { case TypeXenoFunc(_, TypeVoid, Nil) => }),
            ("import bool a();", { case TypeXenoFunc(_, TypeUInt(r), Nil) if r == 1 => }),
            ("import u3 a(i2 i);", { case TypeXenoFunc(_, TypeUInt(r), TypeSInt(a) :: Nil) if r == 3 && a == 2 => })
            // format: on
          )
        } {
          decl in {
            elaborate {
              s"""
                 |typedef u4 t;
                 |
                 |struct s { bool b; i8 c; }
                 |
                 |fsm thing {
                 |  $decl
                 |  fence { a; }
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(expr: ExprSym) => expr
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ should matchPattern(kind)
            }
            cc.messages shouldBe empty
          }
        }

        for {
          (decl, kind) <- List[(String, PartialFunction[Any, Unit])](
            // format: off
            ("pipeline u8 a;", { case TypeUInt(w) if w == 8 => })
            // format: on
          )
        } {
          decl in {
            elaborate {
              s"""
                 |typedef u4 t;
                 |
                 |struct s { bool b; i8 c; }
                 |
                 |network n {
                 |  $decl
                 |  fsm thing {
                 |    fence { a; }
                 |  }
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(expr: ExprSym) => expr
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ should matchPattern(kind)
            }
            cc.messages shouldBe empty
          }
        }

        for {
          (text, kind) <- List[(String, PartialFunction[Any, Unit])](
            // format: off
            ("bool", { case TypeUInt(w) if w == 1 => }),
            ("u2", { case TypeUInt(w) if w == 2 => }),
            ("u3[6]", { case TypeVector(TypeUInt(w1), w2) if w1 == 3 && w2 == 6 => }),
            ("i2", { case TypeSInt(w) if w == 2 => }),
            ("i3[6]", { case TypeVector(TypeSInt(w1), w2) if w1 == 3 && w2 == 6 => }),
            ("void", { case TypeVoid => }),
            ("t /* typedef */", { case TypeUInt(w) if w == 4 => }),
            ("s /* struct */", { case TypeRecord(s, List(b, c)) if s.name == "s" && b.name == "b" && c.name == "c" => })
            // format: on
          )
        } {
          text in {
            elaborate {
              s"""
                 |typedef u4 t;
                 |
                 |struct s { bool b; i8 c; }
                 |
                 |fsm thing {
                 |  fence { $text; }
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              case TypeType(k) => k should matchPattern(kind)
              case _           => fail("Expression must have TypeType")
            }
            cc.messages shouldBe empty
          }
        }
      }

      "unary operators" - {
        for {
          (src, kind) <- List(
            ("+(32'd1)", TypeUInt(32)),
            ("-(32'd1)", TypeUInt(32)),
            ("~(32'd1)", TypeUInt(32)),
            ("!(32'd1)", TypeUInt(1)),
            ("&(32'd1)", TypeUInt(1)),
            ("|(32'd1)", TypeUInt(1)),
            ("^(32'd1)", TypeUInt(1)),
            ("+(32'sd1)", TypeSInt(32)),
            ("-(32'sd1)", TypeSInt(32)),
            ("~(32'sd1)", TypeSInt(32)),
            ("!(32'sd1)", TypeUInt(1)),
            ("&(32'sd1)", TypeUInt(1)),
            ("|(32'sd1)", TypeUInt(1)),
            ("^(32'sd1)", TypeUInt(1)),
            // unsized
            ("+(1)", TypeNum(false)),
            ("-(1)", TypeNum(false)),
            ("~(1)", TypeNum(false)),
            ("!(1)", TypeUInt(1)),
            ("+(1s)", TypeNum(true)),
            ("-(1s)", TypeNum(true)),
            ("~(1s)", TypeNum(true)),
            ("!(1s)", TypeUInt(1))
          )
        } {
          src in {
            elaborate {
              s"""
                 |void f() {
                 |  u32 a = $src;
                 |}""".stripMargin
            } getFirst {
              case e: ExprUnary => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "binary operators" - {
        for {
          (src, kind) <- List(
            //
            // sized - sized
            //
            // unsigned - unsigned
            ("32'd1 *   32'd1", TypeUInt(32)),
            ("32'd1 /   32'd1", TypeUInt(32)),
            ("32'd1 %   32'd1", TypeUInt(32)),
            ("32'd1 +   32'd1", TypeUInt(32)),
            ("32'd1 -   32'd1", TypeUInt(32)),
            ("32'd1 <<  32'd1", TypeUInt(32)),
            ("32'd1 >>  32'd1", TypeUInt(32)),
            ("32'd1 >>> 32'd1", TypeUInt(32)),
            ("32'd1 <<< 32'd1", TypeUInt(32)),
            ("32'd1 >   32'd1", TypeUInt(1)),
            ("32'd1 >=  32'd1", TypeUInt(1)),
            ("32'd1 <   32'd1", TypeUInt(1)),
            ("32'd1 <=  32'd1", TypeUInt(1)),
            ("32'd1 ==  32'd1", TypeUInt(1)),
            ("32'd1 !=  32'd1", TypeUInt(1)),
            ("32'd1 &   32'd1", TypeUInt(32)),
            ("32'd1 ^   32'd1", TypeUInt(32)),
            ("32'd1 |   32'd1", TypeUInt(32)),
            ("32'd1 &&  32'd1", TypeUInt(1)),
            ("32'd1 ||  32'd1", TypeUInt(1)),
            // signed - unsigned
            ("32'd1 *   32'sd1", TypeUInt(32)),
            ("32'd1 /   32'sd1", TypeUInt(32)),
            ("32'd1 %   32'sd1", TypeUInt(32)),
            ("32'd1 +   32'sd1", TypeUInt(32)),
            ("32'd1 -   32'sd1", TypeUInt(32)),
            ("32'd1 <<  32'sd1", TypeUInt(32)),
            ("32'd1 >>  32'sd1", TypeUInt(32)),
            ("32'd1 >>> 32'sd1", TypeUInt(32)),
            ("32'd1 <<< 32'sd1", TypeUInt(32)),
            ("32'd1 >   32'sd1", TypeUInt(1)),
            ("32'd1 >=  32'sd1", TypeUInt(1)),
            ("32'd1 <   32'sd1", TypeUInt(1)),
            ("32'd1 <=  32'sd1", TypeUInt(1)),
            ("32'd1 ==  32'sd1", TypeUInt(1)),
            ("32'd1 !=  32'sd1", TypeUInt(1)),
            ("32'd1 &   32'sd1", TypeUInt(32)),
            ("32'd1 ^   32'sd1", TypeUInt(32)),
            ("32'd1 |   32'sd1", TypeUInt(32)),
            ("32'd1 &&  32'sd1", TypeUInt(1)),
            ("32'd1 ||  32'sd1", TypeUInt(1)),
            // signed - unsigned
            ("32'sd1 *   32'd1", TypeUInt(32)),
            ("32'sd1 /   32'd1", TypeUInt(32)),
            ("32'sd1 %   32'd1", TypeUInt(32)),
            ("32'sd1 +   32'd1", TypeUInt(32)),
            ("32'sd1 -   32'd1", TypeUInt(32)),
            ("32'sd1 <<  32'd1", TypeSInt(32)),
            ("32'sd1 >>  32'd1", TypeSInt(32)),
            ("32'sd1 >>> 32'd1", TypeSInt(32)),
            ("32'sd1 <<< 32'd1", TypeSInt(32)),
            ("32'sd1 >   32'd1", TypeUInt(1)),
            ("32'sd1 >=  32'd1", TypeUInt(1)),
            ("32'sd1 <   32'd1", TypeUInt(1)),
            ("32'sd1 <=  32'd1", TypeUInt(1)),
            ("32'sd1 ==  32'd1", TypeUInt(1)),
            ("32'sd1 !=  32'd1", TypeUInt(1)),
            ("32'sd1 &   32'd1", TypeUInt(32)),
            ("32'sd1 ^   32'd1", TypeUInt(32)),
            ("32'sd1 |   32'd1", TypeUInt(32)),
            ("32'sd1 &&  32'd1", TypeUInt(1)),
            ("32'sd1 ||  32'd1", TypeUInt(1)),
            // signed - signed
            ("32'sd1 *   32'sd1", TypeSInt(32)),
            ("32'sd1 /   32'sd1", TypeSInt(32)),
            ("32'sd1 %   32'sd1", TypeSInt(32)),
            ("32'sd1 +   32'sd1", TypeSInt(32)),
            ("32'sd1 -   32'sd1", TypeSInt(32)),
            ("32'sd1 <<  32'sd1", TypeSInt(32)),
            ("32'sd1 >>  32'sd1", TypeSInt(32)),
            ("32'sd1 >>> 32'sd1", TypeSInt(32)),
            ("32'sd1 <<< 32'sd1", TypeSInt(32)),
            ("32'sd1 >   32'sd1", TypeUInt(1)),
            ("32'sd1 >=  32'sd1", TypeUInt(1)),
            ("32'sd1 <   32'sd1", TypeUInt(1)),
            ("32'sd1 <=  32'sd1", TypeUInt(1)),
            ("32'sd1 ==  32'sd1", TypeUInt(1)),
            ("32'sd1 !=  32'sd1", TypeUInt(1)),
            ("32'sd1 &   32'sd1", TypeSInt(32)),
            ("32'sd1 ^   32'sd1", TypeSInt(32)),
            ("32'sd1 |   32'sd1", TypeSInt(32)),
            ("32'sd1 &&  32'sd1", TypeUInt(1)),
            ("32'sd1 ||  32'sd1", TypeUInt(1)),
            //
            // sized - unsized
            //
            // unsigned - unsigned
            ("32'd1 *   1", TypeUInt(32)),
            ("32'd1 /   1", TypeUInt(32)),
            ("32'd1 %   1", TypeUInt(32)),
            ("32'd1 +   1", TypeUInt(32)),
            ("32'd1 -   1", TypeUInt(32)),
            ("32'd1 <<  1", TypeUInt(32)),
            ("32'd1 >>  1", TypeUInt(32)),
            ("32'd1 >>> 1", TypeUInt(32)),
            ("32'd1 <<< 1", TypeUInt(32)),
            ("32'd1 >   1", TypeUInt(1)),
            ("32'd1 >=  1", TypeUInt(1)),
            ("32'd1 <   1", TypeUInt(1)),
            ("32'd1 <=  1", TypeUInt(1)),
            ("32'd1 ==  1", TypeUInt(1)),
            ("32'd1 !=  1", TypeUInt(1)),
            ("32'd1 &   1", TypeUInt(32)),
            ("32'd1 ^   1", TypeUInt(32)),
            ("32'd1 |   1", TypeUInt(32)),
            ("32'd1 &&  1", TypeUInt(1)),
            ("32'd1 ||  1", TypeUInt(1)),
            // unsigned - signed
            ("32'd1 *   1s", TypeUInt(32)),
            ("32'd1 /   1s", TypeUInt(32)),
            ("32'd1 %   1s", TypeUInt(32)),
            ("32'd1 +   1s", TypeUInt(32)),
            ("32'd1 -   1s", TypeUInt(32)),
            ("32'd1 <<  1s", TypeUInt(32)),
            ("32'd1 >>  1s", TypeUInt(32)),
            ("32'd1 >>> 1s", TypeUInt(32)),
            ("32'd1 <<< 1s", TypeUInt(32)),
            ("32'd1 >   1s", TypeUInt(1)),
            ("32'd1 >=  1s", TypeUInt(1)),
            ("32'd1 <   1s", TypeUInt(1)),
            ("32'd1 <=  1s", TypeUInt(1)),
            ("32'd1 ==  1s", TypeUInt(1)),
            ("32'd1 !=  1s", TypeUInt(1)),
            ("32'd1 &   1s", TypeUInt(32)),
            ("32'd1 ^   1s", TypeUInt(32)),
            ("32'd1 |   1s", TypeUInt(32)),
            ("32'd1 &&  1s", TypeUInt(1)),
            ("32'd1 ||  1s", TypeUInt(1)),
            // signed - unsigned
            ("32'sd1 *   1", TypeUInt(32)),
            ("32'sd1 /   1", TypeUInt(32)),
            ("32'sd1 %   1", TypeUInt(32)),
            ("32'sd1 +   1", TypeUInt(32)),
            ("32'sd1 -   1", TypeUInt(32)),
            ("32'sd1 <<  1", TypeSInt(32)),
            ("32'sd1 >>  1", TypeSInt(32)),
            ("32'sd1 >>> 1", TypeSInt(32)),
            ("32'sd1 <<< 1", TypeSInt(32)),
            ("32'sd1 >   1", TypeUInt(1)),
            ("32'sd1 >=  1", TypeUInt(1)),
            ("32'sd1 <   1", TypeUInt(1)),
            ("32'sd1 <=  1", TypeUInt(1)),
            ("32'sd1 ==  1", TypeUInt(1)),
            ("32'sd1 !=  1", TypeUInt(1)),
            ("32'sd1 &   1", TypeUInt(32)),
            ("32'sd1 ^   1", TypeUInt(32)),
            ("32'sd1 |   1", TypeUInt(32)),
            ("32'sd1 &&  1", TypeUInt(1)),
            ("32'sd1 ||  1", TypeUInt(1)),
            // signed - signed
            ("32'sd1 *   1s", TypeSInt(32)),
            ("32'sd1 /   1s", TypeSInt(32)),
            ("32'sd1 %   1s", TypeSInt(32)),
            ("32'sd1 +   1s", TypeSInt(32)),
            ("32'sd1 -   1s", TypeSInt(32)),
            ("32'sd1 <<  1s", TypeSInt(32)),
            ("32'sd1 >>  1s", TypeSInt(32)),
            ("32'sd1 >>> 1s", TypeSInt(32)),
            ("32'sd1 <<< 1s", TypeSInt(32)),
            ("32'sd1 >   1s", TypeUInt(1)),
            ("32'sd1 >=  1s", TypeUInt(1)),
            ("32'sd1 <   1s", TypeUInt(1)),
            ("32'sd1 <=  1s", TypeUInt(1)),
            ("32'sd1 ==  1s", TypeUInt(1)),
            ("32'sd1 !=  1s", TypeUInt(1)),
            ("32'sd1 &   1s", TypeSInt(32)),
            ("32'sd1 ^   1s", TypeSInt(32)),
            ("32'sd1 |   1s", TypeSInt(32)),
            ("32'sd1 &&  1s", TypeUInt(1)),
            ("32'sd1 ||  1s", TypeUInt(1)),
            //
            // unsized - sized
            //
            // unsigned - unsigned
            ("1 *   32'd1", TypeUInt(32)),
            ("1 /   32'd1", TypeUInt(32)),
            ("1 %   32'd1", TypeUInt(32)),
            ("1 +   32'd1", TypeUInt(32)),
            ("1 -   32'd1", TypeUInt(32)),
            ("1 <<  32'd1", TypeNum(false)),
            ("1 >>  32'd1", TypeNum(false)),
            ("1 >>> 32'd1", TypeNum(false)),
            ("1 <<< 32'd1", TypeNum(false)),
            ("1 >   32'd1", TypeUInt(1)),
            ("1 >=  32'd1", TypeUInt(1)),
            ("1 <   32'd1", TypeUInt(1)),
            ("1 <=  32'd1", TypeUInt(1)),
            ("1 ==  32'd1", TypeUInt(1)),
            ("1 !=  32'd1", TypeUInt(1)),
            ("1 &   32'd1", TypeUInt(32)),
            ("1 ^   32'd1", TypeUInt(32)),
            ("1 |   32'd1", TypeUInt(32)),
            ("1 &&  32'd1", TypeUInt(1)),
            ("1 ||  32'd1", TypeUInt(1)),
            // signed - unsigned
            ("1 *   32'sd1", TypeUInt(32)),
            ("1 /   32'sd1", TypeUInt(32)),
            ("1 %   32'sd1", TypeUInt(32)),
            ("1 +   32'sd1", TypeUInt(32)),
            ("1 -   32'sd1", TypeUInt(32)),
            ("1 <<  32'sd1", TypeNum(false)),
            ("1 >>  32'sd1", TypeNum(false)),
            ("1 >>> 32'sd1", TypeNum(false)),
            ("1 <<< 32'sd1", TypeNum(false)),
            ("1 >   32'sd1", TypeUInt(1)),
            ("1 >=  32'sd1", TypeUInt(1)),
            ("1 <   32'sd1", TypeUInt(1)),
            ("1 <=  32'sd1", TypeUInt(1)),
            ("1 ==  32'sd1", TypeUInt(1)),
            ("1 !=  32'sd1", TypeUInt(1)),
            ("1 &   32'sd1", TypeUInt(32)),
            ("1 ^   32'sd1", TypeUInt(32)),
            ("1 |   32'sd1", TypeUInt(32)),
            ("1 &&  32'sd1", TypeUInt(1)),
            ("1 ||  32'sd1", TypeUInt(1)),
            // signed - unsigned
            ("1s *   32'd1", TypeUInt(32)),
            ("1s /   32'd1", TypeUInt(32)),
            ("1s %   32'd1", TypeUInt(32)),
            ("1s +   32'd1", TypeUInt(32)),
            ("1s -   32'd1", TypeUInt(32)),
            ("1s <<  32'd1", TypeNum(true)),
            ("1s >>  32'd1", TypeNum(true)),
            ("1s >>> 32'd1", TypeNum(true)),
            ("1s <<< 32'd1", TypeNum(true)),
            ("1s >   32'd1", TypeUInt(1)),
            ("1s >=  32'd1", TypeUInt(1)),
            ("1s <   32'd1", TypeUInt(1)),
            ("1s <=  32'd1", TypeUInt(1)),
            ("1s ==  32'd1", TypeUInt(1)),
            ("1s !=  32'd1", TypeUInt(1)),
            ("1s &   32'd1", TypeUInt(32)),
            ("1s ^   32'd1", TypeUInt(32)),
            ("1s |   32'd1", TypeUInt(32)),
            ("1s &&  32'd1", TypeUInt(1)),
            ("1s ||  32'd1", TypeUInt(1)),
            // signed - signed
            ("1s *   32'sd1", TypeSInt(32)),
            ("1s /   32'sd1", TypeSInt(32)),
            ("1s %   32'sd1", TypeSInt(32)),
            ("1s +   32'sd1", TypeSInt(32)),
            ("1s -   32'sd1", TypeSInt(32)),
            ("1s <<  32'sd1", TypeNum(true)),
            ("1s >>  32'sd1", TypeNum(true)),
            ("1s >>> 32'sd1", TypeNum(true)),
            ("1s <<< 32'sd1", TypeNum(true)),
            ("1s >   32'sd1", TypeUInt(1)),
            ("1s >=  32'sd1", TypeUInt(1)),
            ("1s <   32'sd1", TypeUInt(1)),
            ("1s <=  32'sd1", TypeUInt(1)),
            ("1s ==  32'sd1", TypeUInt(1)),
            ("1s !=  32'sd1", TypeUInt(1)),
            ("1s &   32'sd1", TypeSInt(32)),
            ("1s ^   32'sd1", TypeSInt(32)),
            ("1s |   32'sd1", TypeSInt(32)),
            ("1s &&  32'sd1", TypeUInt(1)),
            ("1s ||  32'sd1", TypeUInt(1)),
            //
            // unsized - unsized
            //
            // unsigned - unsigned
            ("1 *   1", TypeNum(false)),
            ("1 /   1", TypeNum(false)),
            ("1 %   1", TypeNum(false)),
            ("1 +   1", TypeNum(false)),
            ("1 -   1", TypeNum(false)),
            ("1 <<  1", TypeNum(false)),
            ("1 >>  1", TypeNum(false)),
            ("1 >>> 1", TypeNum(false)),
            ("1 <<< 1", TypeNum(false)),
            ("1 >   1", TypeUInt(1)),
            ("1 >=  1", TypeUInt(1)),
            ("1 <   1", TypeUInt(1)),
            ("1 <=  1", TypeUInt(1)),
            ("1 ==  1", TypeUInt(1)),
            ("1 !=  1", TypeUInt(1)),
            ("1 &   1", TypeNum(false)),
            ("1 ^   1", TypeNum(false)),
            ("1 |   1", TypeNum(false)),
            ("1 &&  1", TypeUInt(1)),
            ("1 ||  1", TypeUInt(1)),
            // unsigned - signed
            ("1 *   1s", TypeNum(false)),
            ("1 /   1s", TypeNum(false)),
            ("1 %   1s", TypeNum(false)),
            ("1 +   1s", TypeNum(false)),
            ("1 -   1s", TypeNum(false)),
            ("1 <<  1s", TypeNum(false)),
            ("1 >>  1s", TypeNum(false)),
            ("1 >>> 1s", TypeNum(false)),
            ("1 <<< 1s", TypeNum(false)),
            ("1 >   1s", TypeUInt(1)),
            ("1 >=  1s", TypeUInt(1)),
            ("1 <   1s", TypeUInt(1)),
            ("1 <=  1s", TypeUInt(1)),
            ("1 ==  1s", TypeUInt(1)),
            ("1 !=  1s", TypeUInt(1)),
            ("1 &   1s", TypeNum(false)),
            ("1 ^   1s", TypeNum(false)),
            ("1 |   1s", TypeNum(false)),
            ("1 &&  1s", TypeUInt(1)),
            ("1 ||  1s", TypeUInt(1)),
            // signed - unsigned
            ("1s *   1", TypeNum(false)),
            ("1s /   1", TypeNum(false)),
            ("1s %   1", TypeNum(false)),
            ("1s +   1", TypeNum(false)),
            ("1s -   1", TypeNum(false)),
            ("1s <<  1", TypeNum(true)),
            ("1s >>  1", TypeNum(true)),
            ("1s >>> 1", TypeNum(true)),
            ("1s <<< 1", TypeNum(true)),
            ("1s >   1", TypeUInt(1)),
            ("1s >=  1", TypeUInt(1)),
            ("1s <   1", TypeUInt(1)),
            ("1s <=  1", TypeUInt(1)),
            ("1s ==  1", TypeUInt(1)),
            ("1s !=  1", TypeUInt(1)),
            ("1s &   1", TypeNum(false)),
            ("1s ^   1", TypeNum(false)),
            ("1s |   1", TypeNum(false)),
            ("1s &&  1", TypeUInt(1)),
            ("1s ||  1", TypeUInt(1)),
            // signed - signed
            ("1s *   1s", TypeNum(true)),
            ("1s /   1s", TypeNum(true)),
            ("1s %   1s", TypeNum(true)),
            ("1s +   1s", TypeNum(true)),
            ("1s -   1s", TypeNum(true)),
            ("1s <<  1s", TypeNum(true)),
            ("1s >>  1s", TypeNum(true)),
            ("1s >>> 1s", TypeNum(true)),
            ("1s <<< 1s", TypeNum(true)),
            ("1s >   1s", TypeUInt(1)),
            ("1s >=  1s", TypeUInt(1)),
            ("1s <   1s", TypeUInt(1)),
            ("1s <=  1s", TypeUInt(1)),
            ("1s ==  1s", TypeUInt(1)),
            ("1s !=  1s", TypeUInt(1)),
            ("1s &   1s", TypeNum(true)),
            ("1s ^   1s", TypeNum(true)),
            ("1s |   1s", TypeNum(true)),
            ("1s &&  1s", TypeUInt(1)),
            ("1s ||  1s", TypeUInt(1)),
            //
            // Mixed width operators
            //
            // unsigned - unsigned
            ("3'd1 <<  32'd1", TypeUInt(3)),
            ("3'd1 >>  32'd1", TypeUInt(3)),
            ("3'd1 >>> 32'd1", TypeUInt(3)),
            ("3'd1 <<< 32'd1", TypeUInt(3)),
            ("3'd1 &&  32'd1", TypeUInt(1)),
            ("3'd1 ||  32'd1", TypeUInt(1)),
            // unsigned - signed
            ("3'd1 <<  32'sd1", TypeUInt(3)),
            ("3'd1 >>  32'sd1", TypeUInt(3)),
            ("3'd1 >>> 32'sd1", TypeUInt(3)),
            ("3'd1 <<< 32'sd1", TypeUInt(3)),
            ("3'd1 &&  32'sd1", TypeUInt(1)),
            ("3'd1 ||  32'sd1", TypeUInt(1)),
            // igned - unsigned
            ("3'sd1 <<  32'd1", TypeSInt(3)),
            ("3'sd1 >>  32'd1", TypeSInt(3)),
            ("3'sd1 >>> 32'd1", TypeSInt(3)),
            ("3'sd1 <<< 32'd1", TypeSInt(3)),
            ("3'sd1 &&  32'd1", TypeUInt(1)),
            ("3'sd1 ||  32'd1", TypeUInt(1)),
            // signed - signed
            ("3'sd1 <<  32'sd1", TypeSInt(3)),
            ("3'sd1 >>  32'sd1", TypeSInt(3)),
            ("3'sd1 >>> 32'sd1", TypeSInt(3)),
            ("3'sd1 <<< 32'sd1", TypeSInt(3)),
            ("3'sd1 &&  32'sd1", TypeUInt(1)),
            ("3'sd1 ||  32'sd1", TypeUInt(1)),
            //
            // Binary '
            //
            // unsigned - unsigned
            ("10'd4 ' 3'd2", TypeUInt(4)),
            ("10'd3 ' 3'd2", TypeUInt(3)),
            // unsigned - signed
            ("10'd4 ' 3'sd2", TypeSInt(4)),
            ("10'd3 ' 3'sd2", TypeSInt(3)),
            // signed - unsigned
            ("10'sd4 ' 3'd2", TypeUInt(4)),
            ("10'sd3 ' 3'd2", TypeUInt(3)),
            // signed - signed
            ("10'sd4 ' 3'sd2", TypeSInt(4)),
            ("10'sd3 ' 3'sd2", TypeSInt(3))
          )
        } {
          src in {
            elaborate {
              s"""
                 |void f() {
                 |  $src;
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "ternary operator" - {
        for {
          (src, kind) <- List(
            // sized - sized
            ("1 ?  5'd2 :  5'd3", TypeUInt(5)),
            ("1 ?  5'd2 : 5'sd3", TypeUInt(5)),
            ("1 ? 5'sd2 :  5'd3", TypeUInt(5)),
            ("1 ? 5'sd2 : 5'sd3", TypeSInt(5)),
            // sized - unsized
            ("1 ?  5'd2 : 3u", TypeUInt(5)),
            ("1 ?  5'd2 : 3s", TypeUInt(5)),
            ("1 ? 5'sd2 : 3u", TypeUInt(5)),
            ("1 ? 5'sd2 : 3s", TypeSInt(5)),
            // unsized - sized
            ("1 ? 2u :  5'd3", TypeUInt(5)),
            ("1 ? 2u : 5'sd3", TypeUInt(5)),
            ("1 ? 2s :  5'd3", TypeUInt(5)),
            ("1 ? 2s : 5'sd3", TypeSInt(5)),
            // unsized - unsized
            ("1 ? 2u : 3u", TypeNum(false)),
            ("1 ? 2u : 3s", TypeNum(false)),
            ("1 ? 2s : 3u", TypeNum(false)),
            ("1 ? 2s : 3s", TypeNum(true))
          )
        } {
          src in {
            elaborate {
              s"""
                 |void f() {
                 |  $src;
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "cat" - {
        for {
          (src, kind) <- List(
            ("{  3'd0,  4'd0 }", TypeUInt(7)),
            ("{  3'd0, 4'sd0 }", TypeUInt(7)),
            ("{ 3'sd0,  4'd0 }", TypeUInt(7)),
            ("{ 3'sd0, 4'sd0 }", TypeUInt(7))
          )
        } {
          src in {
            elaborate {
              s"""
                 |void f() {
                 |  $src;
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "rep" - {
        for {
          (src, kind) <- List(
            ("{1{4'd0}}", TypeUInt(4)),
            ("{2{4'd0}}", TypeUInt(8)),
            ("{3{4'd0}}", TypeUInt(12)),
            ("{1{4'sd0}}", TypeUInt(4)),
            ("{2{4'sd0}}", TypeUInt(8)),
            ("{3{4'sd0}}", TypeUInt(12)),
            ("{4'd1{4'd0}}", TypeUInt(4)),
            ("{4'd2{4'd0}}", TypeUInt(8)),
            ("{4'd3{4'd0}}", TypeUInt(12)),
            ("{4'd1{4'sd0}}", TypeUInt(4)),
            ("{4'd2{4'sd0}}", TypeUInt(8)),
            ("{4'd3{4'sd0}}", TypeUInt(12))
          )
        } {
          src in {
            elaborate {
              s"""
                 |void f() {
                 |  $src;
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "index" - {
        for {
          (src, kind) <- List(
            ("a[0]", TypeUInt(1)),
            ("a[1]", TypeUInt(1)),
            ("b[0]", TypeSInt(7)),
            ("b[1]", TypeSInt(7)),
            ("b[0][0]", TypeUInt(1)),
            ("b[0][1]", TypeUInt(1)),
            ("c[0]", TypeVector(TypeSInt(7), 2)),
            ("c[1]", TypeVector(TypeSInt(7), 2)),
            ("c[0][0]", TypeSInt(7)),
            ("c[0][1]", TypeSInt(7)),
            ("c[0][0][0]", TypeUInt(1)),
            ("c[0][0][1]", TypeUInt(1)),
            ("d[0]", TypeSInt(7)),
            ("d[1]", TypeSInt(7)),
            ("d[0][0]", TypeUInt(1)),
            ("d[0][1]", TypeUInt(1)),
            ("e[0]", TypeSInt(7)),
            ("e[1]", TypeSInt(7)),
            ("e[0][0]", TypeUInt(1)),
            ("e[0][1]", TypeUInt(1)),
            ("f[0]", TypeVector(TypeVector(TypeSInt(7), 2), 4)),
            ("f[1]", TypeVector(TypeVector(TypeSInt(7), 2), 4)),
            ("f[0][0]", TypeVector(TypeSInt(7), 2)),
            ("f[0][1]", TypeVector(TypeSInt(7), 2)),
            ("f[0][0][0]", TypeSInt(7)),
            ("f[0][0][1]", TypeSInt(7)),
            ("f[0][0][0][0]", TypeUInt(1)),
            ("f[0][0][0][1]", TypeUInt(1)),
            ("h[0]", TypeUInt(1)),
            ("h[1]", TypeUInt(1)),
            ("g[0]", TypeUInt(1)),
            ("g[1]", TypeUInt(1)),
            ("1[0]", TypeUInt(1)),
            ("1[1]", TypeUInt(1))
          )
        } {
          src in {
            elaborate {
              s"""
                 |struct s {
                 |   bool f0;
                 |   bool f1;
                 |   bool f2;
                 |}
                 |
                 |fsm foo {
                 |  i7 a;
                 |  i7[2] b;
                 |  i7[4][2] c;
                 |  i7 d[2];
                 |  i7 e[2];
                 |  i7[4][2] f[3];
                 |  in i7 g;
                 |  in s h;
                 |
                 |  fence {
                 |    $src;
                 |  }
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "slice" - {
        for {
          (src, kind) <- List(
            ("a[8'd3 :8'd2]", TypeUInt(2)),
            ("a[8'd0 :8'd0]", TypeUInt(1)),
            ("a[8'd4+:8'd3]", TypeUInt(3)),
            ("a[8'd4-:8'd3]", TypeUInt(3)),
            ("1[8'd3 :8'd0]", TypeUInt(4)),
            ("1[8'd3+:8'd2]", TypeUInt(2)),
            ("1[8'd3-:8'd2]", TypeUInt(2)),
            ("a[5'd31:5'd0]", TypeUInt(32)),
            ("b[2'd1 :2'd1]", TypeVector(TypeUInt(32), 1)),
            ("b[2'd1 :2'd0]", TypeVector(TypeUInt(32), 2)),
            ("b[2'd3 :2'd1]", TypeVector(TypeUInt(32), 3)),
            ("b[2'd3 :2'd0]", TypeVector(TypeUInt(32), 4)),
            ("b[2'd0+:3'd1]", TypeVector(TypeUInt(32), 1)),
            ("b[2'd2+:3'd2]", TypeVector(TypeUInt(32), 2)),
            ("b[2'd1+:3'd3]", TypeVector(TypeUInt(32), 3)),
            ("b[2'd0+:3'd4]", TypeVector(TypeUInt(32), 4)),
            ("b[2'd1-:3'd1]", TypeVector(TypeUInt(32), 1)),
            ("b[2'd1-:3'd2]", TypeVector(TypeUInt(32), 2)),
            ("b[2'd3-:3'd3]", TypeVector(TypeUInt(32), 3)),
            ("b[2'd3-:3'd4]", TypeVector(TypeUInt(32), 4)),
            ("c[8'd3 :8'd2]", TypeUInt(2)),
            ("c[8'd0 :8'd0]", TypeUInt(1)),
            ("c[8'd4+:8'd3]", TypeUInt(3)),
            ("c[8'd4-:8'd3]", TypeUInt(3)),
            ("c[8'd23:8'd0]", TypeUInt(24))
          )
        } {
          src in {
            elaborate {
              s"""
                 |struct s {
                 |   u8 f0;
                 |   u8 f1;
                 |   u8 f2;
                 |}
                 |
                 |void function() {
                 |  u32 a;
                 |  u32[4] b;
                 |  s c;
                 |
                 |  $src;
                 |}""".stripMargin
            } getFirst {
              case e: ExprSlice => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "select" - {
        for {
          (src, kind) <- List[(String, PartialFunction[Any, Unit])](
            // format: off
            ("a.a", { case TypeSInt(w) if w == 6                                        => }),
            ("a.b", { case TypeRecord(Symbol("s"), List(Symbol("a"), Symbol("b"), Symbol("f"), Symbol("g")) ) => }),
            ("a.b.a", { case TypeUInt(w) if w == 1                                      => }),
            ("a.b.b", { case TypeUInt(w) if w == 8                                      => }),
            ("pi0.valid", { case TypeUInt(w) if w == 1                                  => }),
            ("pi0.read", { case TypeCombFunc(_, TypeSInt(w), Nil) if w == 8             => }),
            ("pi1.valid", { case TypeUInt(w) if w == 1                                  => }),
            ("pi1.read", { case TypeCombFunc(_, TypeVoid, Nil)                          => }),
            ("po0.valid", { case TypeUInt(w) if w == 1                                  => }),
            ("po0.write", { case TypeCombFunc(_, TypeVoid, List(TypeSInt(w))) if w == 8 => }),
            ("po0.full", { case TypeUInt(w) if w == 1                                   => }),
            ("po0.empty", { case TypeUInt(w) if w == 1                                  => }),
            ("po1.valid", { case TypeUInt(w) if w == 1                                  => }),
            ("po1.write", { case TypeCombFunc(_, TypeVoid, Nil)                         => }),
            ("po1.full", { case TypeUInt(w) if w == 1                                   => }),
            ("po1.empty", { case TypeUInt(w) if w == 1                                  => }),
            ("a.b.f", { case TypeStaticMethod(Symbol("f"), TypeVoid, Nil)               => }),
            ("a.b.g", { case TypeNormalMethod(Symbol("g"), TypeVoid, Nil)               => }),
            ("a.h", { case TypeStaticMethod(Symbol("h"), TypeVoid, Nil)                 => }),
            ("a.i", { case TypeNormalMethod(Symbol("i"), TypeVoid, Nil)                 => })
            // format: on
          )
        } {
          src in {
            elaborate {
              s"""
                 |struct s {
                 |  bool a;
                 |  u8   b;
                 |  static void f() {}
                 |  void g() {}
                 |}
                 |
                 |struct t {
                 |  i6  a;
                 |  s   b;
                 |  static void h() {}
                 |  void i() {}
                 |}
                 |
                 |fsm f {
                 |  in  sync ready i8   pi0;
                 |  in  sync ready void pi1;
                 |  out sync ready i8   po0;
                 |  out sync ready void po1;
                 |
                 |  t a;
                 |
                 |  void main() {
                 |    $src;
                 |  }
                 |}""".stripMargin
            } getFirst {
              case expr: ExprDot => expr
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ should matchPattern(kind)
            }
            cc.messages shouldBe empty
          }
        }
      }

      "select from type" - {
        for {
          (src, pattern) <- List[(String, PartialFunction[Any, Unit])](
            ("a.x", { case TypeNone(TypeSInt(w)) if w == 8 => }),
            ("b.y", { case TypeNone(TypeRecord(Symbol("a"), List(Symbol("x"), Symbol("f")))) => }),
            ("b.y.x", { case TypeNone(TypeSInt(w)) if w == 8 => }),
            ("c.d", { case TypeNone(TypeRecord(Symbol("d"), Nil)) => }),
            ("a.f", { case TypeStaticMethod(Symbol("f"), TypeVoid, Nil) => })
          )
        } {
          src in {
            elaborate {
              s"""
                 |struct a {
                 |  i8 x;
                 |  static void f() {}
                 |}
                 |
                 |struct b {
                 |  a y;
                 |}
                 |
                 |struct c {
                 |  struct d {}
                 |}
                 |
                 |fsm f {
                 |  fence {
                 |    $src;
                 |  }
                 |}""".stripMargin
            } getFirst {
              case e: ExprDot => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ should matchPattern(pattern)
            }
            cc.messages shouldBe empty
          }
        }
      }

      "sized integer literals" - {
        for {
          (src, kind) <- List(
            ("1'b0", TypeUInt(1)),
            ("2'd1", TypeUInt(2)),
            ("3'sd2", TypeSInt(3)),
            ("4'sd3", TypeSInt(4))
          )
        } {
          src in {
            TypeAssigner(src.asTree[Expr]).tpe shouldBe kind
            cc.messages shouldBe empty
          }
        }
      }

      "unsized integer literals" - {
        for {
          (src, kind) <- List(
            ("0", TypeNum(false)),
            ("1", TypeNum(false)),
            ("0s", TypeNum(true)),
            ("1s", TypeNum(true))
          )
        } {
          src in {
            TypeAssigner(src.asTree[Expr]).tpe shouldBe kind
            cc.messages shouldBe empty
          }
        }
      }

      "string literals" - {
        for {
          (src, kind) <- List(
            ("\"abc\"", TypeStr),
            ("\"\"", TypeStr)
          )
        } {
          src in {
            TypeAssigner(src.asTree[Expr]).tpe shouldBe kind
            cc.messages shouldBe empty
          }
        }
      }

      "call" - {
        for {
          (src, kind) <- List(
            ("pi0.read", TypeSInt(8)),
            ("pi1.read", TypeVoid),
            ("po0.write", TypeVoid),
            ("po1.write", TypeVoid)
          )
        } {
          src in {
            elaborate {
              s"""
                 |struct s {
                 |  bool a;
                 |  u8   b;
                 |}
                 |
                 |struct t {
                 |  i6  a;
                 |  s   b;
                 |}
                 |
                 |fsm f {
                 |  in  sync ready i8   pi0;
                 |  in  sync ready void pi1;
                 |  out sync ready i8   po0;
                 |  out sync ready void po1;
                 |
                 |  t a;
                 |
                 |  void main() {
                 |    $src();
                 |  }
                 |}""".stripMargin
            } getFirst {
              case expr: ExprCall => expr
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }

      "cast" - {
        for {
          (exprSrc, kindSrc, kind) <- List(
            // format: off
            ("32", "u8", TypeUInt(8)),
            ("32s", "i8", TypeSInt(8)),
            ("8'd1", "uint", TypeNum(false)),
            ("8'sd1", "int", TypeNum(true))
            // format: on
          )
        } {
          s"($kindSrc)($exprSrc)" in {
            val expr = exprSrc.asTree[Expr]
            val castKind = kindSrc.asTree[Expr] match {
              case ExprType(kind) => kind
              case _              => fail()
            }
            castKind shouldBe kind
            val cast = ExprCast(castKind, expr) withLoc Loc.synthetic
            assignChildren(cast)
            TypeAssigner(cast).kind shouldBe kind
            cc.messages shouldBe empty
          }
        }
      }

      "type expressions" - {
        for {
          (text, kind) <- List[(String, PartialFunction[Any, Unit])](
            ("bool[2]", { case TypeType(TypeVector(TypeUInt(w1), w2)) if w1 == 1 && w2 == 2 => }),
            (
              "bool[2][3]",
              {
                case TypeType(TypeVector(TypeVector(TypeUInt(w1), w2), w3))
                    if w1 == 1 && w2 == 3 && w3 == 2 =>
              }
            ),
            ("s.a", { case TypeNone(TypeUInt(w)) if w == 32 => }),
            ("s.t", { case TypeNone(TypeRecord(t, Nil)) if t.name == "t" => }),
            ("x.a", { case TypeType(TypeUInt(w)) if w == 32 => }),
            ("x.t", { case TypeType(TypeRecord(t, Nil)) if t.name == "t" => })
          )
        } {
          text in {
            elaborate {
              s"""
                 |struct s {
                 |  typedef u32 a;
                 |  struct t {}
                 |}
                 |
                 |fsm f {
                 |  s x;
                 |  fence { $text; }
                 |}""".stripMargin
            } getFirst {
              case StmtExpr(e) => e
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ should matchPattern(kind)
            }
            cc.messages shouldBe empty
          }
        }
      }
    }

    "statements" - {
      "unambiguous comb statements" - {
        for {
          (text, pattern) <- List[(String, PartialFunction[Any, Unit])](
            ("a = a + 1;", { case _: StmtAssign => }),
            ("a++;", { case _: StmtPost => }),
            ("a += 1;", { case _: StmtUpdate => }),
            ("bool c;", { case StmtSplice(_: Desc) => }),
            ("assert false;", { case StmtSplice(_: Assertion) => }),
            ("return;", { case _: StmtReturn => }),
            ("wait a;", { case _: StmtWait => }),
            ("wait;", { case _: StmtWait => })
          )
        } {
          text in {
            elaborate {
              s"""
                 |struct s {
                 |  void f() {
                 |    bool a;
                 |    $text
                 |  }
                 |}""".stripMargin
            } getFirst {
              case DescFunc(_, _, _, _, _, body) => body.last
            } tap {
              _ should matchPattern(pattern)
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe TypeCombStmt
            }
            cc.messages shouldBe empty
          }
        }
      }

      "unambiguous ctrl statements" - {
        for {
          (text, pattern) <- List[(String, PartialFunction[Any, Unit])](
            ("goto f();", { case _: StmtGoto => }),
            ("return;", { case _: StmtReturn => }),
            ("fence;", { case _: StmtFence => }),
            ("for(;;) {}", { case _: StmtFor => }),
            ("do {} while(1);", { case _: StmtDo => }),
            ("while (1) {}", { case _: StmtWhile => }),
            ("loop {}", { case _: StmtLoop => }),
            ("let (bool b = 1) for(;;) {}", { case StmtLet(_, List(_: StmtFor)) => }),
            ("let (bool b = 1) do {} while(1);", { case StmtLet(_, List(_: StmtDo)) => }),
            ("let (bool b = 1) while (1) {}", { case StmtLet(_, List(_: StmtWhile)) => }),
            ("let (bool b = 1) loop {}", { case StmtLet(_, List(_: StmtLoop)) => })
          )
        } {
          text in {
            elaborate {
              s"""
                 |fsm e {
                 |  void f() {
                 |    bool a;
                 |    $text
                 |  }
                 |}""".stripMargin
            } getFirst {
              case DescFunc(_, _, _, _, _, body) => body.last
            } tap {
              _ should matchPattern(pattern)
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe TypeCtrlStmt
            }
            cc.messages shouldBe empty
          }
        }
      }

      "unambiguous ctrl statements - loop break/continue" - {
        for {
          (text, pattern) <- List[(String, PartialFunction[Any, Unit])](
            ("break;", { case _: StmtBreak => }),
            ("continue;", { case _: StmtContinue => })
          )
        } {
          text in {
            elaborate {
              s"""
                 |fsm e {
                 |  void f() {
                 |    bool a;
                 |    for (;;) { $text }
                 |  }
                 |}""".stripMargin
            } getFirst {
              case StmtFor(_, _, _, body) => body.last
            } tap {
              _ should matchPattern(pattern)
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe TypeCtrlStmt
            }
            cc.messages shouldBe empty
          }
        }
      }

      "content dependent statements" - {
        for {
          (text, pattern, kind) <- List[(String, PartialFunction[Any, Unit], Type)](
            ("if(a) {}", { case StmtIf(_, Nil, Nil) => }, TypeCombStmt),
            ("if(a) {} else {}", { case StmtIf(_, Nil, StmtBlock(Nil) :: Nil) => }, TypeCombStmt),
            ("if(a) b.read();", { case StmtIf(_, _, Nil) => }, TypeCombStmt),
            ("if(a) b.read(); else c.write();", { case StmtIf(_, _, _ :: _) => }, TypeCombStmt),
            ("if(a) fence;", { case StmtIf(_, _, Nil) => }, TypeCtrlStmt),
            ("if(a) fence; else return;", { case StmtIf(_, _, _ :: _) => }, TypeCtrlStmt),
            ("case(a) {}", { case StmtCase(_, Nil) => }, TypeCombStmt),
            ("case(a) {a: b.read();}", { case _: StmtCase => }, TypeCombStmt),
            ("case(a) {default: b.read();}", { case _: StmtCase => }, TypeCombStmt),
            ("case(a) {a: fence;}", { case _: StmtCase => }, TypeCtrlStmt),
            ("case(a) {default: fence;}", { case _: StmtCase => }, TypeCtrlStmt),
            ("case(a) {default: {b.read(); fence;}}", { case _: StmtCase => }, TypeCtrlStmt),
            ("a;", { case StmtExpr(_: ExprSym) => }, TypeCombStmt),
            ("a + a;", { case StmtExpr(_: ExprBinary) => }, TypeCombStmt),
            ("b.read();", { case StmtExpr(_: ExprCall) => }, TypeCombStmt),
            ("main();", { case StmtExpr(_: ExprCall) => }, TypeCtrlStmt),
            ("xeno();", { case StmtExpr(_: ExprCall) => }, TypeCombStmt),
            ("s.f();", { case StmtExpr(_: ExprCall) => }, TypeCombStmt),
            ("i.g();", { case StmtExpr(_: ExprCall) => }, TypeCombStmt),
            ("{ }", { case _: StmtBlock => }, TypeCombStmt),
            ("{ a; fence; }", { case _: StmtBlock => }, TypeCtrlStmt),
            ("{ a; a; }", { case _: StmtBlock => }, TypeCombStmt)
          )
        } {
          text in {
            elaborate {
              s"""
                 |fsm a {
                 |  in sync bool a;
                 |  in sync void b;
                 |  out sync void c;
                 |  import bool xeno();
                 |
                 |  struct s {
                 |    static void f() {}
                 |    void g() {}
                 |  }
                 |
                 |  s i;
                 |
                 |  void main() {
                 |    a;
                 |    $text
                 |  }
                 |}""".stripMargin
            } getFirst {
              case DescFunc(Sym(Symbol("main")), _, _, _, _, body) => body.last
            } tap {
              _ should matchPattern(pattern)
            } tap {
              assignChildren
            } pipe {
              TypeAssigner(_).tpe
            } tap {
              _ shouldBe kind
            }
            cc.messages shouldBe empty
          }
        }
      }
    }

    "entity contents" - {
      for {
        (name, text) <- List(
          ("entity", "fsm x {}"),
          ("instance", "x = new f;"),
          ("connect", "b -> c;")
        )
      } {
        name in {
          elaborate {
            s"""
               |fsm f {}
               |
               |network a {
               |  in bool b;
               |  out bool c;
               |  $text
               |}""".stripMargin
          } getFirst {
            case DescEntity(_, _, EntityVariant.Net, body) => body.last
          } tap {
            assignChildren
          } pipe {
            TypeAssigner(_).tpe
          } tap {
            _ shouldBe TypeMisc
          }
          cc.messages shouldBe empty
        }
      }

      for {
        (name, text) <- List(
          ("decl", "bool x = true;"),
          ("function", "void x() {}")
        )
      } {
        name in {
          elaborate {
            s"""
               |fsm f  {
               |  $text
               |}""".stripMargin
          } getFirst {
            case DescEntity(_, _, EntityVariant.Fsm, body) => body.last
          } tap {
            assignChildren
          } pipe {
            TypeAssigner(_).tpe
          } tap {
            _ shouldBe TypeMisc
          }
          cc.messages shouldBe empty
        }
      }
    }
  }
}
