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
// Extremely basic and fairly inefficient immutable matrix implementation, used
// to avoid external dependencies on large linear algebra libraries
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.lib

import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

// elements: List of rows which are themselves lists
case class Matrix[T: Numeric](elements: List[List[T]]) {
  require(elements.nonEmpty)
  require(elements.head.nonEmpty)

  private[this] val numeric = implicitly[Numeric[T]]
  import numeric._

  val size = (elements.length, elements.head.length) // (row count, column count)

  def rowCount: Int = size._1
  def colCount: Int = size._2

  def isSquare: Boolean = rowCount == colCount

  require(elements forall { _.length == colCount })

  val rows = elements

  lazy val cols = transpose.rows

  lazy val transpose: Matrix[T] = Matrix(elements.transpose)

  def +(other: Matrix[T]): Matrix[T] = {
    require(size == other.size, s"Incompatible matrix sizes $size + ${other.size}")
    val elements = (rows lazyZip other.rows) map { case (a, b) => (a lazyZip b) map { _ + _ } }
    Matrix(elements)
  }

  def *(other: Matrix[T]): Matrix[T] = {
    require(colCount == other.rowCount, s"Incompatible matrix sizes $size * ${other.size}")
    val elements = for (row <- rows) yield {
      for (col <- other.cols) yield {
        @tailrec
        def loop(row: List[T], col: List[T], acc: T = zero): T = (row, col) match {
          case (Nil, Nil)         => acc
          case (r :: rs, c :: cs) => loop(rs, cs, acc + r * c)
          case _                  => unreachable
        }
        loop(row, col)
      }
    }
    Matrix(elements)
  }

  def pow(exp: Int): Matrix[T] = {
    require(isSquare)
    exp match {
      case v if v < 0 => unreachable
      case 0          => unreachable
      case 1          => this
      case 2          => this * this
      case _ => {
        val half = pow(exp / 2)
        val part = half * half
        if (exp % 2 == 0) part else part * this
      }
    }
  }

  lazy val diagonal: List[T] = {
    require(isSquare)

    val buf = ListBuffer[T]()

    @tailrec
    def loop(rows: List[List[T]]): List[T] = {
      buf append rows.head.head
      if (rows.lengthCompare(1) == 0) {
        buf.toList
      } else {
        loop(rows.tail map { _.tail })
      }
    }

    loop(rows)
  }

  // $COVERAGE-OFF$ Debug code
  override def toString: String = {
    val lines = for (row <- rows) yield {
      row mkString ("[", " ", "]")
    }
    lines mkString "\n"
  }

  def printWithHeaders(rowHeaders: List[String], colHeaders: List[String]): Unit = {
    require(rowHeaders.length == rowCount)
    require(colHeaders.length == colCount)
    for ((txt, idx) <- colHeaders.zipWithIndex) {
      println(" " + "| " * idx + txt)
    }
    for ((txt, line) <- rowHeaders zip toString.split("\n")) {
      println(line + " " + txt)
    }
  }

  def printWithHeaders(headers: List[String]): Unit = {
    require(headers.length == rowCount)
    require(this.isSquare)
    printWithHeaders(headers, headers)
  }

  // $COVERAGE-ON$

}

object Matrix {

  def zeros[T: Numeric](size: Int): Matrix[T] = {
    val row = List.fill(size)(implicitly[Numeric[T]].zero)
    val ele = List.fill(size)(row)
    Matrix(ele)
  }

}
