////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 2017 Argon Design Ltd.
// All rights reserved.
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
////////////////////////////////////////////////////////////////////////////////

package alogic.ast

import alogic.Message

// Signals have a name, a width and a signedness
case class Signal(name: String, signed: Boolean, width: Expr) {
  def declString = {
    val signedStr = if (signed) "signed " else ""
    if (width.isConst) {
      val w = width.eval
      if (w < 1) {
        Message.fatal(s"Cannot declare signal with width ${w}")
      } else if (w == 1) {
        s"${signedStr}${name};"
      } else {
        s"${signedStr}[${w - 1}:0] ${name};"
      }
    } else {
      s"${signedStr}[(${width.simplify.toVerilog})-1:0] ${name};"
    }
  }
}
