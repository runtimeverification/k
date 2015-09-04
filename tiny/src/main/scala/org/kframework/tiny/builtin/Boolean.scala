package org.kframework.tiny.builtin

import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.tiny.{BinaryHookedFunctionLabel, NativeUnaryOpLabel, TypedKTok}

object Boolean {
  val True = TypedKTok(Sorts.Bool, true)
  val False = TypedKTok(Sorts.Bool, false)

  def And(labelString: String) = BinaryHookedFunctionLabel(labelString, Att(), {
    case (False, _) => False
    case (_, False) => False
    case (True, True) => True
  })

  def Or(labelString: String) = BinaryHookedFunctionLabel(labelString, Att(), {
    case (True, _) => True
    case (_, True) => True
    case (False, False) => True
  })

  def Not(labelString: String) = NativeUnaryOpLabel(labelString, Att(), (x: Boolean) => !x, Sorts.Bool)
}