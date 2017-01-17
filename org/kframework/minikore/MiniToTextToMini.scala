package org.kframework.minikore

import org.apache.commons.io.FileUtils

import org.kframework.minikore.MiniKore.Definition

// TODO(Daejun): drop this file

object MiniToTextToMini {
  def apply(d: Definition): Definition = {
    val text = MiniToText.apply(d)
    val file = new java.io.File("/tmp/x")
    FileUtils.writeStringToFile(file, text)
    val d2 = new TextToMini().parse(file)
    val text2 = MiniToText.apply(d2)
    assert(d == d2)
    d2
  }

  def assertequal(d1: Definition, d2: Definition): Unit = assert(d1 == d2)
}
