package org.kframework.kore.parser

import org.apache.commons.io.FileUtils
import org.kframework.kore._
import org.kframework.kore.implementation.DefaultBuilders


// TODO(Daejun): drop this file

// object MiniToTextToMini {
//
//   def defaultImplemntation: Builders = DefaultBuilders
//
//   def apply(d: Definition): Definition = {
//     val text = KoreToText.apply(d)
//     val file = new java.io.File("/tmp/x")
//     FileUtils.writeStringToFile(file, text)
//     val d2 = new TextToKore(defaultImplemntation).parse(file)
//     val text2 = KoreToText.apply(d2)
//     assert(d == d2)
//     d2
//   }

//   def assertequal(d1: Definition, d2: Definition): Unit = assert(d1 == d2)
// }
