// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.builtin

import org.kframework.kore.{Constructors, K}

class Labels[KK <: K](cons: Constructors[KK]) {
  import cons._

  lazy val Hole = KLabel(KLabels.HOLE)
  lazy val KBag = KLabel(KLabels.KBAG)
  lazy val And = KLabel(KLabels.AND)
  lazy val Or = KLabel(KLabels.OR)
}
