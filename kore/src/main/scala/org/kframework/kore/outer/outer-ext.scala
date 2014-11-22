// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.kframework.kore
import org.kframework.kore.Attributes

case class Configuration(
  body: kore.K,
  ensures: kore.K,
  att: Attributes = Attributes()) extends Sentence

case class Bubble(ty: String, contents: String, att: Attributes = Attributes()) extends Sentence
