// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.kore.{FoldK, KToken}

import scala.collection.Set

class ConfigVars(m: Module) {
  lazy val initRules: Set[Rule] = m.rules.collect({ case r if r.att.contains("initializer") => r })

  lazy val configVars: Set[KToken] = {
    val transformer = new FoldK[Set[KToken]] {
      override def apply(k: KToken): Set[KToken] = {
        if (k.sort.name == "KConfigVar") Set(k) else unit
      }
      def unit = Set()
      def merge(set1: Set[KToken], set2: Set[KToken]) = set1 | set2
    }
    initRules.map(r => transformer.apply(r.body))
      .fold(transformer.unit)(transformer.merge)
  }
}
