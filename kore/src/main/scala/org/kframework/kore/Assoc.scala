// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.definition.Module
import scala.collection.immutable
import scala.collection.JavaConverters._

/**
 * Created by dwightguth on 3/27/15.
 */
object Assoc extends {

  def flatten(label: KLabel, list: java.util.List[K], m: Module): java.util.List[K] =
    flatten(
      label,
      list.asScala.to[immutable.Seq],
      ADT.KLabel(m.attributesFor(label).get(Att.UNIT))
    ).asJava

  def flatten(label: KLabel, list: java.util.List[K], unit: KToken): java.util.List[K] =
    list.asScala.flatMap {
      case k: KApply =>
        if (k.klabel == label)
          flatten(label, k.klist.items, unit).asScala
        else
          List(k)
      case k: KToken =>
        if (k == unit)
          List()
        else
          List(k)
      case other => List(other)
    }.asJava

  def flatten(label: KLabel, list: java.util.List[K], unit: KLabel): java.util.List[K] =
    flatten(label, list.asScala.to[immutable.Seq], unit).asJava

  def flatten(label: KLabel, list: immutable.Seq[K], unit: KLabel): immutable.Seq[K] =
    list.flatMap {
      case k: KApply =>
        if (k.klabel == label)
          flatten(label, k.klist.items.asScala.to[immutable.Seq], unit)
        else if (k.klabel == unit)
          List()
        else
          List(k)
      case other => List(other)
    }
}
