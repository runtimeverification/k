package org.kframework.kore

import org.kframework.kore.ADT.KLabel

import scala.collection.JavaConverters._

import org.kframework.definition.Module

/**
 * Created by dwightguth on 3/27/15.
 */
object Assoc extends {

  def flatten(label: KLabel, list: java.util.List[K], m: Module): java.util.List[K] = {
    flatten(label, list.asScala, KLabel(m.attributesFor(label).get[String]("unit").get)).asJava
  }

  def flatten(label:KLabel, list:Seq[K], unit: KLabel): Seq[K] = {
    list flatMap { case k: KApply =>
        if (k.klabel == label)
          flatten(label, k.klist.items.asScala, unit)
        else if (k.klabel == unit)
          List()
        else
          List(k)
      case other => List(other)
    }
  }
}
