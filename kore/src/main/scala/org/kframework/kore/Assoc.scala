package org.kframework.kore

import org.kframework.definition.Module

import scala.collection.JavaConverters._

/**
 * Created by dwightguth on 3/27/15.
 */
object Assoc extends {

  def flatten(label: KLabel, list: java.util.List[K], m: Module): java.util.List[K] = {
    flatten(label, list.asScala, ADT.KLabel(m.attributesFor(label).get("unit"))).asJava
  }

  def flatten(label: KLabel, list: java.util.List[K], unit: KToken) : java.util.List[K] = {
    list.asScala flatMap {
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
    } asJava
  }


  def flatten(label: KLabel, list: java.util.List[K], unit: KLabel): java.util.List[K] = {
    flatten(label, list.asScala, unit).asJava
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
