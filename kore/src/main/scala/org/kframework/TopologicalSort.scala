package org.kframework

import scala.annotation.tailrec
import scala.collection.MapView

/**
 * Created by dwightguth on 4/16/15.
 */
object TopologicalSort {
  @tailrec
  private def tsort[A](toPreds: Map[A, Set[A]], done: Iterable[A]): Iterable[A] = {
    val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
    if (noPreds.isEmpty) {
      if (hasPreds.isEmpty) done else sys.error(hasPreds.toString)
    } else {
      val found = noPreds.map { _._1 }
      this.tsort(hasPreds.view.mapValues { _ -- found } toMap, done ++ found)
    }
  }

  def tsort[A](edges: Iterable[(A, A)]): Iterable[A] = {
    val toPred = edges.foldLeft(Map[A, Set[A]]()) { (acc, e) =>
      acc + (e._1 -> acc.getOrElse(e._1, Set())) + (e._2 -> (acc.getOrElse(e._2, Set()) + e._1))
    }
    tsort(toPred, Seq())
  }
}
